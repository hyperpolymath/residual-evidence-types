#!/usr/bin/env python3
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
"""Compare evaluated proof metadata with a bounded set of repository files.

This uses the Python standard library only. It reads configuration as data;
it never evaluates shell, Just or JavaScript and never executes configured
paths. Source-shape checks establish consistency, not proof correctness.
"""

import argparse
import json
import pathlib
import re
import shlex
import shutil
import sys
import tempfile


class ContractError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise ContractError(message)


class Checkout:
    def __init__(self, root):
        self.root = pathlib.Path(root).resolve()
        self.files = set()

    def path(self, relative):
        require(isinstance(relative, str), "configured path must be a string")
        path = pathlib.PurePosixPath(relative)
        require(relative and not path.is_absolute() and ".." not in path.parts
                and re.fullmatch(r"[A-Za-z0-9_./-]+", relative),
                f"unsafe configured path: {relative!r}")
        result = (self.root / path).resolve()
        require(result.is_relative_to(self.root), f"path escapes checkout: {relative}")
        return result

    def read(self, relative):
        path = self.path(relative)
        require(path.is_file(), f"required file is missing: {relative}")
        self.files.add(relative)
        return path.read_text(encoding="utf-8")

    def inventory(self, relative):
        directory = self.path(relative)
        require(directory.is_dir(), f"rejection directory is missing: {relative}")
        files = sorted(directory.glob("*.agda"))
        for path in files:
            self.read(f"{relative}/{path.name}")
        return [path.stem for path in files]


def single(pattern, source, label):
    matches = re.findall(pattern, source, re.MULTILINE)
    require(len(matches) == 1, f"expected exactly one {label}, found {len(matches)}")
    return matches[0]


def script_flags(source, label):
    flags = single(r"^flags=\(([^\n]*)\)$", source, f"{label} flags assignment")
    return shlex.split(flags)


def check_recipe(justfile, target, script):
    require(re.fullmatch(r"[a-z][a-z0-9-]*", target), f"invalid Just target: {target!r}")
    body = single(rf"^{re.escape(target)}:[^\n]*\n((?:[ \t]+[^\n]*\n|\n)*)",
                  justfile + "\n", f"Just target {target}")
    commands = [line.strip() for line in body.splitlines()
                if line.strip() and not line.lstrip().startswith("#")]
    require(commands == [f"bash {script}"], f"Just target {target} differs from its declared script")


def check_document(document, root, standards_revision, nickel_version, nickel_sha256):
    checkout = Checkout(root)
    pedigree = document["pedigree"]
    security = pedigree["security"]
    require(security["leash"] == "Yard", "proof configuration must use the Yard leash")
    require(security["capabilities"] == [], "proof configuration must grant no capabilities")
    for field in ("allow_network", "allow_filesystem_write", "allow_subprocess", "signature_required"):
        require(security[field] is False, f"proof configuration must keep {field} false")
    require("recipes" not in document, "proof configuration must not declare recipes")
    config = document["config"]
    require(config["repository"] == "hyperpolymath/residual-evidence-types", "wrong repository identity")
    specification = config["specification"]
    require(specification["repository"] == "metadatastician/standards"
            and specification["revision"] == standards_revision
            and specification["contract_version"] == "1.0.0"
            and specification["contract_path"] == "1-formats/k9/spec/contract/k9_contract.ncl"
            and specification["validator_path"] == "1-formats/k9/tools/k9-validate.sh"
            and specification["nickel_version"] == nickel_version
            and specification["nickel_sha256"] == nickel_sha256,
            "configured standards or Nickel pins differ from the verified tools")

    agda = config["agda"]
    required_flags = ["--safe", "--without-K", "--no-libraries", "--ignore-interfaces", "--double-check"]
    require(agda["flags"] == required_flags, "configured Agda flags omit or alter a required check")
    core, siblings, correspondence = (config[name] for name in ("core", "siblings", "correspondence"))
    evidence = config["evidence"]
    require(evidence["hosted_run_and_commit_required"] is True,
            "hosted run and checked commit must remain required")
    require(evidence["configuration_validation_is_proof_verification"] is False,
            "configuration validation must not claim proof verification")
    checkout.read(evidence["record"])
    justfile = checkout.read("Justfile")
    workflow = checkout.read(evidence["workflow"])

    sources = {}
    for label, target in (("core", core), ("siblings", siblings), ("correspondence", correspondence)):
        sources[label] = checkout.read(target["script"])
        check_recipe(justfile, target["just_target"], target["script"])
        require(re.search(rf"^\s*run:\s*bash\s+{re.escape(target['script'])}\s*$", workflow, re.MULTILINE),
                f"proof workflow does not directly run the declared {label} script")

    require(script_flags(sources["core"], "core") == required_flags + ["-i", "src"],
            "core Agda flags differ from declared contract")
    require(script_flags(sources["siblings"], "siblings") == required_flags + ["-i", "src", "-i", "tests/integration"],
            "sibling Agda flags differ from declared contract")
    checkout.read(core["entrypoint"])
    require(re.search(r'^"\$prover" "\$\{flags\[@\]\}" ' + re.escape(core["entrypoint"]) + r"$",
                      sources["core"], re.MULTILINE), "core runner does not invoke its declared entrypoint")
    require(len(siblings["entrypoints"]) == 2, "expected both sibling entrypoints")
    for entrypoint, flag in zip(siblings["entrypoints"], ("echo_flags", "epi_flags")):
        checkout.read(entrypoint)
        expected = f'"$prover" "${{flags[@]}}" "${{{flag}[@]}}" {entrypoint}'
        require(expected in sources["siblings"].splitlines(), f"sibling runner does not invoke {entrypoint}")

    for label, target in (("core", core), ("siblings", siblings)):
        expected = target["expected_rejections"]
        require(isinstance(expected, list) and expected
                and all(isinstance(name, str) and re.fullmatch(r"[A-Z][A-Za-z0-9]*", name) for name in expected)
                and len(set(expected)) == len(expected), f"invalid {label} rejection inventory")
        actual = checkout.inventory(target["rejection_directory"])
        require(actual == sorted(expected),
                f"{label} rejection inventory mismatch: expected {sorted(expected)}, found {actual}")
        require(target["expected_rejection_count"] == len(actual), f"{label} rejection count mismatch")
    require(f'rejects=({core["rejection_directory"]}/*.agda)' in sources["core"].splitlines(),
            "core runner does not enumerate its declared rejection directory")
    for name, prefix in (("echo_rejects", "FalseEcho"), ("epi_rejects", "FalseEpistemic")):
        require(f'{name}=({siblings["rejection_directory"]}/{prefix}*.agda)' in sources["siblings"].splitlines(),
                "sibling runner does not enumerate its declared rejection directory")

    fetch_source = checkout.read(siblings["fetch_script"])
    require(f'bash {siblings["fetch_script"]}' in sources["siblings"].splitlines(),
            "sibling runner does not call its pinned dependency fetcher")
    pins = re.findall(r"^fetch\s+(\S+)\s+(\S+)\s+([0-9a-f]{40})\s*$", fetch_source, re.MULTILINE)
    expected_pins = [("echo-types", "hyperpolymath/echo-types", siblings["pins"]["echo_types"]),
                     ("epistemic-types", "hyperpolymath/epistemic-types", siblings["pins"]["epistemic_types"]),
                     ("standard-library", "agda/agda-stdlib", siblings["pins"]["standard_library"])]
    require(pins == expected_pins, "sibling fetcher pins differ from the declared contract")

    package = single(r"\bagda-bin=([^\s\\]+)", workflow, "pinned Agda package")
    require(package == agda["debian_package_version"], "workflow Agda package differs from contract")
    version = single(r"test \"\$\(agda --version\)\" = 'Agda version ([^']+)'", workflow, "Agda version assertion")
    require(version == agda["version"], "workflow Agda version assertion differs from contract")
    bun_version = single(r"^\s*BUN_VERSION:\s*([0-9.]+)\s*$", workflow, "Bun pin")
    require(bun_version == correspondence["bun_version"], "workflow Bun pin differs from contract")

    correspondence_source = sources["correspondence"]
    harness_tests = int(single(r"^expected_tests=([0-9]+)$", correspondence_source, "harness test-count assertion"))
    require(harness_tests == correspondence["harness_tests"], "correspondence test count differs from contract")
    require(correspondence["required_stages"] == ["harness", "table-byte-equality", "agda-refl-proof"],
            "correspondence stages differ from the required verification chain")
    require('"$bun" test tests/correspondence' in correspondence_source,
            "correspondence harness invocation is missing")
    require('"$bun" tests/correspondence/generate-table.js --out "$fresh"' in correspondence_source,
            "correspondence table regeneration is missing")
    require('diff -u tests/correspondence/ExplorerTable.agda "$fresh"' in correspondence_source,
            "correspondence table byte-comparison is missing")
    flattened = correspondence_source.replace("\\\n", " ")
    invocation = single(r'^"\$prover" ([^\n]*Correspondence\.agda)\s*$', flattened, "correspondence proof invocation")
    require(shlex.split(invocation) == required_flags + ["-i", "src", "-i", "tests/correspondence", correspondence["entrypoint"]],
            "correspondence Agda flags or entrypoint differ from contract")
    correspondence_module = checkout.read(correspondence["entrypoint"])
    require(re.search(r"^checker-matches-explorer : table ≡ expected\nchecker-matches-explorer = refl$",
                      correspondence_module, re.MULTILINE), "declared correspondence refl proof is missing")
    table = checkout.read("tests/correspondence/ExplorerTable.agda")
    rows = len(re.findall(r"^\s*(?:∷\s*)?row\b", table, re.MULTILINE))
    require(rows == correspondence["configurations"], "committed correspondence row count differs from contract")
    return checkout


def regression(document, baseline, arguments):
    """Mutate only isolated copies; require the intended diagnostic each time."""
    with tempfile.TemporaryDirectory(prefix="proof-contract-") as directory:
        fixture = pathlib.Path(directory)
        for relative in baseline.files:
            destination = fixture / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(baseline.root / relative, destination)
        check_document(document, fixture, *arguments)

        script = fixture / document["config"]["core"]["script"]
        original = script.read_text(encoding="utf-8")
        require(original.count("flags=(--safe ") == 1, "cannot construct safety-flag regression fixture")
        script.write_text(original.replace("flags=(--safe ", "flags=(", 1), encoding="utf-8")
        expect_failure(document, fixture, arguments, "core Agda flags differ from declared contract")
        script.write_text(original, encoding="utf-8")
        print("PASS: checkout consistency rejects a removed core safety flag")

        core = document["config"]["core"]
        missing = fixture / core["rejection_directory"] / f'{core["expected_rejections"][0]}.agda'
        missing.unlink()
        expect_failure(document, fixture, arguments, "core rejection inventory mismatch")
        print("PASS: checkout consistency rejects a missing rejection control")


def expect_failure(document, root, arguments, expected):
    try:
        check_document(document, root, *arguments)
    except ContractError as error:
        require(expected in str(error), f"regression failed for the wrong reason: {error}")
    else:
        raise ContractError(f"invalid fixture unexpectedly passed: {expected}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", required=True)
    parser.add_argument("--document", required=True)
    parser.add_argument("--verdict", required=True)
    parser.add_argument("--standards-revision", required=True)
    parser.add_argument("--nickel-version", required=True)
    parser.add_argument("--nickel-sha256", required=True)
    parser.add_argument("--regression", action="store_true")
    options = parser.parse_args()
    verdict = json.loads(pathlib.Path(options.verdict).read_text(encoding="utf-8"))
    require(verdict["dialect"] == "component" and verdict["contract_version"] == "1.0.0"
            and verdict["verdict"] == "pass" and verdict["errors"] == 0 and verdict["skipped"] == 0,
            "canonical validator did not report a complete successful component check")
    document = json.loads(pathlib.Path(options.document).read_text(encoding="utf-8"))
    arguments = (options.standards_revision, options.nickel_version, options.nickel_sha256)
    baseline = check_document(document, options.root, *arguments)
    print("PASS: canonical K9 L2 validation and proof metadata agree with the checkout")
    if options.regression:
        regression(document, baseline, arguments)


if __name__ == "__main__":
    try:
        main()
    except (ContractError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"ERROR: proof contract: {error}", file=sys.stderr)
        sys.exit(1)
