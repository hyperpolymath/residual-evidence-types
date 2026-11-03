K9!
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
# Pure proof-check configuration. Evaluation checks this data, not the proofs.

# Predicates are enforced during evaluation/export, not merely typechecking.
let exactly = fun expected =>
  std.contract.from_predicate (fun actual => actual == expected) in

{
  pedigree = {
    schema_version = "1.0.0",
    component_type = "proof-validation-config",
    security = {
      leash = 'Yard,
      trust_level = "validated-configuration",
      allow_network = false,
      allow_filesystem_write = false,
      allow_subprocess = false,
      signature_required = false,
      capabilities = [],
    },
    metadata = {
      name = "residual-evidence-proof-validation",
      version = "1.0.0",
      description = "Required toolchain, proof targets, dependency pins and rejection controls for residual-evidence-types.",
      author = "Jonathan D.A. Jewell",
    },
  },

  # A host may compare this evaluated data with the checkout and its workflow.
  # No field is a recipe or an authorisation to execute its string contents.
  config = {
    repository | String | (exactly "hyperpolymath/residual-evidence-types")
      = "hyperpolymath/residual-evidence-types",

    specification = {
      repository | String | (exactly "metadatastician/standards")
        = "metadatastician/standards",
      revision | String | (exactly "d3e4b485a2af90c92a8e18af0888cd19cb132cd9")
        = "d3e4b485a2af90c92a8e18af0888cd19cb132cd9",
      contract_version | String | (exactly "1.0.0") = "1.0.0",
      contract_path | String
        | (exactly "1-formats/k9/spec/contract/k9_contract.ncl")
        = "1-formats/k9/spec/contract/k9_contract.ncl",
      validator_path | String | (exactly "1-formats/k9/tools/k9-validate.sh")
        = "1-formats/k9/tools/k9-validate.sh",
      nickel_version | String | (exactly "1.18.0") = "1.18.0",
      nickel_sha256 | String
        | (exactly "9cba4dd65ae9915ec61f73033aafcff307a377665a83fd8f530df086763318cb")
        = "9cba4dd65ae9915ec61f73033aafcff307a377665a83fd8f530df086763318cb",
    },

    agda = {
      version | String | (exactly "2.6.4.3") = "2.6.4.3",
      debian_package_version | String | (exactly "2.6.4.3-1+b2")
        = "2.6.4.3-1+b2",
      flags | Array String
        | (exactly ["--safe", "--without-K", "--no-libraries", "--ignore-interfaces", "--double-check"])
        = ["--safe", "--without-K", "--no-libraries", "--ignore-interfaces", "--double-check"],
    },

    core = {
      just_target | String | (exactly "check") = "check",
      script | String | (exactly "scripts/check.sh") = "scripts/check.sh",
      entrypoint | String | (exactly "src/ResidualEvidence/All.agda")
        = "src/ResidualEvidence/All.agda",
      rejection_directory | String | (exactly "tests/reject") = "tests/reject",
      expected_rejections | Array String
        | (exactly ["FalseCoarsening", "FalseFiniteEntailment", "FalseFiniteSoundness", "FalseIdentification", "FalseIntEquality", "FalsePresence", "FalseRetraction", "FalseWeakening", "InconsistentCase"])
        = ["FalseCoarsening", "FalseFiniteEntailment", "FalseFiniteSoundness", "FalseIdentification", "FalseIntEquality", "FalsePresence", "FalseRetraction", "FalseWeakening", "InconsistentCase"],
      expected_rejection_count | Number | (exactly 9)
        = std.array.length expected_rejections,
    },

    siblings = {
      just_target | String | (exactly "check-siblings") = "check-siblings",
      script | String | (exactly "scripts/check-siblings.sh")
        = "scripts/check-siblings.sh",
      fetch_script | String | (exactly "scripts/fetch-siblings.sh")
        = "scripts/fetch-siblings.sh",
      entrypoints | Array String
        | (exactly ["tests/integration/EchoComparison.agda", "tests/integration/EpistemicComparison.agda"])
        = ["tests/integration/EchoComparison.agda", "tests/integration/EpistemicComparison.agda"],
      rejection_directory | String | (exactly "tests/integration/reject")
        = "tests/integration/reject",
      expected_rejections | Array String
        | (exactly ["FalseEchoCoarsening", "FalseEchoComposition", "FalseEpistemicActualWorld", "FalseEpistemicNonVacuity", "FalseEpistemicRetraction", "FalseEpistemicRevision"])
        = ["FalseEchoCoarsening", "FalseEchoComposition", "FalseEpistemicActualWorld", "FalseEpistemicNonVacuity", "FalseEpistemicRetraction", "FalseEpistemicRevision"],
      expected_rejection_count | Number | (exactly 6)
        = std.array.length expected_rejections,
      pins = {
        echo_types | String | (exactly "9c4b72b52972c7e084c8f569635eb01caef64e7a")
          = "9c4b72b52972c7e084c8f569635eb01caef64e7a",
        epistemic_types | String | (exactly "dd948fbdddbdd06282cda8425e3e644e013c11ff")
          = "dd948fbdddbdd06282cda8425e3e644e013c11ff",
        standard_library | String | (exactly "97bc55e47367c562b3032bf104f2a00b19716f88")
          = "97bc55e47367c562b3032bf104f2a00b19716f88",
      },
    },

    correspondence = {
      just_target | String | (exactly "correspondence") = "correspondence",
      script | String | (exactly "scripts/correspondence.sh")
        = "scripts/correspondence.sh",
      entrypoint | String | (exactly "tests/correspondence/Correspondence.agda")
        = "tests/correspondence/Correspondence.agda",
      bun_version | String | (exactly "1.3.14") = "1.3.14",
      harness_tests | Number | (exactly 11) = 11,
      configurations | Number | (exactly 546) = 546,
      required_stages | Array String
        | (exactly ["harness", "table-byte-equality", "agda-refl-proof"])
        = ["harness", "table-byte-equality", "agda-refl-proof"],
    },

    evidence = {
      workflow | String | (exactly ".github/workflows/proofs.yml")
        = ".github/workflows/proofs.yml",
      record | String | (exactly "PROOF-STATUS.adoc") = "PROOF-STATUS.adoc",
      hosted_run_and_commit_required | Bool | (exactly true) = true,
      configuration_validation_is_proof_verification | Bool | (exactly false)
        = false,
    },
  },
}
