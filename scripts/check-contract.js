#!/usr/bin/env bun
// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
// Compare evaluated proof metadata with a bounded set of repository files.
// Configured paths and strings are data; no configured commands are executed.
// Source-shape checks establish consistency, not proof correctness.

import {
  copyFileSync, existsSync, mkdirSync, mkdtempSync, readFileSync,
  readdirSync, realpathSync, rmSync, statSync, unlinkSync, writeFileSync,
} from 'node:fs';
import { dirname, isAbsolute, join, relative, resolve, sep } from 'node:path';
import { tmpdir } from 'node:os';
import { parseArgs } from 'node:util';

class ContractError extends Error {}

function requireThat(condition, message) {
  if (!condition) throw new ContractError(message);
}

const equal = (left, right) => JSON.stringify(left) === JSON.stringify(right);
const escapeRegex = (text) => text.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
const readText = (path) => readFileSync(path, 'utf8');
const readJson = (path) => JSON.parse(readText(path));

class Checkout {
  constructor(root) {
    this.root = realpathSync(root);
    this.files = new Set();
  }

  path(name) {
    requireThat(typeof name === 'string' && name.length > 0
      && !isAbsolute(name) && !name.split('/').includes('..')
      && /^[A-Za-z0-9_./-]+$/.test(name), `unsafe configured path: ${JSON.stringify(name)}`);
    const lexical = resolve(this.root, name);
    const result = existsSync(lexical) ? realpathSync(lexical) : lexical;
    const inside = relative(this.root, result);
    requireThat(inside !== '..' && !inside.startsWith(`..${sep}`) && !isAbsolute(inside),
      `path escapes checkout: ${name}`);
    return result;
  }

  read(name) {
    const path = this.path(name);
    requireThat(existsSync(path) && statSync(path).isFile(), `required file is missing: ${name}`);
    this.files.add(name);
    return readText(path);
  }

  inventory(name) {
    const directory = this.path(name);
    requireThat(existsSync(directory) && statSync(directory).isDirectory(),
      `rejection directory is missing: ${name}`);
    const files = readdirSync(directory).filter((file) => file.endsWith('.agda')).sort();
    for (const file of files) this.read(`${name}/${file}`);
    return files.map((file) => file.slice(0, -5));
  }
}

function single(pattern, source, label) {
  const matches = [...source.matchAll(new RegExp(pattern, 'gm'))];
  requireThat(matches.length === 1, `expected exactly one ${label}, found ${matches.length}`);
  return matches[0][1];
}

// The checked option arrays contain literal flags and source paths only.
// Reject unsupported shell syntax rather than attempting to evaluate it.
function literalWords(source) {
  requireThat(/^[A-Za-z0-9_./\s-]*$/.test(source), 'proof arguments must remain literal words');
  return source.trim().split(/\s+/).filter(Boolean);
}

function scriptFlags(source, label) {
  return literalWords(single('^flags=\\(([^\\n]*)\\)$', source, `${label} flags assignment`));
}

function checkRecipe(justfile, target, script) {
  requireThat(typeof target === 'string' && /^[a-z][a-z0-9-]*$/.test(target),
    `invalid Just target: ${JSON.stringify(target)}`);
  const body = single(`^${escapeRegex(target)}:[^\\n]*\\n((?:[ \\t]+[^\\n]*\\n|\\n)*)`,
    `${justfile}\n`, `Just target ${target}`);
  const commands = body.split('\n').map((line) => line.trim())
    .filter((line) => line && !line.startsWith('#'));
  requireThat(equal(commands, [`bash ${script}`]), `Just target ${target} differs from its declared script`);
}

function checkDocument(document, root, standardsRevision, nickelVersion, nickelSha256) {
  const checkout = new Checkout(root);
  const security = document.pedigree.security;
  requireThat(security.leash === 'Yard', 'proof configuration must use the Yard leash');
  requireThat(equal(security.capabilities, []), 'proof configuration must grant no capabilities');
  for (const field of ['allow_network', 'allow_filesystem_write', 'allow_subprocess', 'signature_required']) {
    requireThat(security[field] === false, `proof configuration must keep ${field} false`);
  }
  requireThat(!Object.hasOwn(document, 'recipes'), 'proof configuration must not declare recipes');
  const config = document.config;
  requireThat(config.repository === 'hyperpolymath/residual-evidence-types', 'wrong repository identity');
  const specification = config.specification;
  requireThat(specification.repository === 'metadatastician/standards'
    && specification.revision === standardsRevision && specification.contract_version === '1.0.0'
    && specification.contract_path === '1-formats/k9/spec/contract/k9_contract.ncl'
    && specification.validator_path === '1-formats/k9/tools/k9-validate.sh'
    && specification.nickel_version === nickelVersion && specification.nickel_sha256 === nickelSha256,
  'configured standards or Nickel pins differ from the verified tools');

  const requiredFlags = ['--safe', '--without-K', '--no-libraries', '--ignore-interfaces', '--double-check'];
  const { agda, core, siblings, correspondence, evidence } = config;
  requireThat(equal(agda.flags, requiredFlags), 'configured Agda flags omit or alter a required check');
  requireThat(evidence.hosted_run_and_commit_required === true, 'hosted run and checked commit must remain required');
  requireThat(evidence.configuration_validation_is_proof_verification === false,
    'configuration validation must not claim proof verification');
  checkout.read(evidence.record);
  const justfile = checkout.read('Justfile');
  const workflow = checkout.read(evidence.workflow);
  const sources = {};
  for (const [label, target] of [['core', core], ['siblings', siblings], ['correspondence', correspondence]]) {
    sources[label] = checkout.read(target.script);
    checkRecipe(justfile, target.just_target, target.script);
    requireThat(new RegExp(`^\\s*run:\\s*bash\\s+${escapeRegex(target.script)}\\s*$`, 'm').test(workflow),
      `proof workflow does not directly run the declared ${label} script`);
  }
  requireThat(equal(scriptFlags(sources.core, 'core'), [...requiredFlags, '-i', 'src']),
    'core Agda flags differ from declared contract');
  requireThat(equal(scriptFlags(sources.siblings, 'siblings'), [...requiredFlags, '-i', 'src', '-i', 'tests/integration']),
    'sibling Agda flags differ from declared contract');
  checkout.read(core.entrypoint);
  requireThat(sources.core.split('\n').includes(`"$prover" "\${flags[@]}" ${core.entrypoint}`),
    'core runner does not invoke its declared entrypoint');
  requireThat(siblings.entrypoints.length === 2, 'expected both sibling entrypoints');
  for (const [index, flag] of ['echo_flags', 'epi_flags'].entries()) {
    const entrypoint = siblings.entrypoints[index];
    checkout.read(entrypoint);
    requireThat(sources.siblings.split('\n').includes(`"$prover" "\${flags[@]}" "\${${flag}[@]}" ${entrypoint}`),
      `sibling runner does not invoke ${entrypoint}`);
  }

  for (const [label, target] of [['core', core], ['siblings', siblings]]) {
    const expected = target.expected_rejections;
    requireThat(Array.isArray(expected) && expected.length > 0
      && expected.every((name) => typeof name === 'string' && /^[A-Z][A-Za-z0-9]*$/.test(name))
      && new Set(expected).size === expected.length, `invalid ${label} rejection inventory`);
    const actual = checkout.inventory(target.rejection_directory);
    requireThat(equal(actual, [...expected].sort()),
      `${label} rejection inventory mismatch: expected ${JSON.stringify([...expected].sort())}, found ${JSON.stringify(actual)}`);
    requireThat(target.expected_rejection_count === actual.length, `${label} rejection count mismatch`);
  }
  requireThat(sources.core.split('\n').includes(`rejects=(${core.rejection_directory}/*.agda)`),
    'core runner does not enumerate its declared rejection directory');
  for (const [name, prefix] of [['echo_rejects', 'FalseEcho'], ['epi_rejects', 'FalseEpistemic']]) {
    requireThat(sources.siblings.split('\n').includes(`${name}=(${siblings.rejection_directory}/${prefix}*.agda)`),
      'sibling runner does not enumerate its declared rejection directory');
  }

  const fetchSource = checkout.read(siblings.fetch_script);
  requireThat(sources.siblings.split('\n').includes(`bash ${siblings.fetch_script}`),
    'sibling runner does not call its pinned dependency fetcher');
  const pins = [...fetchSource.matchAll(/^fetch\s+(\S+)\s+(\S+)\s+([0-9a-f]{40})\s*$/gm)].map((match) => match.slice(1));
  const expectedPins = [
    ['echo-types', 'hyperpolymath/echo-types', siblings.pins.echo_types],
    ['epistemic-types', 'hyperpolymath/epistemic-types', siblings.pins.epistemic_types],
    ['standard-library', 'agda/agda-stdlib', siblings.pins.standard_library],
  ];
  requireThat(equal(pins, expectedPins), 'sibling fetcher pins differ from the declared contract');

  const packageVersion = single('\\bagda-bin=([^\\s\\\\]+)', workflow, 'pinned Agda package');
  requireThat(packageVersion === agda.debian_package_version, 'workflow Agda package differs from contract');
  const version = single('test "\\$\\(agda --version\\)" = \'Agda version ([^\']+)\'', workflow, 'Agda version assertion');
  requireThat(version === agda.version, 'workflow Agda version assertion differs from contract');
  const bunVersion = single('^\\s*BUN_VERSION:\\s*([0-9.]+)\\s*$', workflow, 'Bun pin');
  requireThat(bunVersion === correspondence.bun_version, 'workflow Bun pin differs from contract');

  const source = sources.correspondence;
  const harnessTests = Number(single('^expected_tests=([0-9]+)$', source, 'harness test-count assertion'));
  requireThat(harnessTests === correspondence.harness_tests, 'correspondence test count differs from contract');
  requireThat(equal(correspondence.required_stages, ['harness', 'table-byte-equality', 'agda-refl-proof']),
    'correspondence stages differ from the required verification chain');
  requireThat(source.includes('"$bun" test tests/correspondence'), 'correspondence harness invocation is missing');
  requireThat(source.includes('"$bun" tests/correspondence/generate-table.js --out "$fresh"'),
    'correspondence table regeneration is missing');
  requireThat(source.includes('diff -u tests/correspondence/ExplorerTable.agda "$fresh"'),
    'correspondence table byte-comparison is missing');
  const invocation = single('^"\\$prover" ([^\\n]*Correspondence\\.agda)\\s*$',
    source.replaceAll('\\\n', ' '), 'correspondence proof invocation');
  requireThat(equal(literalWords(invocation), [...requiredFlags, '-i', 'src', '-i', 'tests/correspondence', correspondence.entrypoint]),
    'correspondence Agda flags or entrypoint differ from contract');
  requireThat(/^checker-matches-explorer : table ≡ expected\nchecker-matches-explorer = refl$/m
    .test(checkout.read(correspondence.entrypoint)), 'declared correspondence refl proof is missing');
  const rows = [...checkout.read('tests/correspondence/ExplorerTable.agda').matchAll(/^\s*(?:∷\s*)?row\b/gm)].length;
  requireThat(rows === correspondence.configurations, 'committed correspondence row count differs from contract');
  return checkout;
}

function expectFailure(document, root, arguments_, expected) {
  try {
    checkDocument(document, root, ...arguments_);
  } catch (error) {
    requireThat(error instanceof ContractError && error.message.includes(expected),
      `regression failed for the wrong reason: ${error.message}`);
    return;
  }
  throw new ContractError(`invalid fixture unexpectedly passed: ${expected}`);
}

function regression(document, baseline, arguments_) {
  const fixture = mkdtempSync(join(tmpdir(), 'proof-contract-'));
  try {
    for (const name of baseline.files) {
      const destination = join(fixture, name);
      mkdirSync(dirname(destination), { recursive: true });
      copyFileSync(join(baseline.root, name), destination);
    }
    checkDocument(document, fixture, ...arguments_);
    const core = document.config.core;
    const script = join(fixture, core.script);
    const original = readText(script);
    requireThat(original.split('flags=(--safe ').length === 2, 'cannot construct safety-flag regression fixture');
    writeFileSync(script, original.replace('flags=(--safe ', 'flags=('));
    expectFailure(document, fixture, arguments_, 'core Agda flags differ from declared contract');
    writeFileSync(script, original);
    console.log('PASS: checkout consistency rejects a removed core safety flag');
    unlinkSync(join(fixture, core.rejection_directory, `${core.expected_rejections[0]}.agda`));
    expectFailure(document, fixture, arguments_, 'core rejection inventory mismatch');
    console.log('PASS: checkout consistency rejects a missing rejection control');
  } finally {
    rmSync(fixture, { recursive: true, force: true });
  }
}

function main(mode, args) {
  if (mode === 'write-driver') {
    requireThat(args.length === 3, 'write-driver requires contract, body and destination paths');
    const [contract, body, destination] = args;
    requireThat(!contract.includes('%{') && !body.includes('%{'), 'Nickel interpolation is not allowed in tool paths');
    writeFileSync(destination, `let K9 = import ${JSON.stringify(contract)} in\n`
      + `let k9_doc = import ${JSON.stringify(body)} in\nk9_doc | K9.Component\n`);
    return;
  }
  if (mode === 'make-negative') {
    requireThat(args.length === 2, 'make-negative requires component and destination paths');
    const text = readText(args[0]);
    const before = '        = ["--safe", "--without-K", "--no-libraries", "--ignore-interfaces", "--double-check"],';
    requireThat(text.split(before).length === 2, 'could not construct the missing-safety-flag fixture unambiguously');
    writeFileSync(args[1], text.replace(before, before.replace('"--safe", ', '')));
    return;
  }
  if (mode === 'assert-negative') {
    requireThat(args.length === 2, 'assert-negative requires exit status and verdict path');
    const result = readJson(args[1]);
    const errors = result.findings.filter((finding) => finding.severity === 'error');
    requireThat(Number(args[0]) === 1 && result.verdict === 'fail' && result.skipped === 0
      && errors.length === 1 && errors[0].rule === 'K9-N001' && errors[0].layer === 'L2'
      && errors[0].message.includes('violates the K9.Component contract'),
    'the missing-safety-flag fixture did not fail at the intended Nickel contract');
    console.log('PASS: Nickel rejects a configured safety-flag omission at K9-N001 / L2');
    return;
  }
  requireThat(mode === 'check', 'expected check, write-driver, make-negative or assert-negative');
  const { values } = parseArgs({ args, strict: true, options: {
    root: { type: 'string' }, document: { type: 'string' }, verdict: { type: 'string' },
    'standards-revision': { type: 'string' }, 'nickel-version': { type: 'string' },
    'nickel-sha256': { type: 'string' }, regression: { type: 'boolean', default: false },
  } });
  for (const name of ['root', 'document', 'verdict', 'standards-revision', 'nickel-version', 'nickel-sha256']) {
    requireThat(typeof values[name] === 'string' && values[name].length > 0, `missing --${name}`);
  }
  const verdict = readJson(values.verdict);
  requireThat(verdict.dialect === 'component' && verdict.contract_version === '1.0.0'
    && verdict.verdict === 'pass' && verdict.errors === 0 && verdict.skipped === 0,
  'canonical validator did not report a complete successful component check');
  const document = readJson(values.document);
  const arguments_ = [values['standards-revision'], values['nickel-version'], values['nickel-sha256']];
  const baseline = checkDocument(document, values.root, ...arguments_);
  console.log('PASS: canonical K9 L2 validation and proof metadata agree with the checkout');
  if (values.regression) regression(document, baseline, arguments_);
}

try {
  main(process.argv[2], process.argv.slice(3));
} catch (error) {
  console.error(`ERROR: proof contract: ${error.message}`);
  process.exitCode = 1;
}
