#!/usr/bin/env bun
// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
// Compare evaluated proof metadata with a bounded set of repository files.
// Configured paths and strings are data; no configured commands are executed.
// Source-shape checks establish consistency, not proof correctness.

import {
  lstatSync, mkdirSync, mkdtempSync, readFileSync,
  readdirSync, realpathSync, rmSync, symlinkSync, unlinkSync, writeFileSync,
} from 'node:fs';
import { dirname, isAbsolute, join, relative, resolve, sep } from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseArgs } from 'node:util';

class ContractError extends Error {}

function requireThat(condition, message) {
  if (!condition) throw new ContractError(message);
}

const equal = (left, right) => JSON.stringify(left) === JSON.stringify(right);
const escapeRegex = (text) => text.replace(/[.*+?^${}()|[\]\\]/g, String.raw`\$&`);
const ordinal = (left, right) => left < right ? -1 : Number(left > right);
const repositoryRoot = realpathSync(fileURLToPath(new URL('..', import.meta.url)));
const cacheDirectory = '_build/k9-tools';
const logDirectory = '_build/check-logs/contract';
const componentPath = 'contractiles/k9/proof-validation.k9.ncl';
const contractPath = '1-formats/k9/spec/contract/k9_contract.ncl';
const validatorPath = '1-formats/k9/tools/k9-validate.sh';

// Every filesystem name is relative to an internally selected boundary.
// Check every existing segment, including dangling links and parent links.
function boundedPath(root, name) {
  requireThat(typeof name === 'string' && name.length > 0 && !isAbsolute(name)
    && /^[A-Za-z0-9_./-]+$/.test(name)
    && name.split('/').every((part) => part && part !== '.' && part !== '..'),
  `unsafe configured path: ${JSON.stringify(name)}`);
  const path = resolve(root, name);
  requireThat(path.startsWith(`${root}${sep}`), `path escapes checkout: ${name}`);
  const parts = name.split('/');
  let current = root;
  for (const [index, part] of parts.entries()) {
    current = join(current, part);
    try {
      const info = lstatSync(current);
      requireThat(!info.isSymbolicLink(), `symbolic links are not allowed: ${name}`);
      requireThat(index === parts.length - 1 || info.isDirectory(), `path parent is not a directory: ${name}`);
    } catch (error) {
      if (error.code !== 'ENOENT') throw error;
    }
  }
  return path;
}

class Checkout {
  constructor(relativeRoot = '') {
    this.root = relativeRoot ? boundedPath(repositoryRoot, relativeRoot) : repositoryRoot;
    requireThat(lstatSync(this.root).isDirectory(), 'checkout boundary must be an existing directory');
    this.files = new Set();
  }

  path(name) {
    return boundedPath(this.root, name);
  }

  read(name) {
    const path = this.path(name);
    requireThat(lstatSync(path).isFile(), `required file is missing: ${name}`);
    this.files.add(name);
    return readFileSync(path, 'utf8');
  }

  json(name) {
    return JSON.parse(this.read(name));
  }

  mkdir(name) {
    mkdirSync(this.path(name), { recursive: true });
  }

  write(name, text) {
    requireThat(this.root.startsWith(`${repositoryRoot}${sep}${cacheDirectory}${sep}`),
      'generated files must stay in a temporary cache directory');
    writeFileSync(this.path(name), text);
  }

  inventory(name) {
    const directory = this.path(name);
    requireThat(lstatSync(directory).isDirectory(),
      `rejection directory is missing: ${name}`);
    const files = readdirSync(directory).filter((file) => file.endsWith('.agda')).sort(ordinal);
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
  return literalWords(single(String.raw`^flags=\(([^\n]*)\)$`, source, `${label} flags assignment`));
}

function checkRecipe(justfile, target, script) {
  requireThat(typeof target === 'string' && /^[a-z][a-z0-9-]*$/.test(target),
    `invalid Just target: ${JSON.stringify(target)}`);
  const body = single(String.raw`^${escapeRegex(target)}:[^\n]*\n((?:[ \t]+[^\n]*\n|\n)*)`,
    `${justfile}\n`, `Just target ${target}`);
  const commands = body.split('\n').map((line) => line.trim())
    .filter((line) => line && !line.startsWith('#'));
  requireThat(equal(commands, [`bash ${script}`]), `Just target ${target} differs from its declared script`);
}

function checkDocument(document, checkout, standardsRevision, nickelVersion, nickelSha256) {
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

  const requiredFlags = ['--safe', '--without-K', '--cubical-compatible', '--no-libraries', '--ignore-interfaces', '--double-check'];
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
    requireThat(new RegExp(String.raw`^\s*run:\s*bash\s+${escapeRegex(target.script)}\s*$`, 'm').test(workflow),
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
    const sortedExpected = [...expected].sort(ordinal);
    requireThat(equal(actual, sortedExpected),
      `${label} rejection inventory mismatch: expected ${JSON.stringify(sortedExpected)}, found ${JSON.stringify(actual)}`);
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

  const packageVersion = single(String.raw`\bagda-bin=([^\s\\]+)`, workflow, 'pinned Agda package');
  requireThat(packageVersion === agda.debian_package_version, 'workflow Agda package differs from contract');
  const version = single(String.raw`test "\$\(agda --version\)" = 'Agda version ([^']+)'`, workflow, 'Agda version assertion');
  requireThat(version === agda.version, 'workflow Agda version assertion differs from contract');
  const bunVersion = single(String.raw`^\s*BUN_VERSION:\s*([0-9.]+)\s*$`, workflow, 'Bun pin');
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
  const invocation = single(String.raw`^"\$prover" ([^\n]*Correspondence\.agda)\s*$`,
    source.replaceAll('\\\n', ' '), 'correspondence proof invocation');
  requireThat(equal(literalWords(invocation), [...requiredFlags, '-i', 'src', '-i', 'tests/correspondence', correspondence.entrypoint]),
    'correspondence Agda flags or entrypoint differ from contract');
  requireThat(/^checker-matches-explorer : table ≡ expected\nchecker-matches-explorer = refl$/m
    .test(checkout.read(correspondence.entrypoint)), 'declared correspondence refl proof is missing');
  let rows = 0;
  for (const line of checkout.read('tests/correspondence/ExplorerTable.agda').split('\n')) {
    const tokens = line.trim().split(/\s+/);
    if ((tokens[0] === '∷' ? tokens[1] : tokens[0]) === 'row') rows += 1;
  }
  requireThat(rows === correspondence.configurations, 'committed correspondence row count differs from contract');
  return checkout;
}

function expectFailure(action, expected) {
  try {
    action();
  } catch (error) {
    requireThat(error instanceof ContractError && error.message.includes(expected),
      `regression failed for the wrong reason: ${error.message}`);
    return;
  }
  throw new ContractError(`invalid fixture unexpectedly passed: ${expected}`);
}

function regression(document, baseline, arguments_) {
  const cache = new Checkout(cacheDirectory);
  const temporary = mkdtempSync(cache.path('regression.'));
  const work = new Checkout(relative(repositoryRoot, temporary));
  try {
    work.mkdir('checkout');
    work.write('outside.txt', 'path-boundary sentinel');
    const fixture = new Checkout(relative(repositoryRoot, work.path('checkout')));
    for (const name of baseline.files) {
      if (dirname(name) !== '.') fixture.mkdir(dirname(name));
      fixture.write(name, baseline.read(name));
    }
    checkDocument(document, fixture, ...arguments_);
    const core = document.config.core;
    const original = fixture.read(core.script);
    requireThat(original.split('flags=(--safe ').length === 2, 'cannot construct safety-flag regression fixture');
    fixture.write(core.script, original.replace('flags=(--safe ', 'flags=('));
    expectFailure(() => checkDocument(document, fixture, ...arguments_), 'core Agda flags differ from declared contract');
    fixture.write(core.script, original);
    console.log('PASS: checkout consistency rejects a removed core safety flag');
    unlinkSync(fixture.path(`${core.rejection_directory}/${core.expected_rejections[0]}.agda`));
    expectFailure(() => checkDocument(document, fixture, ...arguments_), 'core rejection inventory mismatch');
    console.log('PASS: checkout consistency rejects a missing rejection control');

    expectFailure(() => fixture.read('../outside.txt'), 'unsafe configured path');
    expectFailure(() => fixture.write('../outside.txt', 'changed'), 'unsafe configured path');
    console.log('PASS: path boundaries reject parent traversal for reads and writes');
    symlinkSync(work.root, fixture.path('linked-parent'), 'dir');
    expectFailure(() => fixture.read('linked-parent/outside.txt'), 'symbolic links are not allowed');
    expectFailure(() => fixture.write('linked-parent/outside.txt', 'changed'), 'symbolic links are not allowed');
    requireThat(work.read('outside.txt') === 'path-boundary sentinel', 'path-boundary sentinel was changed');
    console.log('PASS: path boundaries reject symbolic-link parents for reads and writes');
  } finally {
    rmSync(temporary, { recursive: true, force: true });
  }
}

function standardsDirectory(revision) {
  requireThat(typeof revision === 'string' && /^[0-9a-f]{40}$/.test(revision), 'invalid standards revision');
  return `${cacheDirectory}/standards-${revision}`;
}

function temporaryCheckout(identifier) {
  requireThat(typeof identifier === 'string' && /^check\.[A-Za-z0-9]{6}$/.test(identifier),
    'invalid temporary cache identifier');
  return new Checkout(`${cacheDirectory}/${identifier}`);
}

function main(mode, args) {
  const repository = new Checkout();
  if (mode === 'prepare') {
    requireThat(args.length === 2 && /^\d{1,3}\.\d{1,3}\.\d{1,3}$/.test(args[1]),
      'prepare requires standards revision and Nickel version');
    const standards = standardsDirectory(args[0]);
    for (const name of [cacheDirectory, logDirectory, `${standards}/${dirname(contractPath)}`, `${standards}/${dirname(validatorPath)}`]) {
      repository.mkdir(name);
    }
    for (const name of [componentPath, `${cacheDirectory}/nickel-${args[1]}`, `${standards}/${contractPath}`, `${standards}/${validatorPath}`,
      ...['canonical.json', 'canonical.log', 'evaluated.json', 'export.log', 'without-safe.json', 'without-safe.log']
        .map((file) => `${logDirectory}/${file}`)]) {
      repository.path(name);
    }
    return;
  }
  if (mode === 'write-driver') {
    requireThat(args.length === 2, 'write-driver requires temporary cache identifier and standards revision');
    const temporary = temporaryCheckout(args[0]);
    const contractName = `${standardsDirectory(args[1])}/${contractPath}`;
    repository.read(contractName);
    temporary.read('body.ncl');
    const contract = repository.path(contractName);
    const body = temporary.path('body.ncl');
    requireThat(!contract.includes('%{') && !body.includes('%{'), 'Nickel interpolation is not allowed in tool paths');
    temporary.write('driver.ncl', `let K9 = import ${JSON.stringify(contract)} in\n`
      + `let k9_doc = import ${JSON.stringify(body)} in\nk9_doc | K9.Component\n`);
    return;
  }
  if (mode === 'make-negative') {
    requireThat(args.length === 1, 'make-negative requires temporary cache identifier');
    const temporary = temporaryCheckout(args[0]);
    const text = repository.read(componentPath);
    const before = '        = ["--safe", "--without-K", "--cubical-compatible", "--no-libraries", "--ignore-interfaces", "--double-check"],';
    requireThat(text.split(before).length === 2, 'could not construct the missing-safety-flag fixture unambiguously');
    temporary.write('without-safe.k9.ncl', text.replace(before, before.replace('"--safe", ', '')));
    return;
  }
  if (mode === 'assert-negative') {
    requireThat(args.length === 1, 'assert-negative requires exit status');
    const result = repository.json(`${logDirectory}/without-safe.json`);
    const errors = result.findings.filter((finding) => finding.severity === 'error');
    requireThat(Number(args[0]) === 1 && result.verdict === 'fail' && result.skipped === 0
      && errors.length === 1 && errors[0].rule === 'K9-N001' && errors[0].layer === 'L2'
      && errors[0].message.includes('violates the K9.Component contract'),
    'the missing-safety-flag fixture did not fail at the intended Nickel contract');
    console.log('PASS: Nickel rejects a configured safety-flag omission at K9-N001 / L2');
    return;
  }
  requireThat(mode === 'check', 'expected prepare, check, write-driver, make-negative or assert-negative');
  const { values } = parseArgs({ args, strict: true, options: {
    'standards-revision': { type: 'string' }, 'nickel-version': { type: 'string' },
    'nickel-sha256': { type: 'string' }, regression: { type: 'boolean', default: false },
  } });
  for (const name of ['standards-revision', 'nickel-version', 'nickel-sha256']) {
    requireThat(typeof values[name] === 'string' && values[name].length > 0, `missing --${name}`);
  }
  const verdict = repository.json(`${logDirectory}/canonical.json`);
  requireThat(verdict.dialect === 'component' && verdict.contract_version === '1.0.0'
    && verdict.verdict === 'pass' && verdict.errors === 0 && verdict.skipped === 0,
  'canonical validator did not report a complete successful component check');
  const document = repository.json(`${logDirectory}/evaluated.json`);
  const arguments_ = [values['standards-revision'], values['nickel-version'], values['nickel-sha256']];
  const baseline = checkDocument(document, new Checkout(), ...arguments_);
  console.log('PASS: canonical K9 L2 validation and proof metadata agree with the checkout');
  if (values.regression) regression(document, baseline, arguments_);
}

try {
  main(process.argv[2], process.argv.slice(3));
} catch (error) {
  console.error(`ERROR: proof contract: ${error.message}`);
  process.exitCode = 1;
}
