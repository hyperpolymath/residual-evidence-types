// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
'use strict';

// Correspondence harness for the explorer's JavaScript model.
// Run with:  bun test tests/correspondence
//
// Every known-answer row below is derived BY HAND from the model's own loop
// (residual-evidence-explorer.html, first <script> block):
//
//   for latent in −6..6:              (ascending)
//     for noise in −6..6:             (ascending)
//       keep (latent, noise) iff  |noise| ≤ noiseBound
//                             and (¬assumeZero ∨ latent = 0)
//                             and observe(latent + noise) = observe(residual)
//
//   count    = number kept
//   presence = decide(c, w ⇒ w.latent ≠ 0).status:
//                no candidates ⇒ inconsistent;
//                no counterexample (every latent ≠ 0) ⇒ entailed;
//                else no supporting (every latent = 0) ⇒ refuted;
//                else ⇒ unresolved.
//   identity = identify(c, w ⇒ w.latent).status:
//                no candidates ⇒ inconsistent (spelled no-candidate in Agda);
//                one distinct latent ⇒ identified; else unidentified.
//   values   = the distinct latents, ascending.
//
// The derivations are worked from that loop, not by running it: running the
// model to produce its own expected values would prove nothing.

import { describe, expect, test } from 'bun:test';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';

import { LIMIT, VIEWS, configs, makeCase, rowOf } from './explorer-model.js';
import { renderTable, rowLine } from './generate-table.js';

const TABLE_PATH = resolve(import.meta.dir, 'ExplorerTable.agda');

describe('model', () => {
  test('is the signed-integer-v1 model with LIMIT 6 and the three views', () => {
    expect(LIMIT).toBe(6);
    expect(makeCase({ residual: 0, noiseBound: 0, view: 'exact', assumeZero: false }).model).toBe('signed-integer-v1');
    expect(VIEWS).toEqual(['exact', 'sign', 'magnitude']);
  });
});

describe('configuration order', () => {
  test('configs() yields exactly 546 configurations in the contract order', () => {
    // Contract order: residual −6..6 ascending (outer), noiseBound 0..6,
    // view exact|sign|magnitude, assumeZero false|true (inner).
    // 13 residuals × 7 bounds × 3 views × 2 flags = 546.
    // Enumerated here with explicit loops so the assertion is independent
    // of the generator under test.
    const expected = [];
    for (let residual = -6; residual <= 6; residual++) {
      for (let noiseBound = 0; noiseBound <= 6; noiseBound++) {
        for (const view of ['exact', 'sign', 'magnitude']) {
          for (const assumeZero of [false, true]) {
            expected.push({ residual, noiseBound, view, assumeZero });
          }
        }
      }
    }
    expect(expected.length).toBe(546);
    const actual = [...configs()];
    expect(actual.length).toBe(546);
    expect(actual).toEqual(expected);
  });
});

// Each known-answer row: the configuration, the row the model must report,
// and the exact Agda spelling the generator must emit for it.
const KNOWN = [
  {
    // ROW 0 of the table (the contract's first row).
    // residual −6, bound 0, exact, assumeZero false.
    //   |noise| ≤ 0            ⇒ noise = 0
    //   latent + 0 = −6        ⇒ latent = −6            ⇒ kept: (−6, 0)
    //   count 1; latent ≠ 0 everywhere ⇒ no counterexample ⇒ entailed
    //   one distinct latent {−6} ⇒ identified; values [−6] = negsuc 5
    name: 'row 0: residual −6, bound 0, exact, assumeZero false',
    cfg: { residual: -6, noiseBound: 0, view: 'exact', assumeZero: false },
    row: { count: 1, presence: 'entailed', identity: 'identified', values: [-6] },
    agda: 'row (negsuc 5) 0 exact false 1 entailed identified (negsuc 5 ∷ [])',
  },
  {
    // ROW 1 of the table (the contract's second row).
    // residual −6, bound 0, exact, assumeZero true.
    //   noise = 0 and latent = 0 ⇒ sum 0 ≠ −6           ⇒ nothing kept
    //   count 0 ⇒ presence inconsistent; identify inconsistent (no-candidate); values []
    name: 'row 1: residual −6, bound 0, exact, assumeZero true',
    cfg: { residual: -6, noiseBound: 0, view: 'exact', assumeZero: true },
    row: { count: 0, presence: 'inconsistent', identity: 'inconsistent', values: [] },
    agda: 'row (negsuc 5) 0 exact true 0 inconsistent no-candidate []',
  },
  {
    // REFUTED. residual 2, bound 6, exact, assumeZero true.
    //   assumeZero ⇒ latent = 0
    //   |noise| ≤ 6 (no restriction inside −6..6); 0 + noise = 2 ⇒ noise = 2   ⇒ kept: (0, 2)
    //   count 1; latent = 0 ⇒ no supporting world, one counterexample ⇒ refuted
    //   distinct latents {0} ⇒ identified; values [0] = pos 0
    name: 'refuted: residual 2, bound 6, exact, assumeZero true',
    cfg: { residual: 2, noiseBound: 6, view: 'exact', assumeZero: true },
    row: { count: 1, presence: 'refuted', identity: 'identified', values: [0] },
    agda: 'row (pos 2) 6 exact true 1 refuted identified (pos 0 ∷ [])',
  },
  {
    // ENTAILED + UNIDENTIFIED. residual 2, bound 1, exact, assumeZero false.
    //   |noise| ≤ 1 ⇒ noise ∈ {−1, 0, 1};  latent = 2 − noise ∈ {3, 2, 1}, all within −6..6
    //   loop order (latent ascending): (1, 1), (2, 0), (3, −1)          ⇒ count 3
    //   every latent ≠ 0 ⇒ entailed
    //   distinct latents {1, 2, 3} ⇒ unidentified; values [1, 2, 3]
    name: 'entailed+unidentified: residual 2, bound 1, exact, assumeZero false',
    cfg: { residual: 2, noiseBound: 1, view: 'exact', assumeZero: false },
    row: { count: 3, presence: 'entailed', identity: 'unidentified', values: [1, 2, 3] },
    agda: 'row (pos 2) 1 exact false 3 entailed unidentified (pos 1 ∷ pos 2 ∷ pos 3 ∷ [])',
  },
  {
    // SIGN VIEW. residual −3, bound 1, sign, assumeZero false.
    //   observe = Math.sign; sign(−3) = −1, so keep iff latent + noise < 0, |noise| ≤ 1:
    //     noise = −1: latent − 1 < 0 ⇒ latent ≤ 0  ⇒ latent ∈ {−6..0}  ⇒ 7 worlds
    //     noise =  0: latent     < 0 ⇒ latent ≤ −1 ⇒ latent ∈ {−6..−1} ⇒ 6 worlds
    //     noise =  1: latent + 1 < 0 ⇒ latent ≤ −2 ⇒ latent ∈ {−6..−2} ⇒ 5 worlds
    //   count 7 + 6 + 5 = 18
    //   latent = 0 occurs (with noise −1) ⇒ a counterexample; latent ≠ 0 occurs ⇒ supporting
    //     ⇒ unresolved
    //   distinct latents {−6, −5, −4, −3, −2, −1, 0} ⇒ unidentified
    //   values ascending: −6 −5 −4 −3 −2 −1 0 = negsuc 5 … negsuc 0, pos 0
    name: 'sign view: residual −3, bound 1, sign, assumeZero false',
    cfg: { residual: -3, noiseBound: 1, view: 'sign', assumeZero: false },
    row: { count: 18, presence: 'unresolved', identity: 'unidentified', values: [-6, -5, -4, -3, -2, -1, 0] },
    agda: 'row (negsuc 2) 1 sign false 18 unresolved unidentified (negsuc 5 ∷ negsuc 4 ∷ negsuc 3 ∷ negsuc 2 ∷ negsuc 1 ∷ negsuc 0 ∷ pos 0 ∷ [])',
  },
  {
    // MAGNITUDE VIEW. residual 2, bound 0, magnitude, assumeZero false.
    //   observe = Math.abs; |noise| ≤ 0 ⇒ noise = 0; |latent| = |2| = 2 ⇒ latent ∈ {−2, 2}
    //   loop order: (−2, 0), (2, 0)                                      ⇒ count 2
    //   every latent ≠ 0 ⇒ entailed
    //   distinct latents {−2, 2} ⇒ unidentified (the sign is unavailable); values [−2, 2]
    //   −2 = negsuc 1, 2 = pos 2
    name: 'magnitude view: residual 2, bound 0, magnitude, assumeZero false',
    cfg: { residual: 2, noiseBound: 0, view: 'magnitude', assumeZero: false },
    row: { count: 2, presence: 'entailed', identity: 'unidentified', values: [-2, 2] },
    agda: 'row (pos 2) 0 magnitude false 2 entailed unidentified (negsuc 1 ∷ pos 2 ∷ [])',
  },
];

describe('known-answer rows', () => {
  for (const k of KNOWN) {
    test(k.name, () => {
      const row = rowOf(k.cfg);
      expect(row).toEqual({ ...k.cfg, ...k.row });
      expect(rowLine(row)).toBe(k.agda);
    });
  }
});

describe('emitted table', () => {
  test('starts with the contract header and the two contract rows, verbatim', () => {
    const lines = renderTable().split('\n');
    expect(lines.slice(0, 15)).toEqual([
      '{-# OPTIONS --safe --without-K #-}',
      '-- SPDX-License-Identifier: MPL-2.0',
      '-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell',
      '-- GENERATED by tests/correspondence/generate-table.js from residual-evidence-explorer.html',
      "-- (model 'signed-integer-v1'). Do not edit; regenerate and diff.",
      '',
      'module ExplorerTable where',
      '',
      'open import Agda.Builtin.Int using (Int; pos; negsuc)',
      'open import Agda.Builtin.Bool using (Bool; true; false)',
      'open import Agda.Builtin.List using (List; []; _∷_)',
      'open import ResidualEvidence.Finite.Row',
      '',
      'expected : List Row',
      'expected =',
    ]);
    expect(lines[15]).toBe('    row (negsuc 5) 0 exact false 1 entailed identified (negsuc 5 ∷ [])');
    expect(lines[16]).toBe('  ∷ row (negsuc 5) 0 exact true 0 inconsistent no-candidate []');
  });

  test('carries exactly 546 rows, closes the list, and ends with one LF', () => {
    const text = renderTable();
    const lines = text.split('\n');
    const rows = lines.filter(l => /^(    |  ∷ )row /.test(l));
    expect(rows.length).toBe(546);
    expect(lines.at(-2)).toBe('  ∷ []');
    expect(lines.at(-1)).toBe('');
    expect(text.endsWith('\n\n')).toBe(false);
    expect(text.includes('\r')).toBe(false);
  });
});

describe('drift', () => {
  test('regenerating the table equals the committed ExplorerTable.agda byte for byte', () => {
    const committed = readFileSync(TABLE_PATH);
    const regenerated = renderTable();
    expect(regenerated).toBe(committed.toString('utf8'));
    expect(Buffer.from(regenerated, 'utf8').equals(committed)).toBe(true);
  });
});

