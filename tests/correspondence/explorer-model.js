// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
'use strict';

// Loads the explorer's JavaScript model straight from the HTML page so that
// the harness and the page can never disagree about what the model says.
//
// Source of truth: the FIRST <script> block of residual-evidence-explorer.html
// at the repo root, which defines
//   globalThis.ResidualEvidence = { LIMIT, makeCase, decide, identify }.
// The HTML is never edited here; it is read and evaluated as-is.

import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';

const HTML_PATH = resolve(import.meta.dir, '..', '..', 'residual-evidence-explorer.html');

function firstScriptBlock(html) {
  const m = /<script\b[^>]*>([\s\S]*?)<\/script>/.exec(html);
  if (!m) throw new Error(`no <script> block found in ${HTML_PATH}`);
  if (!m[1].includes('globalThis.ResidualEvidence')) {
    throw new Error(`first <script> block of ${HTML_PATH} does not define globalThis.ResidualEvidence`);
  }
  return m[1];
}

function loadModel() {
  const src = firstScriptBlock(readFileSync(HTML_PATH, 'utf8'));
  // The block writes to `globalThis`; hand it a private object under that
  // name so evaluation touches neither the real global nor the DOM.
  const sandbox = {};
  new Function('globalThis', src)(sandbox);
  const model = sandbox.ResidualEvidence;
  if (!model) throw new Error('evaluating the model block did not define ResidualEvidence');
  for (const k of ['LIMIT', 'makeCase', 'decide', 'identify']) {
    if (!(k in model)) throw new Error(`model is missing ${k}`);
  }
  return model;
}

const model = loadModel();

export const LIMIT = model.LIMIT;
export const makeCase = model.makeCase;
export const decide = model.decide;
export const identify = model.identify;

export const VIEWS = Object.freeze(['exact', 'sign', 'magnitude']);

// The 546 configurations in CONTRACT ORDER:
//   residual −LIMIT..LIMIT ascending (outer), noiseBound 0..LIMIT,
//   view in VIEWS order, assumeZero false then true (inner).
export function* configs() {
  for (let residual = -LIMIT; residual <= LIMIT; residual++) {
    for (let noiseBound = 0; noiseBound <= LIMIT; noiseBound++) {
      for (const view of VIEWS) {
        for (const assumeZero of [false, true]) {
          yield Object.freeze({ residual, noiseBound, view, assumeZero });
        }
      }
    }
  }
}

// One table row, with the statuses exactly as the JS model spells them.
// (The Agda spelling `no-candidate` for an inconsistent identity is applied
// by the generator, not here.)
export function rowOf(cfg) {
  const { residual, noiseBound, view, assumeZero } = cfg;
  const c = makeCase({ residual, noiseBound, view, assumeZero });
  const presence = decide(c, w => w.latent !== 0);
  const identity = identify(c, w => w.latent);
  return {
    residual,
    noiseBound,
    view,
    assumeZero,
    count: c.candidates.length,
    presence: presence.status,
    identity: identity.status,
    values: identity.values,
  };
}
