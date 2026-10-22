# K215: semantic coverage and a shared implication core

Prepared for Vladimir Reshetnikov's ProveIt project, 21 October 2026.

Review pin: `2ca3a5c16f0876d2cab842056353c03a1ed2f5f0`.

## Main recommendation

Let the binary/source simulation consume **semantic edge contracts**, with the existing symbolic checker as one producer of those contracts. This permits shared decoder/primitive/return proofs to replace repeated leaf checks incrementally. In parallel, render the existing representation-independent implication derivation for both assistants through small numerical adapters.

The report explains the mathematics, exact contracts, verification limits, measured negative results and further research questions. No remote repository mutation was performed, and the literal K215 machine was not changed.

## Results and limits

| Component | Delivered result | Verification scope |
|---|---|---|
| Lean runtime interface | `EdgeContract`, `SemanticCovered`, sound adapter from the old checker, mixed coverage, one semantic simulation induction, old APIs retained | Lean 4.32.0: 13 freshly built project modules plus a typed audit; a second standalone source replay also passed |
| Rocq implication | Generic backend for the unchanged existing 58-step derivation and a small numerical adapter | Coq 8.18.0 compatibility build: seven calculus modules through actual `ThmDom`, exact public-type probe, recursive `coqchk` |
| Reachability experiment | Fifteen bounded-value abstract interpretations on the exact source, with post-fixpoint validation | Python finite evidence; independently replayed; **not** a formal source-CFG or runtime theorem |

The Lean refactor adds 129 lines / 5,842 bytes to KSim (356 -> 485 lines; 16,146 -> 21,988 bytes). **It replaces zero concrete K215 leaf checks so far.** It provides the necessary API, with no claim of a current endpoint-wide size reduction or speedup.

The final Rocq generic core plus adapter has 317 lines / 15,626 bytes, versus 1,169 lines / 22,673 bytes for the pinned reflective replay. This is a 72.9% line reduction and a 31.1% byte reduction in those proof sources. The already-proposed 52-step numerical rendering is smaller (11,190 bytes); the present choice favors the shared abstract specification, a truth-free core and additional public goals. The 58-step derivation itself is inherited, not a new discovery.

The reachability experiment removes only 5 of 6,176 obligations (about 0.081%). That is little benefit for adding a formally verified invariant-indexed runtime route. It does not rule out stronger relational invariants.

**Neither complete K215 endpoint was rebuilt in this delivery.** The Rocq production 9.1 build, generated-manifest integration, nontrivial direct primitive contracts, and complete affected endpoint closure remain integration gates. The existing external proof-assistant statements remain distinct from a separately encoded internal PA/ZFC proof. There is no unconditional nonhalting claim.

## Contents

- `report.tex`, `report.pdf`: complete article.
- `lean/`: repository-relative patch, candidate, baseline, all focused source dependencies, typed API audit, reproducibility driver, exact source/object/log bindings and failed/successful attempts.
- `rocq/`: abstract-core backend, unchanged derivation data and upstream renderer, generic proof, numerical adapter, actual calculus client, type probe and build/check evidence.
- `research/`: strategic review, independent source review of the Lean patch, reachability script and complete result.
- `inputs/`: exact dense and native machine tables, source leaves and archived primitive CFG for comparison.
- `licenses/`, `INHERITED_NOTICE.md`: inherited attribution and license material.
- `verification_summary.json`: concise top-level scope, metrics and input identities.
- `MANIFEST.json`, `verify_bundle.py`: per-file integrity manifest and verifier.

The patch is intended for review against the pinned commit. The raw evidence contains the original build paths so that commands and source bindings remain auditable; replay commands below use new local output paths. Compiled proof objects are omitted.

## Reproduce

Run these from the extracted archive root. Choose new empty compiler output directories; the drivers deliberately prevent accidental reuse of unrelated evidence.

```sh
python3 verify_bundle.py

python3 lean/check_semantic.py \
  --lean /path/to/lean-4.32.0-linux/bin/lean \
  --out /tmp/k215-semantic-replay

python3 rocq/verify_rocq.py \
  --coqc /path/to/coqc --coqchk /path/to/coqchk \
  --out /tmp/k215-rho8-replay --baseline

python3 research/reachability_census.py \
  --sites inputs/sites215.json \
  --compare-cfg inputs/p215_flat_cfg.json \
  --output /tmp/k215-reachability.json

latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

The Lean route uses bundled sources without a checkout or network access; `--repo /path/to/ProveIt` selects a checkout-based route instead. The Rocq driver applies `From Stdlib Require` -> `From Coq Require` only in private build copies when using Coq 8.x, and records both source identities. Supplied production-format files retain their original import prefix. Follow `rocq/README.md` for the precise tested/compiler-compatibility boundary.

The integrity script verifies bytes only. The proof compilers and `coqchk` establish the focused formal claims. The reachability script is untrusted finite evidence, not a proof-assistant substitute.

## Integration order

1. Apply and check the semantic-coverage patch while retaining the old public API and all original executable definitions.
2. Integrate the shared Rocq core and synchronized generator/build manifest; recheck it with the production toolchain.
3. Complete one exact primitive family, such as the existing 86-leaf CB1 design, from the checked decoder port through the full continuation and return.
4. Give its finite selector a proved `EdgeContract` interpretation and use the mixed coverage theorem. Keep the checker on all other leaves.
5. Freshly rebuild affected descendants and both exact endpoint clients. A dependency's unchanged compiled bytes do not excuse an unchecked transitive source change.
6. Measure before/after time, peak memory, source size and object size separately on the same machine/toolchain. Include the new interface overhead.

No repository files need to be overwritten merely to replay this archive.
