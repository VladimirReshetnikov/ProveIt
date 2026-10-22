# Further simplification of the K215 correctness proofs

**Research and checked implementation packet — 21 October 2026.**

Baseline: `VladimirReshetnikov/ProveIt` at
`57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`.

The complete report is `article/report.pdf`, with source `article/report.tex`.
It contains the mathematical arguments, source review, measurements, exact
verification scope, integration order, attribution, and further research questions.

## Main recommendation

Share the implication derivation between the dominated and ordinary calculi;
retain both halting witnesses in one run invariant; and separate the power-set
interface from the calibration proofs that happen to contain it.

| Measured scope | Baseline | Proposed | Saving |
|---|---:|---:|---:|
| Lean shared logic, bytes | 42,454 | 18,243 | 24,211 / 57.03% |
| Lean shared logic, lines | 811 | 401 | 410 |
| Rocq shared logic, bytes | 45,538 | 18,708 | 26,830 / 58.92% |
| Rocq shared logic, lines | 1,399 | 394 | 1,005 |
| Lean `blank_iff` theorem, lines | 52 | 37 | 15 / 28.85% |
| Lean `blank_iff` theorem, bytes | 2,230 | 1,630 | 600 |
| Endpoint import closure, modules | 179 | 177 | 2 |
| Endpoint source closure, all Lean changes | 2,129,439 | 2,075,787 | 53,652 bytes |

Logic counts include the shared core and all replaced adapters. The Rocq
numbers use production `Stdlib` spelling on both sides. The checked Coq 8.18
variants are three bytes smaller on each side, with the same saving.
The power-set extraction alone removes 28,841
bytes from the endpoint's selected closure while adding 320 bytes globally
across its edited/new files. These are source and dependency measurements,
not controlled build-time benchmarks or proof-term minima.

## What is already prior work

The six-goal, 58-detachment implication plan and Lean adapter are attributed
existing proposals, archived under phase twelve's upstream-merge inputs.
They are **not** the production checked core at this baseline: the recent
merges preserve the phase-eleven core and older unrestricted derivation.

This packet connects both actual Rocq client families to the archived plan,
checks the Lean proposal against the current source tree, and adds the
single-invariant dense bridge and exact `PowerSets` extraction. The recommended
Rocq ordinary-logic adapter uses domination `True`, independently of the
numeric adapter, matching Lean's instantiation. This costs nine lines and
348 bytes compared with routing it through numeric domination.

## Package map

- `lean_logic/`: two replacement modules, shared-logic patch, exact-type
  clients, isolated baseline/candidate checker, raw evidence.
- `dense_bridge/`: replacement `KDenseBridge.lean`, patch, original-type
  audit, reproduction script and evidence.
- `semantic_interface/`: exact definition move, import changes, source and
  dependency measurements, fresh local check including the legacy consumer.
- `rocq_shared/`: generic proof, both adapters, focused dependencies, attributed
  plan/renderer, baseline sources, source patches, compiler and recursive
  kernel evidence.
- `tools/`: SHA-256 integrity checker, combined Lean checker, ordered
  reproduction entry point.
- `evidence/`: combined Lean check, shared-plan identity, integration checks,
  and package-reproduction result.
- `article/`: LaTeX and compiled PDF.

Compiled proof objects are excluded. Do not interpret an integrity-only
manifest check as a proof-kernel check.

## Verification boundary

- Lean **4.32.0**, official commit
  `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
- Shared logic: 16 fresh project modules in each variant, the same typed
  audit, and the additional generic-basis audit in the candidate. The common
  audit output and Tarski bridge tail are byte-identical.
- Dense bridge: unchanged dependency closure, baseline and replacement, exact
  original theorem type; both axiom reports are `[propext, Quot.sound]`.
- Power-set extraction: 29 fresh project modules, including the old calibration
  consumer; exact definition and public model-theorem type checked.
- **Combined Lean candidate: 47 fresh project modules plus four typed audits.**
- Rocq sources: **Coq 8.18.0**, with the standard-library spelling normalization
  `Stdlib` to `Coq`; nine baseline and ten candidate modules, exact facade and
  real propositional client-fragment checks, recursive `coqchk` for both.
  The candidate's 24 assumption reports are closed under the global context.

The complete modified `KEndpoint215` closure and the full production Rocq
9.1 endpoint were **not** rebuilt. The production-spelling patch was checked
for applicability, not compiled under Rocq 9.1. The literal 215-state table
and the endpoint theorem statements are unchanged by these proposals.

This packet does not supply an internal PA/ZFC derivation, a new machine,
or a proof of actual nonhalting. It preserves the existing external
correctness interfaces and provides local integration evidence.

## Reproduce

Use Python 3.11 or newer, a pristine checkout at the baseline revision, Lean
4.32.0, and Coq 8.18 `coqc`/`coqchk` on `PATH`:

```sh
python3 tools/verify_packet.py
python3 tools/reproduce_all.py \
  --repo /absolute/path/to/ProveIt \
  --lean /absolute/path/to/lean-4.32.0/bin/lean \
  --out /tmp/k215-simplification-recheck
```

The output directory must not exist. The check does not edit the checkout or
the distributed source/evidence; private copies are used by component drivers
that generate beside themselves. No downloads or Mathlib cache are needed.

To rerun only the combined Lean replacement:

```sh
python3 tools/check_combined.py \
  --repo /absolute/path/to/ProveIt \
  --lean /absolute/path/to/lean-4.32.0/bin/lean \
  --out /tmp/k215-combined-check
```

To rebuild the report:

```sh
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

## Incorporation

The report recommends the semantic-interface and dense-bridge patches first,
followed by the shared logic integration. The three Lean patches and the
Rocq production-spelling patch pass `git apply --check` together at the
baseline. Use `rocq_shared/proof-sources-rocq91.patch` for production spelling;
`proof-sources.patch` mirrors the locally checked Coq 8.18 sources.

The Rocq patches change proof sources only. Production incorporation must add
the new module to the build order, update `regenerate215.py`, and refresh
source manifests/receipts. Adopt the six-goal plan in the maintained Lean
producer as well. Rebuild affected real consumers and the complete endpoints
with the pinned production toolchains before publishing a replacement checked
checkpoint. Do not re-label old receipts as verification of new sources.

Rocq's consumed facade theorems are preserved, but generated internal names
`cd_0` through `cd_106` and the old `Certificate` implementation are removed.
Any wider consumer of those internal names needs a compatibility layer.
