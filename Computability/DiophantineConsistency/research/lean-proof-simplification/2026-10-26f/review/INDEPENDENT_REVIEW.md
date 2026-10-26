# Independent review of simplification claims

Reviewed source: ProveIt commit `60e9c5d620c6c387d932876cfa2d9376f64ea56c`.
Review date: 2026-10-26. This is an independent **source-level review**, not a
Lean compilation or proof certificate. Every supplied Lean candidate remains
**UNCOMPILED**. No source-snapshot or upstream repository files were changed.

## Findings

No obvious mathematical weakening was found in the inspected candidates.
The strongest initial changes are reuse of `half_base_bound`, the explicit
sum-of-squares proof, and the generic nine-coordinate packaging proof. The
following checks support that recommendation, without establishing elaboration:

* **31-variable bound.** The existing generic theorem immediately preceding
  the specialization has the same strict conclusion and encoding.
  `4 * (31 + 1)^2 = 4096` exactly. The proposed specialization retains every
  original hypothesis; it does not weaken the half-base bound. The final
  source candidate uses the two-line body shown in the replacement excerpts.
* **Sum of squares.** The conclusion retains all five residuals, including
  `nk * nt - 1` rather than separate unit-sign assumptions. Nonnegativity is
  available over the original integer domain. The explicit fallback exposes
  the required premises and avoids relying on conditional simplifier discharge.
  The concise and explicit proofs are alternatives, not additive savings.
* **Nine coordinates.** Independently compared the raw pinned line ranges:
  Split 98–157 and Gap 53–112 are identical, 60 lines and 2,292 UTF-8 bytes
  excluding the trailing newline, SHA-256
  `760e5c16d9b8399e9e4d76e3e77c3fc6a6eee7ddb61a631924b90b5b7beb7508`.
  The generic evaluator, `HasZero`, and four compatibility statements preserve
  the original binders and positivity. Internal `j` remains unrestricted;
  positive slot 7 stores `j + 1`, while natural slot 7 stores `j`. The helper
  assumes no source correctness. A net 60-line reduction is not established.
* **Degree profiles.** The proposed inequalities `d1 < d2 + 116` and
  `d0 < d2 + 232` match the lower-layer domination argument. The proposed
  upper target `d2 + 233` gives exactly 2162 and 2083. The reports correctly
  retain the distinct leading-coefficient conditions and do not identify
  the two `KernelBounds` structures.
* **Circuit APIs.** Inspected `run_node_equation`, `run_power`, the proposed
  finite `PowerStep` certificates, and wrapper bodies. The generic theorems
  already exist; the proposal reuses them rather than claiming new generic
  DAG soundness. The original literal DAG and universal `CommRing` scope are
  retained. Zero labels mean uncertified, not exponent zero. No obvious API
  argument mismatch was found, but finite proof cost and elaboration remain
  untested.
* **Other local candidates.** The finite-set intersection, predecessor-power,
  convolution factorization, modular-residue, and finite-switch changes retain
  the visible mathematical conditions. The optional digit-branch proof is
  correctly marked cosmetic, not a demonstrated improvement over reuse of
  `highDigits_lt`. No broad `Mathlib` production import is recommended.
* **Trust and architecture.** The reports distinguish current source/window
  APIs from proposed compositions, preserve the same witness across fields,
  and prohibit adding decoded/no-carry premises. Validation correctly separates
  lexical scans and log parsing from kernel and transitive axiom checks.

## Independently reproduced measurements

| Candidate | Original lines | Candidate lines | Original bytes | Candidate bytes | Identical public header strings |
|---|---:|---:|---:|---:|---:|
| Split Steps | 3,445 | 3,074 | 169,808 | 171,042 | 622 |
| Gap Steps | 3,122 | 2,833 | 153,802 | 154,928 | 570 |
| Total | 6,567 | 5,907 | 323,610 | 325,970 | 1,192 |

The final, audit-inclusive experiment has **660 fewer source lines but 2,360
more bytes**, with 193 per-power `ring` calls replaced. These are source-text
measurements, not elaborated type equality, byte compression, node reduction,
runtime savings, or proof-term reduction. The compact facade candidates are
not drop-in replacements. `independent_checks.json` records the direct counts.

The supplied circuit generator was rerun with a separate output directory.
Both API-preserving outputs matched the delivered files byte-for-byte; finite
topology/exponent checks and their deliberately corrupted negative cases ran.
The reproduction output is recorded in `circuit_reproduction.log`. Those
Python checks are not Lean proofs.

The source-verification script passed all **944** selected blobs. All **16**
validation-helper unit tests passed. These checks do not establish that the
focused snapshot is a complete buildable checkout or that any candidate Lean
file compiles.

Every one of the nine local `findings.json` before-block slices and before/after
line measurements was independently compared to the raw source and matched.
The ShortSystem degree proofs' common exact prefix is 224 lines. The current
base import-graph comparison was also reproduced: 37 existing modules versus
31 existing modules, plus the proposed new base; external closures were not
traversed. The future replay harness passed `bash -n`; its successful Lean path
was not run.

## Corrections and remaining acceptance gates

Minor draft inconsistencies were reported to the authors: the 31-variable
candidate was aligned to its two-line excerpt; the old predecessor-power
proof body has three lines, while its four-line span includes the `have`
statement; circuit measurements were updated after adding audit commands.
None was a change to a mathematical conclusion.

Before adoption: compile in a full pinned checkout, check exact elaborated
types and definition bridges, build all consumers and existing audits, compare
endpoint axiom sets, and benchmark with the same machine and cache policy.
No installation, new trust assumption, or upstream edit is authorized by this
proposal study.

## Final TeX/PDF review

The final reviewed PDF has **17 pages**, SHA-256
`a527fea1dc5efbeb32262510b4618e626a95a0d4f494e9c78020e1f7f7ede40b`.
The main PDF matched the immutable v3 review copy. All 74 `src` anchors refer
to existing files and valid source-line ranges. Its 99 external URI annotations
(78 distinct URLs) are pinned GitHub blob links; no unresolved `??` references
were extracted.

All-page rendered contact sheets and selected full-resolution pages were
visually inspected. The title no longer breaks the project name, inline Lean
commands preserve spaces, and the short before/after power proof is together
on page 11. Tables, mathematical symbols, code, margins, and page numbering
were legible without visible clipping or overlap. The final TeX log had no
overflow, missing-character, or undefined-reference warning; its only warning
was the harmless adjustment of a table float from `h` to `ht`.

Two source-description corrections were incorporated: the power-rewrite theorem
anchor is lines 86–131, and the deliberately corrupted circuit edge is described
as forward/non-earlier rather than self-referential. **No unresolved content or
presentation blocker was found.** Successful PDF compilation remains entirely
separate from the unavailable Lean compilation.
