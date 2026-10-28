# Actual C222 source quantifier contexts — author receipt

Author: `circuit_reduction`. Status: frozen; final private main/check replay
PASS. This is an author verification record, not independent peer review.

## Frozen sources and outputs

| Item | SHA256 |
|---|---|
| `ValidatorSourceQuantifierContext222.lean` (220 lines) | `97da604536ee7bc28fed6e4d06431362255cec03888b4cbc8b26ee1218ba398b` |
| `ValidatorSourceQuantifierContext222Checks.lean` (112 lines) | `b3584f73871f06f32ed10ade5fd568fce30e592515557e7f4e834d4ddc54eb75` |
| Fresh main object | `f187f3eb89782765795015866faece406faa9f2fbdeac5f19473a5b5c50e101c` |
| Fresh checks object | `76956637d34bf2513821196d9eacf1a1f7f84cb5c9df81ed6da5a89b185f1039` |
| `validator-source-quantifier-context222-cache.json` | `1329123bbde386605bf0d5168cf97905b82d9120869303cbc5fa420e65f023d9` |
| `validator-source-quantifier-context222-replay.json` | `1898017ecd78b4de060a0f0c466e8c75a77c7a4bfe37a12ffec4850961051d38` |
| `validator-source-quantifier-context222-author-replay/FILES.json` (43 files) | `f32fac0b86b770377fbbf23192b2d8722e04951110a180c56b8f5a9316f1c1b3` |

Sources are in `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA`. The private
provider is `/tmp/validator-source-quantifier-context222-author-up2sx7d8/lib`.
The frozen replay summary contains the exact absolute source, compiler,
command, object, timing and log paths.

## Proved scope

`cProv_gen_context` proves the numeric implication
`wal i (imps G g) → imps G (wal i g)` for arbitrary internal contexts with
an actual `Vac i` certificate for every internal indexed member. Its explicit
Π₂ invariant is discharged by actual IΣ₂ order induction. `der_gen` applies
this implication to an actual C222 theorem generalization; it is not an
unrestricted GEN-under-hypotheses rule.

`negEnc_vacuous` and its member form derive every negative source-hypothesis
vacuity from actual source typing, `StreamFree`, `fresh_resources`, and
`encode_formula_vac`. The separate `cProv_gen_source_context` directly uses
Σ₁ vector induction: its typed-list guard is Δ₁ and its conclusion is Σ₁.
The theorem still retains IΣ₂ for the imported uniform encoded vacuity proof.
No extra free-environment length, label injectivity, parity, or freshness of
the conclusion is assumed.

The ALL endpoints use the literal extended environment `eigen F s∷F`, source
`free p`, actual `shiftList`, `tail_cons` and `all_opened_equiv`. The EXS
endpoint applies the existing `ex_term_imp` through `Der` MP for an arbitrary
internal context without any context-vacuity premise. `seqC_cons_iff_der`
is an IΣ₁ finite classical C222 deduction; it uses numeric negation rather
than identifying source NNF negation with it. `seqC_all`, `seqC_exs` and the
two witness theorems expose the actual source sequent rules and numeric
`ArithmeticHistory222.value` proofs.

Focused checks cover empty and duplicate contexts, arbitrary internal member
indices, two successive source shifts, nested ALL/EXS binders, original stream
zero under its exact safety premise, fallback label 1, repeated stored zero
labels, arbitrary term instances, and actual internal checker witnesses.
All 23 axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`.
No `sorry`, `native_decide`, new axiom or model-standardness assumption was added.

## Read, build and provenance scope

The author fully read the new main/checks and preparation/build/freeze
drivers before executing them, including each later small edit. The selected
closure contains 162 current-source cached modules, 117 Foundation modules,
513 object artifacts and 40 explicit package/toolchain boundaries including
Init. Nine selected actual C222 prerequisite leaves use accepted root-fresh
providers. The cache records exact parent receipts and inherited provenance.
No dependency or Foundation module was rebuilt. The two new outputs are
regular files, never output symlinks; accepted objects were not overwritten.

The planning audit retained 743 observations. The final pair recorded 2,198
pre/post input and source observations. Every selected source, object
companion, explicit boundary, compiler, manifest and parent receipt matched.
`public meta import Aesop` is included. The read-only planning duplicate-import
and explicit-Init metadata preflights remain preserved separately from Lean
development; no historical accepted inventory was rewritten.

Both final commands used Lean 4.32.0, `-M6000 -j1 -DElab.async=false`,
`LEAN_NUM_THREADS=1`, the pinned private/package path, and a 512 MiB reserve
guard. Final wall times were 10.765 s main and 3.083 s checks. The main log is
empty, and the checks contain only the 23 standard axiom reports.

One main development attempt failed at parsing because a doc comment preceded
`omit`; moving `omit` before that comment fixed it without changing any
theorem. The following main/check pair passed. The planned two-shift check
then replaced a redundant wrapper, and a final complete pair passed. All
attempt sources, logs, commands, timings, driver snapshots, pins and previous
successful objects are preserved in the frozen 43-file bundle.

This packet does not interpret arbitrary source derivations, discharge source
axiom images or the internal tagged-seed obligation, compile proofwords, assert
semantic seed validity, or prove an HA endpoint. R2Quant was a source-only
guide; no R2 proof module is imported. No shared source, umbrella, display,
dependency output or Git state was changed by this work.
