# 1980 formalization audit and agreed scope

Audit date: 2026-09-14. The initial source checkpoint was `c32e616`.
This document records the project owner's scope decisions and compares
the retained statements with their actual Lean contracts.

## Completion criterion

The retained numbered scope is **Theorems 1–3 and the abridged Theorem 4,
containing the proved universal pair `(58,4)`**. The owner explicitly
excluded the other reported table values given without proofs, for now.
Theorem 5 is intentionally excluded because its statement is vague and
imprecise. Its existing RE-set representation theorem is retained as
supporting material, not as evidence for a numerical operation count.

The owner also replaced the previous historical/elementary axiom allowances
with **no new axioms**. The retained proofs introduce no project
mathematical axioms. Reuse of verified Mathlib and project results remains
permitted, with their transitive dependencies checked.

The retained numbered results are covered by the existing proofs. The
single-parameter indexing remark has an additional wrapper in this
milestone; its final validation receipt is recorded below.

## Statement crosswalk

| Retained statement | Lean evidence | Exact boundary |
|---|---|---|
| Theorem 1: exponential/binomial system with twelve positive unknowns | `Jones1982.Thm1`, `theorem_1`, `Theorem1Solvable58`, `rePred_theorem1_system` | `ν=58`, hence exponent `5^60`; both directions, all twelve witnesses positive |
| Theorem 2: one central-binomial test and fourteen positive unknowns | `Jones1982.Thm2`, `theorem_2`, `Theorem2Solvable58`, `rePred_theorem2_system` | Both directions; exact packing polynomial and all fourteen positive witnesses |
| Theorem 3: eighteen polynomial equations and twenty-eight positive unknowns | `Jones1982.Thm3`, `theorem_3`, `Theorem3Solvable58`, `rePred_theorem3_system` | Both directions; all twenty-eight witnesses positive; signed expressions retain their integer interpretation |
| One positive coding triple works for all three systems | `Jones1982.rePred_printed_systems` | The triple is chosen once for the RE set, before quantifying over the positive input |
| Abridged Theorem 4: universal pair `(58,4)` | `Jones1982.universal_quartic58` | One joint polynomial is fixed before choosing the RE set; specialized degree is at most four in the input and 58 witnesses |
| Positive-triple code injectivity | `Jones1980.indexCode_injective` | Injectivity of `((z*u*y)^2+u)^2+y` for positive `z,u,y` |
| Adjoining that code equation preserves all three representations | `Jones1980.singleParameterSolvable_indexCode_iff`, `rePred_single_parameter_systems` | One fixed positive code represents the set through all three systems; adds three positive witnesses |

The shared system definitions and proofs are in
[Theorem1.lean](Diophantine/Paper1982/Theorem1.lean),
[Theorem2.lean](Diophantine/Paper1982/Theorem2.lean),
[Theorem3Defs.lean](Diophantine/Paper1982/Theorem3Defs.lean), and
[Theorem3.lean](Diophantine/Paper1982/Theorem3.lean).
The uniform RE-set wrappers are in
[RecursivelyEnumerableSystems.lean](Diophantine/Paper1982/RecursivelyEnumerableSystems.lean).

## Quantifiers and domains

The input hypothesis is `0 < x`. These theorems do not assert behavior
of the displayed systems at input zero. The fixed-code versions require
an admissible `Index 58 P z u y`, a normalized polynomial, and its degree
bound. This matches the corrected article's editorial code convention;
it does not assign the same interpretation to unrelated positive triples.

The universal result is stronger than choosing an unrelated quartic for
each RE set: `universal_quartic58` first supplies a single polynomial in
`Fin 3 ⊕ Fin 59`, then chooses three positive index parameters for the
represented set. The degree bound applies after specializing those three
parameters. It counts the input and the 58 witnesses. This is the degree
convention stated in the full 1982 derivation.

The public quartic uses nonnegative natural witnesses. The proved shift
equivalence `ShortQuadratic.exists_shifted_iff` connects them to the
58 positive quadratic-system witnesses. The first three printed systems
already quantify strictly positive witnesses directly.

The single-parameter reduction in
[SingleParameter.lean](Diophantine/Paper1980/SingleParameter.lean) adjoins
`indexCode z u y = v` and quantifies `z,u,y`. Injectivity forces every
solution at the code of a fixed positive triple to recover that same
triple. The resulting witness counts are therefore 15, 17, and 31,
respectively. This does not preserve the three-parameter witness counts,
and it does not state a decoder or a computable-enumeration theorem.

## Explicit exclusions and broader statements

The following reported Theorem 4 entries are outside the current abridged
completion criterion and are not being relabeled as proved:

`(38,8)`, `(32,12)`, `(29,16)`, `(28,20)`, `(26,24)`, `(25,28)`,
`(24,36)`, `(21,96)`, `(19,2668)`, `(14,≈2.0·10^5)`,
`(13,≈6.6·10^43)`, `(12,≈1.3·10^44)`, `(11,≈4.6·10^44)`,
`(10,≈8.6·10^44)`, and `(9,D₉)`.

The rounded scientific-notation entries are not exact integer bounds.
The expression `D₉=47216*5^58+9728` is recorded in the corrected source;
checking its numerical size alone would not prove the corresponding
nine-variable construction.

Theorem 5's operation convention, optimized certificates, and proof-system
encoding are not completion blockers under the owner's exclusion. The
existing [Theorem5.lean](Diophantine/Paper1980/Theorem5.lean) proves an
RE-set-to-positive-solution equivalence. It explicitly does not formalize
the operation-count assertion. Written proofs and Python certificate
checks remain separately labeled evidence. Other agents' unpublished
operation-certificate drafts are not part of this source checkpoint.

This audit does not claim separate formal theorems for every introductory
historical assertion, for an effective one-parameter decoder, or for the
literal route that adds thirty auxiliaries directly to the original
28-variable system. The `(58,4)` endpoint is proved through the full §5
construction. Completion claims should name the agreed retained scope.

## Validation

The two new modules passed their focused Lake targets. One consolidated
`lake build` then completed successfully with **3581 jobs**, including the
136 project modules and the vendored proof library. The new modules emit
no warnings; existing linter and deprecation warnings elsewhere remain.

The expanded [Paper1980Axioms.lean](checks/Paper1980Axioms.lean) audit
passed all **15** transitive dependency checks, including the new
single-parameter wrapper. Every reported dependency belongs to `propext`,
`Classical.choice`, or `Quot.sound`; no project mathematical axiom or
`sorryAx` occurs. The supporting declaration named `theorem_5` is audited
without counting the excluded printed Theorem 5 as formalized.

The separate shared Putnam construction in
[DiophantineFunctionPolynomial.lean](Diophantine/Common/DiophantineFunctionPolynomial.lean)
also passed its
[dependency audit](checks/DiophantineFunctionPolynomialAxioms.lean).
It handles a zero function output and an empty original witness family,
and adds one output witness without a numerical bound on the final family.
Its existence statement is useful for 1976 Theorem 4; this helper alone
does not establish that theorem's prime-graph premise or its 14-witness
refinement.

The reproducible commands, from the ProveIt root, are:

```text
lake build Diophantine
lake env lean Computability/HilbertTenthProblem/Lean/checks/Paper1980Axioms.lean
lake env lean Computability/HilbertTenthProblem/Lean/checks/DiophantineFunctionPolynomialAxioms.lean
```

A nested-comment and string-aware scan of all **150 library Lean files**
found no code token `sorry`, `admit`, `axiom`, or `native_decide`. Each
project module occurs exactly once in the umbrella. The publication
receipt in [STATUS.md](STATUS.md) records source preservation through
the final upstream merge. No new article error was found in this audit.
