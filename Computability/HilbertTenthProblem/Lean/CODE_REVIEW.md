# Existing-code simplification after MRDP

The project owner paused further formalization of the six papers on
2026-09-14. This review preserves the existing mathematical statements
while shortening proofs, extracting shared lemmas, and correcting comments.
The updated brief also calls for useful generalizations and stronger results;
existing public interfaces remain available to their callers.
MRDP remains available in both directions; the outstanding article work
and the agreed 1980 exclusions remain recorded in [STATUS.md](STATUS.md).

## First cleanup batch

| Area | Change and reason |
|---|---|
| Integer square tests | [PositiveSquareTest.lean](Diophantine/Common/PositiveSquareTest.lean) proves that `0 ≤ a` and `0 < a * (1 - b²)` force the integer residual `b` to vanish. The function-polynomial construction and four 1976 prime-polynomial constructions share this fact. |
| Relation combining | [RelationCombiningArithmetic.lean](Diophantine/Common/RelationCombiningArithmetic.lean) specializes the existing unsquared factor lemmas to `B²` and `C²`. Their sign hypotheses follow from squaring, and integer power cancellation recovers `B ∣ C`. This removes a duplicate necessity/sufficiency argument while retaining signed parameters. |
| Halted machine runs | [Machine.lean](Diophantine/Paper1974/Machine.lean) supplies `run_eq_of_halted` for two halted runs from the same initial configuration. Score uniqueness, machine composition, and the comparisons with `SH` and `SC` reuse it. |
| Finite Gödel coding | [Godel.lean](Diophantine/Paper1978/Godel.lean) obtains `exists_S_eq` from the stronger `exists_S_eq'` with both lower bounds zero. The stronger result already proves the required Chinese remainder construction. |
| Existing interfaces | [RecursivelyEnumerableDioph.lean](Diophantine/Common/RecursivelyEnumerableDioph.lean) uses primitive-recursive composition directly; [PellInt.lean](Diophantine/Common/PellInt.lean) uses `Nat.twoStepInduction`; [Identities.lean](Diophantine/Paper1984/Identities.lean) uses `Nat.le_of_testBit`. |
| Comments | The Pell shift comment now states its actual identity and the reason for `2 ≤ m`. The binomial-digit comment retains the required `k ≤ n` hypothesis. The [MRDP module](Diophantine/MRDP.lean) overview explains both directions. |

The square-test helper permits a zero multiplier in its initial hypothesis;
strict positivity of the product excludes that case. The halted-run helper
works from arbitrary initial configurations, including zero-state machines.
These helpers generalize the former positive-multiplier private lemma and
the repeated arguments specialized to individual machine inputs.
The stronger `mul_one_sub_sq_pos_iff` gives the complete criterion:
for `0 ≤ a`, positivity of `a * (1 - b²)` is equivalent to `0 < a ∧ b = 0`.
No new hypothesis is imposed on their existing callers. The polynomial
definitions, variable assignments, degree bounds, and prime-representation
statements are unchanged.
The batch removes a net 91 library lines, counting the new helpers and
expanded comments; documentation and the audit driver are counted separately.

## Review and validation

The review compares this cleanup with published baseline `37972c7`.
A comment-aware, whitespace-normalized source comparison checks all
**185 existing public theorem/lemma statement headers** in the fourteen
edited mathematical modules, including declarations with inline attributes.
An independent source review checks the shared arguments and their clients,
including namespaces, assumptions, definitions, and dependency direction.
Header comparison is a textual compatibility check; kernel compilation
separately verifies that the new proofs elaborate.

## Polynomial helpers and upstream integration

The second batch extracts four general facts and applies them to the existing
polynomial constructions:

| Helper | Generality and existing clients |
|---|---|
| [`exists_eval_rename_option_iff`](Diophantine/Common/PolynomialRenaming.lean) | Renaming variables preserves a polynomial equation with a distinguished input. Witness values may inhabit any type, the map into a commutative semiring need not be injective, and the target value is arbitrary. The enumeration quartic and the 58-witness quartic share this argument. |
| [`eval_rename_zeroWitnesses`](Diophantine/Common/PolynomialRenaming.lean) | Setting all witnesses to zero commutes with renaming. Both quartic normalization proofs use this identity. |
| [`totalDegree_sum_pow_le`](Diophantine/Common/PolynomialDegree.lean) | A finite sum of `k`th powers of polynomials of degree at most `d` has degree at most `k * d`. Three sum-of-squares bounds specialize it to `k = d = 2`. The helper also permits empty families, exponent zero, and trivial coefficient semirings. |
| [`signFlip_signed_X`](Diophantine/Common/RelationCombiningPolynomial.lean) | Flipping a variable toggles its chosen sign exactly at the matching index, for arbitrary variable types and commutative rings. The original and refined relation-combining factors share this fact. It has no global simp attribute. |

The four 1982 clients retain their polynomial definitions, residual ordering,
coordinate equivalences, witness counts, and degree bounds. Comments now point
to the existing bridge modules and distinguish arbitrary integer assignments
from the positive witnesses used by the Pell-system equivalence.

The concurrent upstream integration also required correcting two existing
proofs in `Paper1980/PellRelaxed.lean`: the norm equation needs a negative
multiplier in `pow_x_y`, and the zero-index congruence case needs explicit
reduction of `Nat.ModEq`. Their statements are unchanged. The umbrella now
imports the incoming `System93`, `Bootstrap93`, and `PellRelaxed` modules.
The [window module](Diophantine/Paper1980/Window93.lean) overview no longer
claims a `paired_zero` endpoint: the file proves `window_digits` and
`window_nonneg_of_small`, under their explicit decomposition and size hypotheses.
The digit-mask overview now includes `S₂ < B^(2L)`, since the mask constrains
only those low positions. The relaxed-Pell overview states the positivity
assumptions and distinguishes its auxiliary data from the other premises of
`doubled_index_core`. The system-level Pell overview explicitly includes the
positive-input assumption inherited from `Pos93`; the MRDP theorem includes zero.
The bit-mask overview states `0 < m`, as required for digitwise equivalence
in radix `2^m`; radix one would discard all bits.

The second comparison checks **74 existing public theorem/lemma headers**
in seven modules, including the two repaired recursive Pell proofs. Together
with the first batch, this checks **259 headers in 21 modules**. Recursive
equation clauses are treated as proof bodies, just like `:= by` proofs.
Independent source review complements these textual checks.

## Build and axiom checks

Focused module and family checks resolve elaboration errors before the final
consolidated umbrella build. Reproduce the kernel and transitive axiom checks from
the ProveIt root:

```text
lake build Diophantine
lake env lean Computability/HilbertTenthProblem/Lean/checks/CodeCleanupAxioms.lean
lake env lean Computability/HilbertTenthProblem/Lean/checks/MRDPAxioms.lean
lake env lean Computability/HilbertTenthProblem/Lean/checks/PolynomialCleanupAxioms.lean
```

For the shared Windows host, set `$env:LEAN_NUM_THREADS = '1'` before
starting Lake. This configures its regular runtime worker budget and
reduces build fan-out. The initial umbrella run had library-object load
failures in nine modules while free physical memory fell below 500 MB; its
failure log is retained separately from the recovery run. No library objects
or mathematical source were replaced to address those load failures.

The [cleanup audit](checks/CodeCleanupAxioms.lean) checks 25 helpers and public
results transitively. The [MRDP audit](checks/MRDPAxioms.lean) repeats all
11 checks for the computational and arithmetic proof chain. The
[polynomial audit](checks/PolynomialCleanupAxioms.lean) adds 21 checks for the
new helpers, their clients, the repaired Pell proofs, and six incoming support
endpoints. The dated
[validation receipt](STATUS.md) records the observed build result, source
inventory, and axiom dependencies.

Further article formalization remains paused. These cleanup batches preserve
the operation-certificate schedules and the agreed article proof boundaries.
