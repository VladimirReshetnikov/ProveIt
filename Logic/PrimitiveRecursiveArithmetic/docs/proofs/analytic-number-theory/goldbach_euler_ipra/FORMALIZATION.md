# Lean formalization roadmap

## Status

This package contains a complete human proof and a detailed Lean roadmap.  The
file `lean/GoldbachEulerOutline.lean` deliberately contains `sorry`; it is not
reported as compiled or formally verified.  `lean/ConciseIPRABridge.lean`
contains the generic final transfer step against the current ConciseIPRA API.
The Python checks are exact finite audits, not a proof assistant verification.

## Pinned repository context

The ProveIt `main` branch inspected for this package was
`a85c645dd7213a1adbe35b0965d1e44e06c942be` (2026-11-15).
Relevant current files are:

- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`:
  `PR`, `PTm`, `PRAAx`, and quantifier-free induction.
- `.../NativeBiInterpretation.lean`: `native_iff_pra`, `pra_iff_native`, the
  round-trip theorems, and equiconsistency.
- `.../README.md`: the native scalar core and its relationship to iPRA.

## Recommended dependency order

### Stage A: ordinary Mathlib arithmetic

1. Define a bounded Boolean perfect-power test.
2. Prove the canonical decomposition theorem:
   every `n >= 2` has a unique `n = r^e` with `r` root-free and `e >= 1`.
3. Prove the two finite geometric identities and the telescoping identity.
4. Define the rational partial sum indexed by values `p`, so duplicates are
   omitted definitionally.
5. Prove `partial_le_one` by the finite truncation contradiction.
6. Prove the lower rectangle estimate and the modulus
   `B(k) = 2^(2*(k+1)^2)`.
7. Combine with monotonicity.

This layer isolates the mathematical combinatorics from syntax coding.

### Stage B: primitive-recursive implementations

Give explicit `PR` codes (or a reusable compiler from a proved primitive-
recursive DSL) for:

- addition, multiplication, truncated subtraction, order and Boolean choice;
- exponentiation and bounded sums/products;
- bounded divisibility, primality and prime valuation;
- finite gcd fold and the canonical root/exponent functions;
- the perfect-power characteristic function;
- rational-pair accumulation `Num(N), Den(N)`;
- the modulus `B`.

All searches are bounded by an input such as `n`, and all loops are primitive
recursions.  No minimization operator is needed.

### Stage C: arithmetic correctness in `PRAAx`

Prove defining/correctness formulas by quantifier-free induction.  The main
closed formula can avoid quotient types and rational subtraction:

```
forall k N,
  B(k) <= N ->
    Num(N) <= Den(N) /\
    (2^k - 1) * Den(N) <= 2^k * Num(N).
```

The first inequality says `S_N <= 1`.  The second says
`S_N >= 1 - 2^-k`.  Every symbol denotes a primitive-recursive natural-number
function, so the formula lies directly in the `PRAAx` language.

Suggested theorem name:

```lean
theorem goldbachEuler_iPRA :
  ([] : List (Fm PTm 0)) ⊢[PRAAx] goldbachEulerFormula
```

### Stage D: transfer to ConciseIPRA

Use the already formalized theorem:

```lean
(pra_iff_native (Γ := []) (φ := goldbachEulerFormula)).mp
  goldbachEuler_iPRA
```

This yields a derivation of `NFm.ofPRA goldbachEulerFormula` in the native
scalar calculus.  The bridge itself is in `lean/ConciseIPRABridge.lean`.

## Principal proof obligations

1. **Factorization correctness.** A trial-division or valuation implementation
   returns the exact finite prime-exponent vector.
2. **Canonical uniqueness.** The gcd of the positive valuations is the unique
   exponent whose root is not a perfect power.
3. **Finite reindexing.** `(r,i) |-> r^i` is injective on root-free bases.
4. **Upper bound.** Formalize the rational positive-gap argument with an
   explicit truncation index `I = N*Den(N)+1`.
5. **Lower bound.** Reindex the finite rectangle onto all `2 <= m <= R` and
   close the two error estimates at `R=2^(k+1)`, `T=2*k+2`.
6. **Coding fidelity.** Relate the natural pair `(Num,Den)` to the Mathlib
   rational partial sum, or prove the pair theorem directly and use Mathlib
   only as an optional semantic layer.

## Constructivity checklist

- Perfect-power membership is a bounded decision procedure.
- The canonical root is computed from finite factorization data.
- Every sum in the internal proof is finite.
- The apparent reductio in the upper bound is a case split on a decidable
  natural/rational inequality.
- There is no real-number completeness, countable choice, Markov principle,
  classical prime selection, or permutation of a completed infinite series.
