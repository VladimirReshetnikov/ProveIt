# Formalization status and completion route

## Honest status

`BetaIPRAOutline.lean` is a detailed outline, not a completed Lean development. It intentionally contains 25 `sorry` markers. No compiled-Lean claim is made, and Lean was not available in the artifact-building container.

The human-readable report supplies the mathematical finite proofs. The outline records the exact remaining implementation obligations and the bridge into ProveIt's object theory.

## Reused checked infrastructure

The intended target is the current ProveIt repository:

- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean`
  - exposes `pra_iff_native` and the reverse bridge.
- `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Core/`
  - checked arithmetic for semirings, order, finite sums/products, powers, factorials, division, bounded search, pairing, and permutation.
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/analysis/gamma_ipra/`
  - a research packet with effective Gamma mathematics and a host-level Lean scaffold. Its analytic certificates and `Prf PRAAx` derivations are not complete and must not be treated as checked theorems.

## Recommended completion sequence

1. **RatCode and error arithmetic**
   - Implement rational/complex-rational codes as primitive-recursive functions.
   - Prove all operations preserve positive denominators.
   - Internalize the finite sum, product, and inverse error lemmas.

2. **Elementary functions**
   - Taylor evaluator for `exp`.
   - atanh-series evaluator for `log` on a positive interval.
   - positive-base powers `t^z`.
   - explicit derivative and remainder bounds.

3. **Finite calculus**
   - left Riemann sums and common refinement.
   - Lipschitz error.
   - finite fundamental theorem.
   - integration by parts and one-dimensional substitution with quadratic remainders.

4. **Complete Beta**
   - implement the cutoffs in the report exactly.
   - prove regularity and certificate independence.
   - prove symmetry and positivity.

5. **Direct identities**
   - Pascal.
   - balanced integration by parts.
   - coordinate recurrences.
   - natural/factorial/binomial values.
   - `h` derivative and PDE.
   - truncated-power convolution.

6. **Gamma bridge**
   - complete the Gamma packet's Euler approximant and integral contracts.
   - prove the explicit beta-to-gamma estimate.
   - prove the cleared beta-Gamma identity before guarded division.

7. **Derived analysis**
   - transformed integrals and Euler product.
   - parameter derivatives.
   - reflection/duplication/multiplication.
   - Gosper products.
   - asymptotics.

8. **Incomplete and multivariate Beta**
   - incomplete evaluator and endpoint modes.
   - polynomial values and binomial CDF.
   - hypergeometric finite-sum name.
   - multivariate list recursors and fixed-dimensional simplex reduction.

9. **Object-theory compilation**
   - reify each evaluator as a fixed primitive-recursive symbol.
   - encode every theorem as `Fm PTm`.
   - construct `Prf PRAAx` derivations using only quantifier-free induction on finite invariants.
   - audit with `#print axioms`.
   - apply `pra_iff_native` only at the final step.

## First three concrete object-theory targets

### Symmetry

For the primitive-recursive output code `BA`, prove:

```text
forall D a b p,
  Dom(D,a,b) ->
  close(BA(D,a,b,p+c), BA(swap(D),b,a,p+c), p).
```

Invariant: the first `r` samples of the original mesh equal the last `r` samples of the reversed mesh after replacing `t` by `1-t`.

### Pascal

```text
forall D a b p,
  Dom(D,a,b) ->
  close(
    BA(D,a,b,p+c),
    BA(shiftL(D),a+1,b,p+c) + BA(shiftR(D),a,b+1,p+c),
    p).
```

Invariant: the accumulated difference is exactly zero on the common mesh because `t + (1-t) = 1`.

### Cleared beta-Gamma

```text
forall D a b p,
  Dom(D,a,b) ->
  close(
    BA(D,a,b,p+c) * GA(a+b,p+c),
    GA(a,p+c) * GA(b,p+c),
    p).
```

This avoids division at the principal theorem boundary. The quotient form follows from a separate Gamma margin theorem.

## Proof checker boundary

A completed development must not introduce any axiom named “Beta correctness,” “integral completeness,” “analytic continuation,” or similar. Every such claim must be an explicit finite estimate. Host-level structures are allowed only as organizers of already proved fields.
