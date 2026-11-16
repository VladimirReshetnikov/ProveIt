/-!
# Object-language targets for ProveIt

This is an intentionally uncompiled integration blueprint.  Replace the module
names below by the exact imports chosen in the target branch and then implement
each displayed `Target` as a theorem of type

    [] ⊢[PRAAx] phi

in `LeanProofs.ConciseIPRA` / `IPRADerivations`.

Pinned repository commit used by the report:
`2a7a1cc230762eaa57df921e944a5443afeb0519`.

Relevant existing definitions:

* `ConciseIPRA.PR`: primitive recursive symbols (`zero`, `succ`, `proj`,
  `comp`, `prec`);
* `ConciseIPRA.PTm`: object terms;
* `ConciseIPRA.PRAAx`: defining equations, successor axioms, qf induction;
* `ConciseIPRA.PRA.qfInd`: the induction constructor;
* `pra_iff_native`: transfer to the native scalar core;
* the `gamma_ipra` packet and the checked arithmetic library in
  `Logic/PrimitiveRecursiveArithmetic/Derivations`.

## Suggested module graph

```
BarnesG/FiniteProducts
  -> BarnesG/IntegerValues
  -> BarnesG/RationalBalls
  -> BarnesG/CanonicalTail
  -> BarnesG/ProductEvaluator
  -> BarnesG/FunctionalEquation
  -> BarnesG/Taylor
  -> BarnesG/Reflection
  -> BarnesG/Multiplication
  -> BarnesG/Asymptotic
  -> BarnesG/SpecialValues
  -> BarnesG/Checks/Axioms
```

## Representative exact targets

Let `fac`, `gPos`, `hyper`, and `facBlock` be fixed `PR` symbols with their
recursion equations.

1. Integer recurrence:

```
Target GSucc := forall n,
  gPos(S n) = fac(n) * gPos(n).
```

This is a defining equation.

2. Hyperfactorial identity:

```
Target GHyper := forall n,
  gPos(n) * hyper(n) = pow(fac(n),n).
```

Use qf induction; normalize the successor step with the ring/power library.

3. Finite Gamma product, division cleared:

```
Target GammaBlock := forall k n,
  gPos(k+n) = gPos(k) * facBlock(k,n).
```

4. Canonical tail, all denominators cleared.  For fixed natural radius `R`:

```
Target CanonicalTail(R) := forall N p,
  2*R <= N /\ 2*R^3*2^(p+2) <= 3*N ->
  LogTailBound(R,N,p).
```

`LogTailBound` is a code for the dyadic ball statement produced by summing the
geometric majorants of the factors.  Its checker uses only bounded sums,
products, order and powers.

5. Functional equation at requested precision:

```
Target GFunctional(codeZ,p) :=
  Safe(codeZ,p) ->
  BallEq(G(codeZ+1,p+guard), Gamma(codeZ,p+guard)*G(codeZ,p+guard), p).
```

The proof combines the finite-product cancellation identity, the Gamma Gauss
limit contract, harmonic-minus-log and Stirling certificates, and a single
error-budget telescope.

6. Reflection, multiplication, asymptotic and special values are analogous
`BallEq` or `BallSubset` targets.  Quotient forms are never primary targets:
first prove a cross-multiplied identity, then invoke an apartness certificate.

## Native transfer

After each ordinary theorem `h : [] ⊢[PRAAx] phi` is built, apply the repository
bridge `pra_iff_native` (or its current namespaced equivalent) to obtain the
corresponding derivation in the concise native calculus.  A host-Lean theorem
about `Nat`, `Rat`, or `Complex` is not a substitute for this final step.
-/
