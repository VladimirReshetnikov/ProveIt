# The actual sharp pairing quartic in internal omega

The direct numeric checker uses the max-square pairing

```
pair(a,b) = if a<b then b*b+a else a*a+a+b.
```

It cannot be interpreted in an arbitrary ZFC model merely by applying an
external theorem about `Nat`. The model's omega may contain nonstandard
elements. The following checked modules work on the whole carrier
`ObjectOmegaSemiring.Natural H`, for arbitrary `H : ZFAxioms mem`.

* `ObjectNaturalDiscrete` proves zero/successor decomposition, the exact
  strict-order difference certificate, and `t*t=t ↔ t=0 ∨ t=1`.
* `ObjectNatPairing` interprets the sharp certificate directly on that
  carrier. Its three auxiliary naturals `t,s,m` satisfy
  `t*t=t`, `m+t*b=b+t*a`,
  `b+t*s+t*(s+1)=a+(s+1)` and `z=m*m+a+t*b`.
  The certificate exists exactly when `z=pair(a,b)`.
* `ObjectPairingSyntax` binds those equations to the **actual existing
  four residual rows** of `QuadraticNatPairing`, removes the empty register
  block by an explicit rename, and interprets their sum of squares over
  every internal natural assignment. The resulting stored expression is
  an integer polynomial of degree at most four. It has six coordinates:
  `a,z,b,t,s,m`.
* `ObjectPairingGraph` supplies the set-theory graph formula for exactly
  this quartic, including natural guards on every visible and auxiliary
  coordinate. It proves totality and functionality and obtains actual
  unconditional `BProv ZFCax_s []` derivations of their sealed sentences.
* `ObjectPairingSurjective` proves that every internal natural has a pair
  decomposition. Its induction predicate is an explicitly displayed
  set-theory formula, using `omega_ind` from the existing ZF development.
  The square-boundary transitions `(b-1,b) → (b,0)` and
  `(a,a) → (0,a+1)` are handled in the successor proof without using
  subtraction on the carrier. Surjectivity also has an unconditional
  derivation in the sealed ZFC calculus.
* `ObjectNaturalOrderedSemiring` supplies strict ordered multiplication.
  `ObjectPairingInjective` bounds each output between consecutive squares
  of the maximum input, obtaining injectivity without an external square
  root. `ObjectUnpair` therefore supplies an equivalence between pairs of
  internal naturals and internal naturals, exact quotation agreement with
  `Nat.unpair`, and an unconditional ZFC proof of inverse-graph uniqueness.

The graph does not silently substitute a semantic equality for the literal
quartic. `expression_zero_iff`, `exists_equationRel_iff` and `graphForm_spec`
are the explicit syntax-to-semantics links. Numeral compatibility is
`ObjectNatPairing.pair_cast`, using the same branch convention as `Nat.pair`.

The mathematical carrier operations may use choice to select the unique
values of definable arithmetic relations; no selected representation data
or extra axiom is inserted into the polynomial. Dedicated Lean checks
audit the dependency axioms. This is a local internal-arithmetic component,
not the complete consistency theorem: interpreting the full numeric checker,
its axiom context and its proof codes in internal omega remains required.
