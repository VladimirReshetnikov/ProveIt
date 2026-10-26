# Independent review of four proof-simplification patches

## Review scope and conclusion

Source pin: `1e2a853935a6155cbcf2aa199aaca51946c4fff9` in `VladimirReshetnikov/ProveIt`.

This is an independent source and mathematical review of the four exact patches listed below. All four preserve the existing public theorem statements and computational definitions. No new mathematical premise has been added to an existing theorem; no result is weakened from the original contract. The changes remove repeated reasoning or replace stronger-than-needed proof machinery with already available structure. Lean compilation and kernel/axiom checks are separate evidence produced by the build owner; this review does not represent an unrun build as successful.

The public changes are one new shared theorem, replacement proof terms, and the order of two foundational imports. The exact-witness factorization has a modest net source reduction; its principal benefit is one authoritative proof of the construction's properties. Generic canonical-witness factoring and generic import reordering were already suggested before and are not claimed as novel.

## 1. Canonical order before successor discreteness

Patch: `canonical-order.patch`.

The replacement of `ObjectNaturalOrderedSemiring.mul_strict_left` is mathematically valid on the whole internal `Natural H`, including a possibly nonstandard model. It does not reduce the argument to external natural numbers.

The original proof wrote both a positive factor and a positive additive gap as successors. The replacement uses the canonical additive order to obtain `c = b + d` from `b < c`. Strict inequality implies `d ≠ 0`. Together with `a > 0`, the existing `NoZeroDivisors` instance gives `a * d ≠ 0`. In canonical order this means `0 < a * d`, so additive strictness gives

    a * b < a * b + a * d = a * c.

This uses exactly the original hypotheses. The imported canonical-order lemmas do not assume a successor representation. The same `IsStrictOrderedRing (Natural H)` instance is then constructed as before. `ObjectNaturalDiscrete.mul_self_eq_self_iff` is replaced by `IsIdempotentElem.iff_eq_zero_or_one`; under the resulting multiplicative cancellation structure, `x*x=x` and `x≠0` imply `x=1`. Its displayed type, model parameter, and universes remain unchanged. The other discrete-natural theorems remain unchanged.

The import direction is changed from `ResidualSquares → Discrete → OrderedSemiring` to `ResidualSquares → OrderedSemiring → Discrete`. This is acyclic: the original Discrete module already depended on ResidualSquares. The change does stop OrderedSemiring from re-exporting all Discrete declarations transitively. Every maintained direct client was checked: the umbrella imports Discrete explicitly, and ObjectPairingInjective imports ObjectPairingSurjective → ObjectPairingGraph → ObjectPairingSyntax → ObjectNatPairing → ObjectNaturalDiscrete. Therefore these maintained clients retain their necessary declarations. An external client importing only OrderedSemiring could need an explicit Discrete import if it uses those discrete facts.

Novelty qualification: round c, `report.tex` lines 854-867, already noticed the import cycle and suggested weaker assumptions or module reordering; round k also contains a broad natural-difference/order-embedding direction. The new contribution is this concrete proof that multiplication strictness and Boolean idempotence need no successor discreteness, together with its actual client simplification. Reordering itself is not a new idea.

## 2. Formula-code 44 from outer-constructor minima

Patch: `formula-minimum.patch`.

The proof uses the repository's exact square pairing `Nat.pair`, not a replacement encoding. The existing strict monotonicity lemmas in each coordinate give a private coordinatewise monotonicity helper. The same property then holds for `forkCode` after its fixed offsets. `atomCode n ≥ 1` supplies the lower bounds for variable indices and tags.

The concrete constructor certificates are sound:

- `forkCode 1 1 = 8`.
- `forkCode 1 (forkCode 1 1) = 67`, so every variable-code constructor exceeds 44.
- `atomCode 3 = 10` and `forkCode (atomCode 3) 0 = 133`, so every connective with tag at least 3 exceeds 44, regardless of its natural-valued payload.
- The bottom formula has code 44, giving the actual global minimum.

Thus the formula-code lower bound depends only on the outer constructor. The replacement `cases f` needs no induction hypothesis about subformula codes. It removes separate nonlinear lower-bound arguments without altering `formCode`, `atomCode`, `forkCode`, `variableCode`, the closure program, the quadratic program, the guarding threshold, or any node-count formula. In particular, `formCode_ge` keeps precisely the statement `44 ≤ formCode f`.

The concrete inequalities are discharged by `decide`; no unchecked numeric assertion or representation change is introduced. Exact elaboration of the monotonicity lemma calls is a compiler-validation responsibility, not inferred from source review alone.

Novelty qualification: the old AnnotatedClosure recommendation in round e concerns typed/numeric iterator fusion, not this minimum-code proof. General coefficient bounds and certificate simplification remain prior work; the retained recommendation is the exact outer-constructor argument above.

## 3. Helical rows and seam status from period one

Patch: `helical-rigidity.patch`.

For the helix, fix `x` and `t` and define the integer-indexed function

    f(s) = T (x + w*s) (t-s).

The original hypothesis `T (y+w) (u-1) = T y u` says exactly that `f(s+1)=f(s)`. `Function.Periodic.int_mul_eq` gives `f(t)=f(0)`, and symmetry yields `T x t = T (x+w*t) 0`. This handles arbitrary target type and every signed `x`, `w`, and `t`, including negative width or time and width zero. No positivity, nonzero-width, coprimality, or additional periodicity hypothesis has been introduced.

For seam columns, the existing successor equivalence becomes period one for the Prop-valued function `SeamAt T x`, via `propext`. The same integer-period theorem yields equivalence with time zero. The period is derived from the already available adjacency equivalence, not assumed. The statement and the hypotheses `hAllowed` and `hTime` are unchanged. Since the new proof mentions `propext` explicitly, axiom provenance should be checked in the actual compiled old/new constants rather than presumed from the source diff. Proposition extensionality is a standard Lean axiom, but the exact comparison belongs in the build evidence.

Novelty qualification: pending incoming work recommends centered integer induction for interval propagation from a known interior point. Here the operation is a global orbit-invariance/period-one argument, covering a helix after reparameterization and a global seam predicate. It is not a renamed version of the interval induction proposal. Shared cyclic geometry and finite predecessor-invariance proposals remain excluded as general directions.

## 4. Exact CycleBand quotient properties before existential erasure

Patch: `exact-band-witness.patch`.

The new `WangTiles942CycleBand.band_quotient_properties` proves MarkedWord and all band-binding equalities for the explicit quotient word already used by `WangTiles942BandMarker.canonicalWord`. It pays for `extension_properties`, `quotientWord_marked`, and the composition of `quotientWord_binding` with `extend_on_band` once. The old existential `marked_word_of_halt` theorem packages this exact witness. The old `canonicalWord_properties` theorem reuses its matching and binding conclusions and adds its existing separate marker-uniqueness result.

The actual patch leaves the `canonicalWord` definition and its namespace unchanged. It also leaves `band`, `extend`, and `quotientWord` unchanged. The explicit term in the new helper matches that definition. No arbitrary witness is silently substituted for the canonical word, and marker uniqueness is not asserted for every marked word.

The helper retains the actual machine-halting premise, independent left and right margins and height, the half-open interval `[-L, R)`, and all integer times. Its `NeZero H`, `NeZero ((L+R)*H)`, and positive-width inputs are already derived from the original margin/height bounds at the existential endpoint. The existing public theorem therefore gains no premise. No trace-boundary condition, clean-run condition, or extra uniqueness condition has been introduced.

The net reduction is only four physical lines after the shared helper is counted. The benefit is the elimination of a duplicated construction proof and an exact-witness interface that both existing consumers can share. Any claim of a much larger net source reduction would be misleading.

Novelty qualification: earlier rounds propose coherent digit/window witnesses and same-word selector transport. Those broad ideas are not repeated as new recommendations. The new recommendation is the exact duplicated CycleBand/BandMarker quotient construction, with its particular marked-word and pointwise band-binding contract.

## Patch identity and size accounting

The hashes below identify the exact reviewed patch bytes. All four now use repository-root paths `a/Computability/...` and `b/Computability/...`, suitable for a common `-p1` application from the repository root. The counts include blank and comment lines; they are source deltas, not a theorem-count or runtime measurement.

| Patch | Added lines | Removed lines | Net lines | SHA-256 |
|---|---:|---:|---:|---|
| canonical-order.patch | 15 | 28 | -13 | b8e6bdd58be35601dc1a5c29b24a0e1f9dd139d76ae574140059d42e661f5566 |
| formula-minimum.patch | 28 | 47 | -19 | 36f0e0491f85473c656921def16666314afdc7c513328ccaf5b567d385123fd0 |
| helical-rigidity.patch | 9 | 24 | -15 | 0dda26320e80cfa07470e4d56e414bc619ac3ddcf473ee32b955139dda713873 |
| exact-band-witness.patch | 34 | 38 | -4 | 27c41782ca67abe5835c6c7b14252c223fc812b434be6c64ef4e02433d7409c2 |

Total: 86 added, 137 removed, net reduction 51 physical source lines across seven modules. This includes the new helper and updated documentation.

## Validation handoff

The source review finds no changed computational definition, weakened public statement, additional public premise, or improper substitution of an external-standard-natural argument for internal arbitrary-model reasoning. Remaining validation is concrete: compile the affected modules and relevant downstream clients against the pinned Lean/mathlib setup, inspect theorem axiom lists where requested, and package the exact tested patches. The build owner is collecting that evidence separately. No performance claim is made here.
