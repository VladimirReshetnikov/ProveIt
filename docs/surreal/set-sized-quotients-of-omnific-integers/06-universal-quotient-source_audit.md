# Source, novelty, and proof audit

Article: **The Universal Set-Sized Quotient of the Omnific Integers**  
Research snapshot: 22 September 2026.

## 1. Repository scope

Repository: https://github.com/VladimirReshetnikov/Surreal  
Pinned commit: `a5c2a97df4b545dfe7f4cb8c11e4efed83101f6e`.

The GitHub connector was used to inspect repository metadata, the root
README, the report catalogue, and selected report descriptions. The three
README sources cited by the article were checked against the pinned commit:

1. `docs/README.md`: catalogue and verification conventions.
2. `docs/surreal/euclidean-three-space/README.md`: particularly the
   description of Part III, *Valuation Cuts and the Universal Set-Sized
   Quotient of Surreal Rotation Groups*.
3. `docs/surcomplex/first-kappa-coefficients/README.md`: particularly the
   bounded-support field-closure statements and the distinction between
   regular and singular support bounds.

A connector code search for `omnific` returned no matches. This is weak
negative evidence: index coverage and retrieval limits prevent treating it
as proof of absence. No complete repository checkout or proof audit of all
reports and historical manuscripts was performed. The article intentionally
states this limited scope rather than claiming an exhaustive comparison.

The rotation-group report is an acknowledged conceptual precedent for
asking about universal set-sized quotients. The new proof here uses scaled
fields, divisibility, and a finite collision identity in a ring ideal,
not commutators in a rotation group. The first-kappa report is an acknowledged
precedent for bounded-support Hahn fields. Their field closure, including
possible singular support bounds, is not claimed as new here. Regularity
in the new construction is used for simultaneous support gaps and ideal
generation.

## 2. External mathematical inputs

### Surreal normal forms and Hahn arithmetic

Alessandro Berarducci, *Surreal numbers, exponentiation and derivations*,
arXiv:2008.06878v1 (2020).

https://arxiv.org/abs/2008.06878

Sections 3 and 8–10 supply background for set-sized cuts, Conway monomials,
normal forms, and the finite-contribution Hahn support calculus. These are
standard inputs. The article gives its own proofs of the uniform support
gap and the scaled-field collision mechanism.

### Algebraic closedness of full Hahn fields

Bjorn Poonen, *Maximally complete fields*, L'Enseignement Mathematique
39 (1993), 87–106, especially Corollary 4.

https://math.mit.edu/~poonen/papers/amsval.pdf

The corollary supplies algebraic closedness when the coefficient field is
algebraically closed and the value group is divisible. The bounded-support
closure argument in the article localizes the finitely many polynomial
coefficients into a smaller rational exponent span and applies this standard
theorem there. The real case follows using the ordered real Hahn field and
its algebraically closed complexification. This closure is not a novelty claim.

### An explicit omnific prime

Sonia L'Innocente and Vincenzo Mantova, *A factorisation theory for
generalised power series and omnific integers*, arXiv:1710.07304v5,
22 January 2024; related publication DOI 10.1016/j.aim.2024.109513.

https://arxiv.org/abs/1710.07304

The published input is the primality of
`q = omega^(sqrt(2)) + omega + 1` in the omnific integers. It was checked in
the authors' abstract and paper. It is neither reproved nor claimed as new.
The new application proves that the nonzero domain `Oz/(q)` has no unital
map into any nonzero set-sized ring and no nonzero set-sized unital module.
The representation obstruction uses `c0(q) = 1`, not a new factorization
argument. No claim about the current status of other factorization or
refinement conjectures is made.

### Filtered colimits and flatness

The Stacks Project, Section 10.39, Tag 00H9, Lemma 10.39.3.

https://stacks.math.columbia.edu/tag/00H9

A filtered colimit of flat modules is flat. This is used for the explicit
increasing union of free rank-one principal ideals. The rank-one
nonprojectivity argument, tensor vanishing, change-of-rings Ext computation,
flat-dimension calculation, and extension witnesses are proved in the
article itself.

## 3. Proposed originality and search limitations

Targeted searches combined terms such as `omnific integers`, `homomorphisms`,
`set-sized`, `constant term`, `quotient`, and `projective`, alongside primary
surreal and generalized-power-series literature. The searches did not locate
an identical statement of the universal ring quotient theorem or of the
explicit cardinal/homological threshold package. Negative search results
are not evidence sufficient to certify priority.

The proposed original contributions are:

- The universal set-sized quotient of `Oz` and `Oz[i]`, including the module
  version and the explicit collision proof with arbitrary ring targets.
- The quotient-level universal property and the obstruction for non-arithmetic
  prime quotients, including the application to the cited omnific prime.
- The two-sided cardinal-scale construction, minimum ideal-generator count,
  and exact detection thresholds under explicitly stated cardinal arithmetic.
- The combination of those thresholds with flat idempotent nonprojective
  ideals and exact minimum sizes of degree-one and degree-two Ext witnesses.

Routine consequences, such as ordinary finite congruences after quotienting
by the purely infinite ideal, are not promoted as individually substantial
new theorems. Standard Hahn-field closure and the cited primality theorem
are explicitly excluded from the novelty claim. This report does not claim
to settle a named established open conjecture.

## 4. Proof checkpoints

The following distinctions were checked while developing the proofs:

- Constant coefficient is multiplicative on the nonnegative-exponent ring,
  not on the entire surreal field.
- Every element has set-sized support. A positive lower bound on that support
  provides a genuine monomial factor with purely infinite quotient.
- The collision identity is finite. The target map is never applied
  termwise to an infinite source sum and need not preserve strong summation.
- The explicit geometric witness has positive, strictly decreasing support.
  In its support estimate the correct inequality is
  `b + n(b-c) <= (n+1)b < a`; the first comparison need not be strict at n=0.
- Ring targets may have zero divisors or be noncommutative. The contradiction
  uses equality of two images and the image of a fixed monomial square,
  never cancellation or inversion in the target.
- The module argument compares the size of the module itself, rather than
  bounding the often much larger endomorphism ring.
- Proper-class universal properties are interpreted in a set/class foundation.
  Quotient notation does not silently treat proper classes as elements.
- Uncountable regularity of kappa is separate from the optional assumption
  `kappa^{<kappa} = kappa`. Lower bounds use the former; exact matching
  cardinal-size upper witnesses use both. CH supplies the indicated
  kappa = aleph_1 example. No unconditional existence claim is made for
  cardinals satisfying the extra equation.
- Every Tor, Ext, free resolution, and dimension calculation is over the
  explicitly set-sized ring `R_kappa` or its Gaussian variant.
- Flat dimension one does not imply projective dimension one. Nonzero large
  coefficient-module extension classes are compatible with vanishing on
  all smaller modules.
- Exact projective dimension is left open; only the proved lower bound
  `pd >= 2` is asserted.

## 5. Computational and editorial verification

`verify.py` uses exact rational arithmetic, a fixed seed, and no external
packages. The recorded run passes 17,586 assertions in five groups:
geometric remainders and finite supports, constant coefficients, boundary
counterexamples, a diagonal Euler derivation, and real complex-structure
matrix blocks. The program's JSON report lists both its positive scope and
what it does not verify.

In particular, the computation does not verify class or cardinal arguments,
existence of infinite Hahn sums, the external prime theorem, Tor/Ext
computations, formal correctness in Lean, or novelty. Full written proofs
are the evidence for the proposed infinite results. No peer review or
formal verification is claimed.

The LaTeX file was compiled to a 25-page PDF. The final log has no unresolved
references or citations and no overfull/underfull box warnings. All pages
were rendered, overview images were inspected, and representative pages
were examined at readable resolution. Build and file-integrity details are
recorded in `build_audit.json`.
