# Independent audit: universal avoidance of convergent recurrences

The recurrence proof draft, now incorporated into Section 4, was read in
full. The argument is mathematically sound subject to the minor wording
clarifications listed below. This audit is not a formal proof-assistant
verification and does not certify exhaustive novelty.

## Critical points checked

1. **First crossings.** Since V_0=1>Q^j, the predecessor of the first crossing
   satisfies V_(nu_j-1)>Q^j, even when nu_j=1. The lower step bound therefore
   gives alpha Q^j < V_(nu_j) <= Q^j. Choosing a maximizing block coordinate
   supplies an actual nonzero original term. For j<k, the reverse triangle
   inequality gives separation greater than (alpha-Q)Q^j even when the two
   terms have opposite signs. The selected original indices are distinct;
   they need not be ordered.

2. **Parameter selection and conditioning.** Threshold signs determine the
   first crossing, and squared-coordinate comparisons determine the least
   maximizing coordinate including ties. Grid-boundary signs then determine
   every possible local table address. The sign representatives depend on the
   fixed center and exposed first-default vertex, but not on unexposed bits.
   Thus the conditional union bound is legitimate. Fixing all selectors before
   evaluating terminal failures is the correct order of conditioning.

3. **Signs and grid boundaries.** Excluding grid boundaries from the closed
   symmetric stability interval is sufficient for both signs of displacement.
   Zero signs in the parameter sign decomposition cannot be discarded: with
   one positive and one negative displacement, the key vector at a scale
   boundary can differ from both neighboring open intervals. The accompanying
   exact checker exhibits eleven such cases.

4. **Discontinuous selections and closed residuals.** The selected b_j need
   not be continuous. The residual center set is correctly defined instead by
   all original polynomial values f_n through the finite index bound. Its
   defining set is closed in a compact product, so its projection is compact.
   Every such residual miss is also a selected miss, preserving the probability
   bound. This avoids any reliance on continuity of the first-crossing map.

5. **Nonzero repair.** The bound V_n >= alpha^n guarantees arbitrarily late
   nonzero original terms. If a finite hit uses a zero value, the center itself
   is in the open blocker. A sufficiently late nonzero term then also hits.
   The same argument repairs residual centers in an open neighborhood. Thus
   the theorem genuinely supplies nonzero hits, not only the limit point.

6. **Matrix families.** The norm, determinant, power contraction and normalized
   state constraints define a compact rational semialgebraic family. The
   inverse cofactor bound m! L^m gives the stated lower block bound. Writing
   n=k tau+r gives the uniform exponential upper bound. Every stable invertible
   companion matrix enters a family by first choosing a contracting power and
   then increasing L. No continuous choice of eigenvectors or Jordan form is
   required in this compact-family step.

7. **Stable tails.** Zero-eigenvalue modes disappear after a finite shift.
   The shift-operator polynomial annihilating every active root except lambda
   leaves a nonzero polynomial times lambda^n. Since the original sequence and
   all finite linear combinations of its shifts tend to zero, no active root
   with modulus at least one can remain. The resulting tail recurrence has
   real coefficients, nonzero constant coefficient, and stable spectrum.

8. **Effective search.** Once a blocker of strictly smaller measure budget
   exists, the nonzero-hit conditions form an open cover of the compact
   parameter domain. A finite subcover gives a finite index bound and finitely
   many witnessing open arcs. Rational arcs contained in them retain the
   witnesses and the measure budget. Quantifier elimination can therefore
   find a finite rational blocker; countable assembly has an explicit measure
   tail. Computable measure and effective closedness follow. No computable
   distance function or practical complexity bound follows from this argument.

## Minor wording clarifications identified during review

* Use different symbols for the companion-matrix power index and affine scale.
* In the vector extension require an injective affine map, or explicitly
  require its transformed orbit not to be eventually constant. A nonzero but
  noninjective linear map can annihilate the entire orbit.
* State explicitly that enumerated rational blockers must satisfy the requested
  density bound; this is implicit in the draft's termination argument.
* Apply the dyadic grids only at indices b>=j_0. The chosen j_0 guarantees
  c Q^(-b)>1 there, even if c itself is less than one.
* The oscillatory examples exclude identically zero special cases, such as
  r^n sin(n theta) with theta an integer multiple of pi, and identically
  cancelling finite sums, as required by the theorem's hypotheses.

## Reproducible finite verification

Run `python3 code/verify_routing.py --json verification/routing.json` from
the package root. It requires only Python's standard library.
The exact checks include selector-dependent terminal addresses, exposure atoms,
deliberate collision counterexamples, half-open boundaries with both signs,
signed first crossings for nonreal and repeated roots, nested grid separation,
and explicit small preorder trees. The logarithmic-budget checks are labelled
floating-point sanity checks of analytic bounds. They never instantiate the
astronomically large construction.

## Later audit: all infinite-range real recurrences

The stronger corollary is valid for the compact section K, though not for the
whole periodic F. Any nonempty 1-periodic F contains x+Z for each x in F, so
the latter could not avoid all unbounded recurrences.

Assume an affine copy of a real linear recurrence sequence of infinite range
lies in compact K. The sequence is bounded. After deleting a finite prefix,
Jordan expansion and the shift isolators used in the stable-tail lemma give

`a_n = u_n + b_n`, `u_n = sum_j c_j lambda_j^n`, `|lambda_j|=1`, `b_n -> 0`.

Indeed, each isolator preserves boundedness and preserves the degree of the
isolated polynomial coefficient. Active roots of modulus greater than one,
and polynomial coefficients of positive degree at unit-modulus roots, would
therefore violate boundedness. All remaining stable modes tend to zero.

Write `lambda_j = exp(2 pi i theta_j)`. Take a rational basis
`1,tau_1,...,tau_d` for the rational span of `1,theta_1,...,theta_r`, and clear
the finitely many denominators with an integer q. For each residue r modulo q,
`u_(qn+r)` is a real continuous Laurent polynomial F_r evaluated on
`(exp(2 pi i n tau_1),...,exp(2 pi i n tau_d))`. Kronecker's theorem makes
every tail of this orbit dense in the connected torus. Consequently the tail
limit set of `a_(qn+r)` is exactly the compact interval `F_r(T^d)`.

The compact K is nowhere dense: otherwise an interval in K would contain an
affine copy of a geometric sequence, already forbidden by the recurrence
theorem. Any nondegenerate interval F_r(T^d) therefore contradicts containment
in K. If all these intervals are singletons, all q residue subsequences
converge. At least one has infinite range, because the entire sequence has
infinite range and there are only finitely many residues. That subsequence is
again linearly recurrent and is not eventually constant, so the existing
convergent-recurrence theorem excludes its affine copy. This proves the
corollary with no convergence or characteristic-root restriction.

The structural background is classical. Stefan Gerhold, *The Shape of the
Value Sets of Linear Recurrence Sequences*, Journal of Integer Sequences 12
(2009), Article 09.3.6, uses this bounded unit-spectrum/Kronecker analysis:
https://cs.uwaterloo.ca/journals/JIS/VOL12/Gerhold/gerhold5.pdf . Cite only that
relevant analysis and reprove the bounded reduction. The paper's separate
unbounded-case shortcut claiming that the absolute values must tend to infinity
is false already for `2^n(1+(-1)^n)`, which is zero at every odd index. The
compact avoidance corollary does not use that shortcut.


## Final integration status

The listed wording clarifications were incorporated in the delivered manuscript.
