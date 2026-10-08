# Independent adversarial audit: one long twist and structural certificates

Independent research review, 8 October 2026. These notes audit the extension
without claiming literature novelty. The underlying baseline is ProveIt commit
`ea2abcb115aaa58f0b193ce1e045c2def983e1e6`; its ordinary macro backend is
`fast/fastunknot/twist/core.py` in this package.

The computational audit was executed before packaging. Its mathematical checks
and random corpus are unchanged in the portable script. Only import/output
paths and explanatory text were adapted for distribution. Source and result
hashes, execution status, and exact counts are recorded in
`reference/INDEPENDENT_AUDIT_PROVENANCE.json`.

## Verdicts

1. The two signed finite-threshold recurrence formulas are correct for the
   quantum-forgotten, reduced characteristic-two macro complex. The proof must
   identify both incident differentials at an interior degree, not merely the
   repeated chain groups.
2. The slope is the total rank of reduced characteristic-two Khovanov homology
   of the closure obtained by replacing the distinguished twist by its E
   smoothing. It is strictly positive. Jaeger's weighted-dot sliding theorem is
   the appropriate primary precedent; the argument is not a new basepoint
   invariance theorem.
3. The investigated signature packing certificate is valid, including nonconsecutive
   signed occurrences. It is always dominated on closed braids by the existing
   diagrammatic Rasmussen bound. It therefore supplies no additional certified
   instances to that pipeline and should not be presented as an improvement.

## 1. Common central differential

Write the context degree interval as

\[
a=-\sum_{e_j<0}|e_j|,\qquad b=\sum_{e_j>0}|e_j|,
\qquad w=b-a.
\]

The distinguished run is excluded from these sums. Let C be the direct sum of
all context groups when that run is in the E sector. Its dimension M and the
ordinary context differential D are independent of the distinguished exponent.
Let L be the sum of the dots on the cap and cup of that E smoothing. Then
F=D+L is a square-zero endomorphism of the ungraded vector space C.

The direct verification uses the Frobenius algebra A=F2[X]/(X^2). Each dot
squares to zero, different dot actions commute, and hence L^2=0. D^2=0. For a
fixed arc, multiplication by X commutes with every saddle touching that arc:

\[
m(X\otimes1)=Xm=m(1\otimes X),\qquad
(X\otimes1)\Delta=\Delta X=(1\otimes X)\Delta.
\]

These identities also hold on the reduced subcomplex defined by labeling the
circle through the fixed marked point by X. Consequently DL=LD, and F^2=0
over F2. This is an ungraded endomorphism statement: D raises context homological
degree while L preserves it. There is no claim that L has the degree of D in
the original bigrading.

Set

\[
\eta=\dim H(C,F)=M-2\operatorname{rank}F\ge0.
\]

## 2. Positive distinguished run

Its E summands are indexed by 1<=k<=m and lie in degree k. In total degree h,
the context summand of degree q occurs precisely when k=h-q lies in [1,m].
Thus the total group contains exactly one copy of every context summand iff

\[
b+1\le h\le a+m.
\]

The I summand has distinguished degree zero and is absent above context degree
b. Between two adjacent complete E groups, the differential is F under the
identification indexed by context states and circle labels. This identification
is independent of k: the baseline's geometry depends on the support pattern
(I or E), not on the positive value of k.

Let m0=w+2. There are exactly two consecutive complete E groups at m0, in
degrees b+1 and b+2. Compute H(m0), and let A_+(z) be the part in degrees
<=b+1 and B_+(z) the part in degrees >=b+2. For every delta=m-m0>=0,

\[
P_m(z)=A_+(z)+z^\delta B_+(z)
  +\eta\sum_{h=b+2}^{a+m-1}z^h.
\]

Here empty sums are zero. All chain groups and both relevant boundary maps
at or below the lower shoulder are unchanged. The upper shoulder, including
its incoming boundary, translates by delta. Every newly inserted degree has
F as both incoming and outgoing differential, so its Betti number is eta.

Crucial extraction detail: neither shoulder Betti number at m0 need equal eta.
At m0, eta can be computed from M and the rank of d_(b+1)=F. Alternatively,
at m0+1 the Betti number in the middle degree b+2 equals eta.

## 3. Negative distinguished run

Its E summands have distinguished degree -k, 1<=k<=m. Therefore the complete E
groups lie in

\[
b-m\le h\le a-1,
\]

and the maps between them are F. At m0=w+2, let A_-(z) contain the seed
homology degrees <=a-2 and B_-(z) those >=a-1. Then

\[
P_{-m}(z)=z^{-\delta}A_-(z)+B_-(z)
  +\eta\sum_{h=b-m+1}^{a-2}z^h.
\]

The lower shoulder translates downward; the upper one remains fixed. At the
seed, d_(a-2)=F determines eta through its rank. At m0+1, homology in degree
a-2 equals eta.

For both signs the total rank is R(m0)+(m-m0)eta. The proof permits links and
any basepoint. For knot recognition, component count must be checked on the
original run list, because replacing m by m0 can change permutation parity.

## 4. Identification and positivity of the slope

Let Ebar be the actual link obtained by replacing the distinguished block by
one cap and one cup. These two arcs belong to the same actual component.
Indeed, outside the replacement box, the coherent braid orientation shows that every open
path joins a top cut end to a bottom cut end (the directed path runs from the
bottom cut end to the top cut end when braid strands are oriented downward). There are two such paths, with
either of the two possible top-to-bottom matchings. Adding the top cap and
bottom cup joins both paths into one component in either case. Other closed
components are immaterial. This is a statement about the actual diagram,
not about individual resolutions, where the two dot locations can lie on
different circles.

### Local dot slide

In the ordinary crossing cube, let p,p' be successive points of the same
strand on opposite sides of one crossing, and H the reverse saddle at that
crossing, with H zero in the other cube direction. Then

\[
H^2=0,\qquad DH+HD=X_p+X_{p'},\qquad
(X_p+X_{p'})H=0.
\]

To verify the diagonal composite, use mDelta=0 and
Delta m=X tensor1+1 tensorX over F2. The last identity follows either from
the two dot actions agreeing on a single circle, or from
(X tensor1+1 tensorX)Delta=0 when the reverse saddle splits. Saddles at
other cube coordinates commute and cancel in pairs in DH+HD. A dot at any
fixed other point commutes with H by the Frobenius module identities.

Suppose W is a sum of dot actions and W'=W+X_p+X_p'. Then

\[
(D+W')(1+H)=(1+H)(D+W).
\]

Thus 1+H is an invertible change of basis, with inverse itself. Slide the
cap dot along its actual component until it reaches the cup dot; the two
weights 1 cancel. This conjugates the ungraded ordinary cube differential
D+L to D. The construction commutes with the dot at the fixed reduction
point, so it restricts to the marked-X subcomplex even if that marked point
is on a different component.

### Transfer to the run macro complex

The local Bar-Natan reductions inside the other run boxes are relative to
the external arcs. Their maps f,g and chain homotopies h commute with an
exterior dot L. Hence an identity

\[
gf-1=Dh+hD
\]

continues to hold with D replaced by D+L, since Lh+hL=0 in characteristic
two. The maps remain chain maps for the deformed differential as well. This
transfers the cube result to the compressed context complex and proves

\[
\eta=\dim_{\mathbb F_2}\widetilde{Kh}(\overline E;\mathbb F_2)>0.
\]

For positivity, ordinary reduced integral Khovanov homology has a nonzero
graded Euler polynomial: the absolute value of its reduced Jones polynomial at 1 is
2^(ell-1) for an ell-component nonempty link. Therefore integral homology
has a nonzero free summand, which survives in characteristic two. Neither
component parity nor a knot-only hypothesis is needed.

### Primary precedent

Thomas C. Jaeger, *A Remark on Roberts' Totally Twisted Khovanov Homology*,
arXiv:1109.1805 (2011), Theorem 3.1, pages 3--4:
https://arxiv.org/pdf/1109.1805 . His characteristic-two weighted-dot
construction proves precisely the needed invariance under relocating
weights while preserving their sum on each actual component. Our two unit
weights have sum zero. The local conjugation above specializes that
construction and supplies a transparent audit of the macro transfer.

For the basepoint actions and their compatible homotopies, see Baldwin,
Levine, Sarkar, *Khovanov homology and knot Floer homology for pointed links*,
arXiv:1512.05422v2, Lemmas 2.2--2.3:
https://arxiv.org/pdf/1512.05422 . Do not replace the explicit conjugation
argument by the generally invalid principle that adding any null-homotopic
operator to a differential preserves homology.

## 5. Signature packing: valid but dominated

Let a one-component closed s-braid have n crossings. Its canonical Seifert
surface F is connected with d=b1(F)=n-s+1. Retain all s Seifert disks and
some selected bands. Since F is obtained from the retained surface F0 by
attaching only one-handles, H2(F,F0)=0 and H1(F0) injects into H1(F). The
Seifert pairing on F0 is the restriction of that on F. Keeping all p positive
occurrences of one generator produces the standard T(2,p) surface and unused
disks, regardless of positions of the deleted bands. It has a definite
symmetrized Seifert form of rank p-1. Negative occurrences give the opposite
sign. Nonadjacent generator indices use disjoint strand pairs, so their
retained signed surfaces form a split union and their forms sum directly.

For a chosen sign and an independent set of generator indices, define
R=sum max(p_i-1,0). A definite subspace of dimension R in a real symmetric
d-dimensional form gives |sigma|>=2R-d. Maximizing R by weighted independent
set on the index path is elementary. Opposite signs must be optimized
separately. The disconnectedness of F0 is harmless here specifically because
all disks were retained; arbitrary subsurface H1 injectivity would be false.

However, let P be the total positive crossing count and u+ the number of
generator indices occurring positively. The existing diagrammatic Rasmussen
lower bound for a connected braid diagram is

\[
s(K)\ge e-s+2(s-u_+)-1
       =2(P-u_+)-d.
\]

The notation s(K) denotes Rasmussen's invariant, while s in this display is
the strand number. Since

\[
R\le\sum_i\max(p_i-1,0)=P-u_+,
\]

the signature certificate never improves the existing positive bound. The
negative statement follows with N and u-. The homogeneity defect for a knot
braid is u+ + u- - s + 1, which is exactly the number of mixed-sign generator
indices because every index 1,...,s-1 must occur in at least one sign.

Thus an RLE implementation should directly compute the pre-existing
Rasmussen data using exact counts and sparse touched-index sets. It should
not spend time integrating the dominated signature packing optimization.
This is a useful rejected-optimization theorem, not an algorithmic speedup.

Classical signature background: Peter Feller, *The signature of positive
braids is linearly bounded by their first Betti number*, arXiv:1311.1242v2,
Section 4, Lemmas 2--3, pages 6--7:
https://arxiv.org/pdf/1311.1242 . For the surface-minor viewpoint see Sebastian
Baader, *Positive braids of maximal signature*, arXiv:1211.4824:
https://arxiv.org/pdf/1211.4824 .

## 6. Scope and novelty

Two-ended stabilization under twisting is established literature. Andrew
Lobb, *2-strand twisting and knots with identical quantum knot homologies*,
Geometry & Topology 18 (2014), 873--895, DOI 10.2140/gt.2014.18.873,
arXiv:1103.1412v3, Theorems 1.3--1.4, is a useful predecessor:
https://arxiv.org/pdf/1103.1412 . Its oppositely oriented twist and
Khovanov--Rozansky coefficient setting differ from the current cooriented
braid, reduced F2 setting. Cite it for context without claiming its theorem
directly proves the exact formula above. The defensible contribution here
is a proved finite-threshold specialization, an explicit slope identification,
a bounded-context implementation, and reproducible comparison with the
crossing cube. A comprehensive novelty search is still required before any
claim of a new knot-theoretic stability theorem.

## 7. Independent computational audit

The script `tools/audit_long_twist.py` uses the original baseline macro
backend, constructs the signed recurrence independently, and compares it
with both the macro backend at the target exponent and the separate
crossing-cube reference backend. No production recurrence implementation is
called. Its results are in `results/independent_long_twist_audit.json`.

* Seed: 20261008.
* 104 contexts, 208 signed families, strands 2--5.
* 832 macro comparisons at increments 0, 1, 2, 5 above the proved threshold.
* 220 independent crossing-cube comparisons.
* Empty context, mixed signs, and varying distinguished index and position.
* All checks passed, including d-squared checks.

The checks verify implementation agreement in these examples; the proofs,
not the finite tests, justify the asymptotic formula. The separate `tools/audit_slope.py` audit reports 500 additional agreements
of eta with the ordinary E-closure macro homology rank; its raw results are
`results/slope_audit.json`.

## Portable reproduction

From the package root, run:

```sh
python tools/audit_long_twist.py
```

The script imports the packaged ordinary macro and independent crossing-cube
backends, never the tail recurrence implementation. It replaces
`results/independent_long_twist_audit.json` with the new run. The audit uses
Python assertions, so run it without the `-O` optimization switch.
