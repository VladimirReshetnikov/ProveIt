# Fixed-prefix lower bound: independent mathematical audit

Completed 2026-10-08. This note supports `article/03_checkpoint.tex`.

## Verdict and scope

The proposed theorem is sound for the specified checkpoint, with summands counted
with multiplicity in the ordinary, explicitly delooped Bar–Natan basis. It applies
over any field via a reduced closure functor, and has a separate unreduced proof
over F₂. It does not establish a lower bound for all scan orders, all representations,
or the running time of unknot recognition. The explicit family is already part of
the rational continuation identity construction; its use as a promised-unknot
checkpoint witness is a further consequence, not a claim that rational hard-unknot
families themselves are newly discovered.

## Reduced closure and exactness

A point on an *external closure cap* survives every closed cobordism as a fixed
vertical track. Its multiplication-by-X action is natural even when the original
tangle category has no basepoints. Frobenius multiplication and comultiplication
are linear for this marked-circle A-action; births/deaths elsewhere commute.
Therefore `F(closure(-)) ⊗_A A/(X)` is an additive functor. Tensoring here is not
claimed to be exact. The only requirement is preservation of chain-homotopy
equations, which every additive functor supplies. This is stronger and cleaner
than arguing from an unspecified quasi-isomorphism.

For four ends, a circle-free matching closes to one or two circles. The unreduced
scalar chain dimensions are two or four; the reduced dimensions are one or two.
An M-summand complex therefore gives at most 2M reduced generators in total, so
2M bounds the reduced homology dimension. The Euler characteristic gives the
determinant lower bound.

The input knot orientation need not agree with the orientation chosen for the
test closure N(P). One can use the unoriented formal bracket. The conventional
oriented normalization changes only overall gradings, irrelevant to total
dimension and absolute-value Euler estimates.

If a universal Bar–Natan category is used, specialize to the ordinary Khovanov
Frobenius algebra; homotopy equivalences survive specialization. This argument
does not apply to an unrelated deformed theory whose parameters cannot specialize
to ordinary Khovanov homology.

### Stronger graded bound

If ordinary quantum gradings are retained, the argument improves. A reduced
closure of c circles has graded dimension (up to a monomial)
`(z+z**(-1))**(c-1)`. At z=i it vanishes for c>1 and has modulus one for c=1.
The absolute value of the reduced Euler characteristic is consequently at most
the number of summands whose test closure is connected. Thus M>=det for any
fixed number of ends, without the 2^(1-r) factor. For four ends, numerator and
denominator closure each see a different one of the two matching types. Our
p_k,q_k are both odd, so both closures are knots and the two type multiplicities
are at least p_k and q_k. The strongest graded conclusion is M>=p_k+q_k.
This requires preservation of the quantum grading. The original M>=p_k/2 bound
still applies if one discards that grading but preserves the full ordinary
homotopy type. No Khovanov thinness or identification of exact minimal size is
assumed by either proof.

## Primary references inspected

1. Dror Bar-Natan, *Khovanov’s Homology for Tangles and Cobordisms*, Geometry &
   Topology 9 (2005), 1443–1499.
   Published-version text:
   https://arxiv.org/pdf/math/0410495
   - Theorem 2: planar composition preserves homotopy
     equivalent complexes and is compatible with the tangle bracket.
   - Section 7: arbitrary additive functors extend
     to the formal complex category and preserve homotopies; Definition 7.1 and
     Proposition 7.2 give the ordinary Frobenius TQFT and the local relations.

2. Mikhail Khovanov, *Patterns in Knot Cohomology I*, Experimental Mathematics
   12(3) (2003), 365–374; arXiv:math/0201306, version 1 (January 30, 2002).
   https://arxiv.org/pdf/math/0201306
   - Section 3, printed p.6: module action at a crossing-free segment,
     and homotopy equivalences of A-module complexes.
   - Section 3, printed p.7: quotient definition of reduced complex and
     explicit inequality `rank reduced H >= |J(i)| = |Delta(-1)|`.
   - Printed pp.3–5: author's Jones variable convention, including the evaluation
     at i rather than −1. Our article uses conventional Jones variable t; t=−1.
   - The source initially works over Q. The same bound over arbitrary fields
     follows directly from the identical graded Euler-characteristic argument.

3. Alexander N. Shumakovitch, *Torsion of Khovanov Homology*, Fundamenta
   Mathematicae 225 (2014), 343–364. DOI 10.4064/fm225-1-16.
   https://arxiv.org/pdf/math/0405474 (version 2, June 19, 2018).
   - Section 2.2, printed pp.8–9: reduced complex and Jones polynomial.
   - Corollary 3.2.C, printed p.12: over F₂, unreduced homology is two
     grading shifts of reduced homology. This proves the same M >= det/2 bound
     using only unreduced closure, independently of our marked functor argument.
   - Primary publication metadata confirms the DOI:
     https://www.impan.pl/en/publishing-house/journals-and-series/fundamenta-mathematicae/all/225/0/88465/torsion-of-khovanov-homology

4. Kauffman–Lambropoulou topology sources are documented in the top-level `RESEARCH_PROVENANCE.md`.
   In addition, *From Tangle Fractions to DNA* §4.1 Remark 2, printed p.24, gives the bracket/Alexander determinant interpretation of the numerator
   and denominator closures. The familiar rational primitive fraction p/q gives
   determinant |p| for numerator closure. The lens-space cover calculation also
   supplies this formula directly.

## Numerical checks and exact crossing convention

For k>=1, P_k has continued fraction `[2]*(2*k-1)+[3]`, and −Q_k has
`[2]*(2*k)+[1,2]`; for k=0 use `[1]` and `[1,2]`. The displayed diagrams have
exactly 4k+1 and 4k+3 crossings and their full numerator sum has exactly 8k+4.
No assertion concerns the unknot's minimal crossing number.

`AB=[[5,2],[2,1]]`, trace 6 and determinant 1, gives p0=1,p1=7 and
p_(k+2)=6 p_(k+1)−p_k. For lambda=3+2sqrt(2),

    p_k = ((1+sqrt(2))*lambda**k + (1-sqrt(2))*lambda**(-k))/2.

Thus p_k>=lambda**k, and the integral object-count bound is (p_k+1)/2.
We intentionally omit a numeric global sweep-width bound. Only the specified
checkpoint's four actual ends are needed for the theorem.

`verify_checkpoint_family.py` compares the recurrence against independently
multiplied CF matrices, checks actual PD crossing counts and closure decisions,
compares independent Alexander determinants of the prefix closures for small k,
and checks small reduced homology ranks with the existing unsimplified cube
reference. These checks are diagnostics, not the proof of the lower bound.
