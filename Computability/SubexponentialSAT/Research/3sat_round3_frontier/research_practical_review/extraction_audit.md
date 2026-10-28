# Independent packet extraction audit

## Conclusion and scope

The centered antipodal identity, its guard-bit requirement, the projective
odd-root filter, and the proposed mixed sign/cube-root filter are valid.
They preserve the packet's creation-precision semantics when the output is
first computed at its immutable creation precision and only then canonically
lifted. These are selective local coefficient-extraction improvements, not
an end-to-end SAT performance theorem or a smaller logarithmic order.

Final implementation status: the centered and projective cubic kernels,
their adaptive dispatcher, and benchmarks are delivered. The mixed
sign/cube-root identity is **notes only: not implemented or benchmarked**.
Its independent tests below validate a separately written direct formula,
not a delivered production kernel. No hybrid implementation is pending.

Reviewed implementation: `research_practical/packet_extraction.py`, read as
source without importing or executing it. Separate integer and modular tests
are implemented in `independent_filters.py`; no candidate or incoming
executable code is imported. The candidate's own tests and benchmarks are
separate evidence and are not relabeled as this audit's tests.

## Homogeneous coefficient and centered half grid

Let H(Z)=∏_{r=1}^R(∑_j a_rj Z_j) over a commutative coefficient ring,
and let β≥0 with |β|=R. Remove zero-target variables by setting them to
zero. Write B=∏_j β_j!, G=∏_j(β_j+1). An affine row product can be put
in this form by adjoining a constant variable with target exponent
β₀=R−∑_{j>0}β_j. A negative β₀ means the requested coefficient is zero.

Repeated finite differences give the integer polynomial identity

    Σ_(0≤γ≤β) (−1)^(R−|γ|) binom(β,γ) H(2γ−β)
        = 2^R B [Z^β]H.

One proof is to test monomials Z^α of total degree R. The β_j-th difference
annihilates degree below β_j; since |α|=|β|, only α=β survives, with
factor ∏_j 2^β_j β_j!=2^R B.

Under γ↔β−γ the sign changes by (−1)^R and H changes by (−1)^R,
so paired summands agree. If a central grid point exists, H(0)=0 for
R>0. Therefore one representative of each pair gives

    N_half = 2^(R−1) B [Z^β]H,
    number of representatives = floor(G/2).

The candidate's disjoint rectangles select the first noncentral coordinate
below its midpoint. Earlier even coordinates are fixed at their midpoints;
an odd coordinate stops the construction. This covers every noncentral
antipodal pair exactly once. Its reflected mixed-radix traversal changes
one coordinate by ±1. A centered row sum then changes by ±2a_rj, while
the binomial weight can be updated using an exact **integer** quotient.
This quotient is not an inverse of a nonunit coefficient-ring element.

To return modulo 2^p, put h=R−1+v₂(B). Compute N_half modulo 2^(p+h),
divide canonical coordinates by the explicit 2^h, and multiply by the
inverse of the odd integer B/2^v₂(B) modulo 2^p. The output is exact.
Reducing the numerator modulo 2^p before this division is invalid.

The source ring has an integral finite-free presentation
Z[U,V]/(f(U),V^ell), with f monic. Consequently integer polynomial
identities and coordinatewise power-of-two divisibility descend to it;
irreducibility is unnecessary for this extraction identity. This is why
nilpotents do not invalidate the guard-bit argument.

## Projective cubic filter

Assume every retained β_j is 1 or 2 and let ω be a cubic root satisfying
ω²+ω+1=0. Fix any coordinate k to one, and evaluate all other coordinates
at ω^g_j, g_j∈{0,1,2}. Multiply by the character
ω^(−Σ_(j≠k)β_j g_j), sum, and divide by the odd integer 3^(t−1).

For a monomial Z^α, cubic orthogonality forces
α_j≡β_j (mod 3) at every free coordinate. Since 0<β_j<3 and α_j≥0,
this means α_j=β_j+3q_j with q_j≥0. Homogeneity then forces
α_k=β_k−3Σq_j. Because β_k<3, nonnegativity forces every q_j=0.
Thus only the requested monomial survives. There are exactly 3^(t−1)
evaluations and no additional power-of-two precision is needed.

The same proof applies to an odd order m when every positive β_j<m and
the ring contains an orthogonal m-th root. The candidate verifies the
orthogonality sums explicitly rather than assuming root^m=1 suffices in
an arbitrary ring. Its phase update and precomputed neighboring-root
increments agree with the character formula.

The restriction β_j<m is essential. With target β=(1,3), fixing the
second coordinate and using cubic filtering on the first aliases the
monomial with exponent α=(4,0). The independent negative control detects
this. Homogenization must also be included in the restriction: a large
constant-variable target exponent cannot be ignored.

The actual source extension has even residue degree 4λ and hence contains
F₄. A nontrivial cubic root lifts because the derivative 2ω+1 is a unit.
The candidate's bitwise lift uses the derivative's residue one; adding the
top error bit cancels it modulo the next power of two. Searching for an
initial residue root may be polynomial in source size but is not free and
is explicitly excluded from the local timings. An actual integration must
charge it, preferably once per fixed extension with reusable lifting data.

## Mixed sign and cubic characters

This optional extension is proved and independently checked here, but was
intentionally not added to the delivered implementation or benchmarks.

For β∈{1,2}^t let n₁ be the number of ones and n₂ the number of twos.
If n₁>0, fix a coordinate with exponent one. Use signs ±1 on the other
one-coordinates and cubic roots on all two-coordinates. Orthogonality
forces each surviving free exponent to be β_j+m_jq_j, where m_j=2 or 3
and q_j≥0. The fixed exponent is

    α_k = 1 − Σ m_jq_j,

so all q_j vanish. The numerator is therefore

    2^(n₁−1) 3^n₂ [Z^β]H.

It uses 2^(n₁−1)3^n₂=G/2 evaluations and n₁−1 guard bits, with no
factorial division. If n₁=0, fix a two-coordinate and use cubic filtering
on the rest: there are G/3 evaluations and no guard bits.

### Root precision need not be raised merely for the guard

For the mixed filter, a cubic root valid modulo the creation precision 2^p
can be arbitrarily lifted to the temporary guard precision. A stronger
work-precision Hensel lift is sufficient, but is not necessary. The reason
is that summing the full sign characters is, coefficientwise, divisible
by 2^(n₁−1) as an integer polynomial in the coefficients and the cubic
root placeholder. Changing that placeholder by a multiple of 2^p changes
the sign-summed numerator by a multiple of 2^(p+n₁−1). After the exact
division, the result modulo 2^p is therefore independent of the lift;
cubic orthogonality is needed only at precision p.

This corrects an initially overcautious message from this reviewer that
called a guard-precision root lift necessary. The correction was sent
and incorporated into the implementation notes. Thirty explicit tests
over Z[U]/(U⁴+U+1) use ω=U+U², a cubic root modulo two but not modulo
four, and confirm that arbitrary-lift guard evaluation still works.

## Immutable creation precision

The implementation's `_prepare` canonicalizes all input coefficient
coordinates using the requested ring precision **before** constructing a
higher-precision work ring. This is correct when that requested precision
is the tensor's immutable creation precision. All divisions occur in the
temporary numerator computation, and the resulting entry is reduced to
creation precision before storage or return.

A later recursive call must reuse that stored creation-time entry (or
reevaluate its immutable description at that same creation precision), then
canonically lift the result. It must not call the extractor on the original
factors at the later requested precision. For example, the coefficient
4·3⁴=324 is zero modulo four but four modulo sixteen. Recreating it at
precision four bits is different from lifting the two-bit creation value.
The independent negative control verifies this distinction.

For temporary computation, any fixed lifts of coefficients congruent modulo
2^p yield the same final coefficient modulo 2^p. Keeping canonical lifts
is a clear and safe implementation convention; it does not authorize
changing the tensor's creation precision or its defining quotient polynomial.

## Counts and fair baseline comparison

The appropriate incumbent is the full **forward Gray** grid, not a naive
implementation that recomputes every row sum. Both baseline and candidate
update R row sums after one coordinate change and multiply R row values.
Leading per-grid-point ring work is O(R), with polynomial initialization and
integer-weight maintenance. Centered rectangles can require several fresh
initializations; this is polynomial and should remain in timing results.

| Method | Grid points | Additional precision bits |
| --- | --- | --- |
| Forward Gray finite differences | G | v₂(B) |
| Centered antipodal Gray | floor(G/2) | R−1+v₂(B) |
| Projective cubic | 3^(t−1), only β∈{1,2} | 0 |
| Mixed characters with n₁>0 | G/2 | n₁−1 |
| All twos cubic specialization | G/3 | 0 |

The forward homogeneous grid's origin has zero value, so a trivial further
optimization can skip its product, reducing G to G−1 nonzero-point product
evaluations. The delivered baseline currently counts it. This changes only
one point and does not explain the observed gains, but the baseline should
not be called globally optimal or the strongest possible implementation.

For all ones, the projective cubic grid can be much larger than either
forward or centered grids. For all twos, it is one third of the forward
grid, and approximately two thirds of the centered grid. The mixed filter
retains the half-grid count while reducing guard bits relative to centered
differences. Extra guard precision, root setup, ring dimension, weight
arithmetic, and constants can reverse finite timing comparisons. Therefore
these are optional kernels; a dispatcher may choose an estimated cost, but
no universal wall-clock speedup is established.

The candidate benchmarks use the same coefficient data and ring for each
method, include setup/lifts/precision division/output, and alternate method
order. Excluding initial cubic-root discovery is disclosed. They are
synthetic packet microbenchmarks, not SAT, contraction, or upstream-program
timings. Packet-entry work remains a lower-order term in the contraction
certificate; halving its local grid does not halve the SAT exponent.

## Independent evidence

Normal and optimized independent runs have identical substantive output:
183 centered integer identities, 732 centered modular/guard checks, 1,572
projective monomial checks, 63 projective ring identities with 252 modular
checks, 63 mixed-filter identities with 252 modular checks, 30 deliberately
under-lifted-root controls, and one creation-precision control. The tests
include noncanonical signed coefficients and nilpotent V with ell up to
three. Finite tests supplement the algebra above; they do not prove the
general identities or substitute for eventual integration tests.

No denied, pending, or uncertain operation occurred. No candidate or
upstream program was imported or executed during these independent checks.
