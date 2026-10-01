# An unsquared unit product lowers degree at the same arithmetic cost

The six-field [strong-coefficient compiler](group_projective_strong_coefficient.md)
has a same-cost polynomial with a smaller exact degree. Keep its paid
unit product W, and let R_i be all comparison residuals except W-1.
Replace the final sum of squares by the explicit product polynomial

    F=W*(1+sum_i R_i^2)-1.                         (1)

This polynomial has exactly the same integer zero set as the full
certificate. Hence all strictly positive witnesses, the ordinary input,
the fixed-table theorem and its universal interpretation are unchanged.
The polynomial in (1) is not a sum of squares and is not asserted
nonnegative away from its zeros. The previous SOS remains a valid
same-cost alternative.

Keep the fixed compiler hypotheses and notation

    C=3m+3h+p+185+f_flow-3min(h,3)-epsilon,
    L=m+18 if epsilon=0, L=2m+10 if epsilon=1,
    nu=1+chi.

The certificate still costs C+3, with `10-chi` comparisons and
`m+28-chi` positive witnesses. Both final polynomial schedules cost
`C+32-3chi`, with identical multiplication/addition counts. Their exact
degrees are

| Final polynomial | Exact degree |
|---|---:|
|Former full SOS|nu(38L+2m+30)+52|
|Unsquared unit times positive outer factor|nu(27L+m+15)+46|

For the illustrative ten-letter table with both optional projections,
the result is **287 operations, 43 positive witnesses and exact degree
2376**, using the same 261-operation, nine-comparison certificate.
Without controller-mask reuse it is **288 operations and degree 1944**,
with the same witness and comparison counts. The former SOS degrees
are 3368 and 2760, respectively. This is a fixed-table compiler result,
not a numerical instantiation of the universal matrix alphabet; the
separate 75/88 numerical frontiers remain unchanged.

## 1. Exact integer zero-set equivalence

For every integer supplied assignment, all arithmetic registers and
residuals are integers. Put

    S=1+sum_i R_i^2.

Then S is a positive integer with S>=1. If F=0, equation (1) says
W*S=1. Both integer factors must equal one because S is positive.
Thus W=1 and the sum of nonnegative squares is zero, forcing every
R_i=0. Conversely, W=1 and all R_i=0 give F=0.

This proves equality with the complete certificate zero set over all
integer supplied assignments, not only positive ones. Restricting
to the parent's positive domain therefore gives exactly its original
positive witness vectors. The proof needs no sign restriction on W
before the final equation, no recovered Pell unit, and no omitted
typing or range hypothesis. The other native and outer equations are
retained as the residual squares inside S.

In particular, the strong comparison remains inside S. The auxiliary
coefficient substitution is never treated as a free off-zero identity.
All earlier positive-domain and checksum-normalization proofs remain
available through the unchanged certificate theorem.

## 2. The literal final polynomial costs the same

The actual paid product register is named `six_units` for historical
reasons; after the checksum projection its value is the five-factor
product

    W=N0*N1*N3'*Nk*Nl.

The [source](group_projective_unsquared_outer_product.py) preserves
every certificate instruction and comparison. Its `polynomial_source`
function omits only the comparison `(six_units,1)` from the list of
squared residuals. For the other e-1 comparisons it emits each
subtraction and square, sums the squares, adds one, multiplies by W,
and subtracts one to obtain (1). Every added instruction is present
in the returned literal DAG.

The finalizer costs are

    M: (e-1) residual squares +1 product =e,
    A: (e-1) residual subtractions +(e-2) sum additions
       +1 positive offset +1 final subtraction =2e-1.

These are exactly the e multiplications and 2e-1 additions of the
previous full SOS. Thus both schedules add `3e-1` operations to the
same certificate. Even an identically zero flow comparison is kept
and charged as in the parent; no special case silently reduces e.

The module also exposes the unchanged `former_sos_source` so the old
polynomial remains directly reproducible. Both outputs use the same
integer parameters and positive auxiliary coordinates. No runtime
branch, exponentiation, division or extra witness is introduced.

## 3. The strongest remaining residual is known uniformly in the table

Degree is measured in all actual supplied coordinates, including x,
before imposing equations. Fixed compiler numerals and state codes
have degree zero. With the parent's stars,

    P*=P if supplied,
    P*=16(alpha*x+height_slack)*sum_e Ehat_e if computed,
    q*=16(P*)^L, s*=2*odd_half, k*=eta+zeta,
    c*=k*s*q*.

The strong comparison residual is

    delta=(ic^2)^2-Delta(f^2-1).

Since degc=nu L+2 and `deg[Delta(f^2-1)]=4nu L+6`, its nonzero
highest form and exact degree are

    delta*=i^2(c*)^4,
    degdelta=4nu L+10.                            (2)

Here are bounds for every other residual remaining in S:

| Residual class | Degree bound |
|---|---:|
|Four history transports|3|
|Native bound r+bound_beta-X|nu(3L+m+15)+1|
|Joint scalar bound|nu|
|Repunit comparison, if P is supplied|2|
|Sparse controller flow|2|

These bounds follow from the literal compiler, uniformly in m and h.
The common B, shift, endpoints and affine input have degree one.
Each computed physical selector is an affine sum of supplied edge
hats. A history update therefore has degree at most two before its
single B multiplication, and its endpoint times P has degree at most
nu+1<=3. The joint bound is a linear sum compared with P+1. The
repunit uses one product of affine B-1 and affine J.

For flow, the [sparse source](group_sparse_macro_flow.md), Sections 2-4,
uses weighted sums of edge hats with **fixed integer state labels**.
Its raw group sums, weighted sums and the correction n(n+1)/2 are all
affine. The only variable multiplication in the flow equation is B
times its affine target word. This gives degree at most two in the
empty-state, one-state, internal-edge and all-length-two cases. The
later substitutions do not replace B or the edge hats by higher-degree
expressions. There is no uncharged or implicit power of B in a state
coefficient.

The native-bound degree is the already proved packed-r degree. Its
distance below (2) is

    (4nu L+10)-[nu(3L+m+15)+1]
      =nu(L-m-15)+9>0.

Indeed `L-m-15=3` for the eight-lane range mask, or `m-5>=3` when
the controller mask is reused. Every other bound in the table is
also strictly smaller than (2). Thus delta is the unique largest
outer residual for every permitted fixed macro table, not only the
three tables used for exact polynomial fixtures.

## 4. Exact degree and highest form of the new product

The parent establishes the nonzero highest form W* of its paid unit
product, with

    degW=nu(19L+m+15)+26.

By Section 3 the positive factor S has unique highest contribution
delta^2. Hence

    degS=8nu L+20, S*=(delta*)^2=i^4(c*)^8.

The highest part of (1) is exactly

    F*=W* i^4(c*)^8,
    degF=nu(27L+m+15)+46.                         (3)

Both factors are nonzero polynomials, so their product is nonzero.
Subtracting the constant one cannot alter it. No positivity claim
about its leading coefficient is needed: unlike the old SOS, F can
have a negative leading coefficient. Formula (3) uses the paid source
polynomials without substituting any native equation or power geometry.

## 5. Reproducible evidence

The [receipt](group_projective_unsquared_outer_product.json) stores ten
compact ledgers and one complete certificate plus final polynomial
source. On 640 assignments, including 160 signed assignments, the
checker compares the actual new output with the independently assembled
quantity `(old_unit_residual+1)*(1+sum_outer residual^2)-1`, and checks
the former SOS separately. It verifies identical literal M/A counts
and unchanged certificate registers.

Ten exact weighted offset polynomial evaluations compute the certificate
residuals and the lower-degree factor S. They check W's degree and
leading coefficient, delta's strict dominance, and S's full polynomial
degree and leading coefficient. The last two literal instructions are
checked to be multiplication and subtraction as specified. Their exact
product degree and leading coefficient establish (3), without redundantly
expanding the degree-2376 final product.

Additional random macro tables receive syntactic degree audits on the
actual complete DAG: all outer residuals obey Section 3's bounds,
including tables beyond the three small symbolic fixtures. A finite
integer-grid check supplements the elementary factor proof in Section 1;
it is not used in place of that proof or as a decidability claim.

Run the source normally for a deterministic receipt comparison or with
`--write` to regenerate it. All parent sources and receipts remain
unchanged. This packet changes only the final polynomial aggregation.

The author regenerated the receipt successfully. The root reviewer ran
a fresh default replay, reviewed the source and degree proof, and checked
256 additional independent signed full-output identities; all passed.
A second reviewer read the full note and source with no findings and
checked 320 signed complete-output/SOS identities across all ten options,
including the unchanged certificate prefix, acyclic register names and
identical M/A counts. The receipt's broader degree checks cover 134
actual DAGs through m=128; its integer-factor grid has 7,029 cases.
