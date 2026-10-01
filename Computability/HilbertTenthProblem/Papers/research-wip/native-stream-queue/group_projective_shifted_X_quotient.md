# Shifting the native quotient removes the separate index bound

The six-field [factored-index compiler](group_projective_factored_native_index.md)
has a positive quotient reparametrization that removes one witness and
one comparison. It uses the already computed factor S in r=(q-1)S:

    X=q(w+S),             X-r=qw+S>0.                    (1)

The old bound addition is reused for w+S, so the certificate costs the
same. The final product polynomial saves **three operations**, one
multiplication and two additions. Divisibility q|X remains explicit.
This is an exact bijection between the old and new positive certificate
zero sets, preserving the ordinary input and every outer history field.

At the same time the auxiliary norm coefficient is restored from K to
T^2. The retained strong comparison T^2=K proves equality at every
zero. This uses the same multiplication, and gives the smaller degree
for the new quotient parametrization.

Keep the fixed-table hypotheses and notation of the parent:

    C=3m+3h+p+185+f_flow-3min(h,3)-epsilon,
    L=m+18 if epsilon=0, L=2m+10 if epsilon=1,
    nu=1+chi.

Here epsilon selects controller-mask reuse, allowed for m>=8, and chi
selects computed P. The complete new six-field ledger is

| Quantity | Exact value |
|---|---:|
|Certificate operations|C-1|
|Comparisons|9-chi|
|Strictly positive witnesses|m+27-chi|
|Final product operations|C+25-3chi|
|Final product degree|nu(44L+9m+135)+44|

For the illustrative ten-letter table, all four switch choices are:

| Mask reuse | Computed P | Certificate | Polynomial | M | A | Equations | Positive witnesses | Degree |
|---|---|---:|---:|---:|---:|---:|---:|---:|
|No|No|258|284|120|164|9|43|1819|
|No|Yes|258|281|119|162|8|42|3594|
|Yes|No|257|283|119|164|9|43|2171|
|Yes|Yes|257|280|118|162|8|42|4298|

The smallest operation count trades increased degree for fewer gates.
Leaving P supplied also gives useful intermediate points. These are
complete fixed-table compiler bounds; the universal numerical matrix
alphabet is still uninstantiated. The separate numerical 75/88
frontiers are unchanged.

## 1. A positive paid factor, before any native equation

The parent computes

    q=16P^L,
    S=(16H+13)+(q+1)((16M+10)+(q-1)(16Z+8)),
    r=(q-1)S.                                          (2)

S is the existing register `packed_top_sum`; it costs no new gate to
use it. H,M,Z are the joined input, mask and output integers. For any
strictly positive supplied assignment, their source expressions are
nonnegative. Raw physical selectors are sums of nonnegative edge
counts, and decoded output coordinates are Zhat_i-1>=0. The region
scales and radix are positive. When P is supplied it is positive by
domain; when P is computed, J=sum_e(Ehat_e-1)>=0 and
P=(B-1)J+1>=1. Thus q>=16 independently of any comparison or native
AND theorem.

Consequently every padded term in S is strictly positive, and
S>0, r>0 hold before typing. In fact even H=M=Z=0 gives
S>=8q^2+10q+15, so q<r. None of these facts assumes the old X bound.
No new Boolean typing, power geometry, range assertion or existential
coordinate is introduced here.

In the parent the quotient and bound are paid as

    X=q*w_old,            r+bound_beta=X,

with w_old,bound_beta strictly positive supplied coordinates. Replace
these two instructions by

    shifted_native_quotient=w+S,
    X=q*shifted_native_quotient,

and remove the bound comparison and coordinate. Equation (1) follows
identically from (2). Thus the native inequality X>r is available
before any Pell recovery, exactly where the parent proof needs it.

## 2. Exact positive witness correspondence

First map a new positive zero to the parent by retaining every other
supplied coordinate and setting

    w_old=w+S,            bound_beta=qw+S.               (3)

Both restored coordinates are strictly positive without imposing any
equation. The parent X equals the new X, and its bound residual is
identically zero. All downstream native quantities agree, except for
the auxiliary coefficient discussed below. The retained strong
comparison makes that difference zero as well. Hence every parent
comparison holds. The parent theorem therefore proves the same fixed
matrix-history relation and the same ordinary-input acceptance claim.
This direction does not invoke the native theorem before recovering
its positive bound witness.

Conversely, start with a positive parent zero. Its already established
native theorem gives

    X=2^(2r+1),          X=q*w_old.

This application is legitimate because the parent still has its
strict positive bound witness and all original hypotheses. Since
q<r and 2^r>=r+1 for r>=1,

    X=2^(2r+1)>r^2,     w_old=X/q>r>S.

Define the new positive integer w=w_old-S. This leaves X unchanged.
The old bound equality gives

    bound_beta=X-r=q(w_old-S)+S=qw+S,

so the maps are inverse. Every other supplied coordinate is unchanged.
In particular, the ordinary input x is not recoded, the fixed program
numerals alpha,beta do not vary at runtime, and all new supplied
coordinates remain strictly positive. The earlier checksum-branch
normalization is already part of the parent theorem; no new negative
unit branch is added by this quotient change.

For the coefficient change, write

    delta=T^2-K,
    G=V^2-y^2,
    N3_old=K*G+y^2,
    N3_new=T^2*G+y^2.

The literal identity is N3_new-N3_old=delta*G. The strong residual
delta remains one of the squared outer comparisons. Thus both
coefficient choices give exactly the same positive zero sets, even
though their off-zero unit polynomials differ. If O=N0*N1*Nk*Nl,
the new unit residual equals the lifted old unit residual plus
O*delta*G. The source audits precisely this correction; it does not
claim an off-zero equality between the final output polynomials.

This argument retains q|X. The
[standalone divisibility obstruction](native_binary_X_divisibility_obstruction.md)
to dropping that property does not apply to (1).

## 3. Literal source and operation accounting

The [source](group_projective_shifted_X_quotient.py) verifies the exact
producer and consumer lists for the bound gate, its witness and X.
The packed factor S uses only outer fields and is independent of X,w
and bound_beta, so the new dependency is acyclic. A topological sort
moves the reused quotient addition before its multiplication. No new
arithmetic instruction is inserted and no old arithmetic instruction
is deleted: one addition changes operands, the X multiplication changes
one operand, and the auxiliary multiplication changes its coefficient.
The full multiplication/addition histogram is unchanged.

The removed comparison has no residual consumers elsewhere. Its
witness appears only in that comparison's paid sum. The certificate
therefore has one fewer equation and one fewer positive witness at
cost C-1.

Let W be the paid five-unit product, still named `six_units`, and R_i
all remaining comparison residuals other than W-1. The final output is

    F=W*(1+sum_i R_i^2)-1.                              (4)

For integer supplied assignments, its positive second factor is at
least one. Hence F=0 iff W=1 and every R_i=0. This is the same exact
integer-factor argument as in the parent's unsquared finalizer.
No assumption on W's off-zero sign is required.

For e comparisons the finalizer costs e multiplications and 2e-1
additions. Deleting one comparison therefore saves 1M+2A, giving
C+25-3chi operations. The former SOS is also exposed by the source
at exactly the same arithmetic cost; it has the same zero set but a
higher degree. Every fixed-numeral multiplication is paid in these
literal DAGs. No exponentiation, division or hidden witness is used
as an arithmetic instruction.

## 4. Exact degree of the shifted source

Degrees are measured in all actual supplied coordinates, including x,
before imposing equations. Fixed compiler numerals have degree zero.
Use stars for highest homogeneous parts and set

    Q=nu L,       A0=nu(4L+m+15),
    P*=P                                      if P is supplied,
    P*=16(alpha*x+height_slack)*sum_e Ehat_e    if P is computed,
    q*=16(P*)^L, s*=2*odd_half, k*=eta+zeta.

The parent's unchanged packed index has

    r*=16^4 H2 (P*)^(3L+m+15),
    deg r=nu(3L+m+15)+1.

By (2), the highest term of qS is r*, while qw has lower degree.
Therefore the new X*=r*. With a=Y(X+1), E=XY and c=kY+eta,

    a*=E*=s*q*r*,       deg a=A0+2,
    c*=k*s*q*,          deg c=Q+2.                     (5)

There is no division instruction in these formulas: S* could
alternatively be written explicitly as
16^3 H2(P*)^(2L+m+15).

Let g be the positive first-root gap and h the native index witness.
The five literal unit factors have these exact highest forms:

| Factor | Highest homogeneous part | Degree |
|---|---|---:|
|N0|4a*(k*s*q*)*(g-k*)|A0+Q+5|
|N1|8ga*(a*)^2*c*|2A0+Q+7|
|N3|i^2(c*)^6|6Q+14|
|Nk|-h*a*|A0+3|
|Nl|-2h*a*|A0+3|

In the N1 row, `ga` is the supplied main-root slack; it is not the
product of g and a. The N1 cancellation follows from the literal
main-root expression d=X+ac+ga(4a+3), giving the leading term
8ga*a^2*c. N3 uses T^2=(ic^2)^2 and V=of-c. Since c dominates of,
V*=-c*. The index and linear factors are dominated by hE after the
shift. Each displayed highest form is a nonzero polynomial.

Thus W has exact degree and highest part

    deg W=5A0+8Q+32,
    W*=N0* N1* N3* Nk* Nl*.                            (6)

For the retained strong residual delta=T^2-Delta(f^2-1), the degree
ordering has changed:

    deg T^2=4Q+10,
    deg[Delta(f^2-1)]=2A0+6>4Q+10,
    delta*=-(a*)^2*f^2.                               (7)

All other outer residuals have degree at most three. The four history
transports multiply affine shifts, selectors and endpoints at most
twice; P has degree nu<=2. The joint scalar bound has degree at most
nu. The optional repunit comparison and sparse flow have degree at
most two. In particular sparse flow coefficients are fixed integer
state labels, not powers of the variable radix. The native bound
residual has been removed. These are uniform bounds for every allowed
fixed table, not assumptions drawn from the finite fixtures.

Equation (7) therefore uniquely supplies the highest square in the
outer factor of (4). Consequently

    deg F=9A0+8Q+44=nu(44L+9m+135)+44,
    F*=W* ((a*)^2*f^2)^2.                              (8)

This is nonzero; subtracting one cannot change the degree. The former
SOS instead has exact degree 2(5A0+8Q+32), since W dominates every
other residual. Retaining K in N3 would yield the larger product degree
nu(48L+11m+165)+40 at the same arithmetic cost, which is why only the
T^2 version is implemented here.

## 5. Reproducible checks and their scope

The [receipt](group_projective_shifted_X_quotient.json) contains ten
compact ledgers and one complete certificate with its finalizer.
Across 320 supplied assignments, including 80 signed assignments,
the checker substitutes (3) into the actual parent source, checks the
deleted bound residual identically, and compares every remaining
residual with the explicit coefficient correction. It compares the
actual final output against an independently assembled unit times
positive outer factor. All unchanged certificate registers agree.
For 240 positive assignments, the restored coordinates are positive
and X-r=qw+S is checked directly before imposing equations.

Ten exact weighted-offset polynomial evaluations check each unit
factor's full polynomial degree and leading coefficient, the strong
residual and every other outer residual. The four literal unit-product
gates are checked separately; multiplying their nonzero leading forms
proves (6) and (8) without redundantly expanding a large product.
These checks use no on-zero substitution to reduce degree.

Another 4,680 finite positive shift identities and 27 canonical
inverse-size fixtures supplement the proofs. They do not materialize
full astronomical Pell witnesses or turn finite evidence into a
positive converse. The parametric correspondence in Section 2 supplies
that converse. Run the checker normally to compare with its receipt,
or with `--write` to regenerate it.

Independent proof/source review and a separate fresh default replay
passed. Another 256 complete supplied assignments checked the exact
final-product correction against the lifted parent, including 128
unconditional positive graph extensions and their bound witnesses.
