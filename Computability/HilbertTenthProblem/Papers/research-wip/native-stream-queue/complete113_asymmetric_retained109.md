# Retained-a,c asymmetric sources: 111 operations at degree24 and 109 at degree34

This packet changes the actual retained-a,c source from `X=w*q^3` to
`X=w*q`, retaining `Y=s*q^3`, the ordinary strong auxiliary equation,
and the complete ordinary-input interface. It proves a bijection of the
**full positive integer zero sets**, with `w_new=q^2*w_old` and every other
supplied coordinate unchanged. Four complete emitted finalizers are included.

| Variant | Comparison schedule | Equations | Complete SOS | Exact degree | Positive witnesses |
|---|---:|---:|---:|---:|---:|
| `sos` |75=40M+35A|13|113=53M+60A|24|24|
| `pair` |76=41M+35A|12|111=53M+58A|24|24|
| `triple` |77=42M+35A|11|109=53M+56A|42|24|
| `two_pairs` |77=42M+35A|11|109=53M+56A|34|24|

Every binary multiplication, addition and subtraction is charged, including
multiplication by a fixed numeral and the full residual/square/sum finalizer.
All supplied fields and every gate are live. The two nondominated points in
this four-source family are **109/34 and111/24**. They extend the authenticated
older86–98 operation/degree catalogue and dominate the intervening113/28
and111/30 points. The older
86–98 points have19 witnesses; these new points have24. This is not a global
optimality result, a new74-operation comparison bound, or a claim about
all possible unit partitions.

## 1. Exact parents, interfaces and source changes

The direct parents are the default six-definition projection in
[complete74_gap_selective_projection113](complete74_gap_selective_projection113.md)
and its protected main/input grouping
[complete113_main_input_units111](complete113_main_input_units111.md).
Their source/receipt/note bytes, all inherited arithmetic dependencies, and
four proof notes are authenticated before every public construction or check.
No historical Python module executes. The proof dependencies are the
[actual raw universal source](../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md),
[ordinary relaxed auxiliary rank proof](../../1980/PELL_RELAXED_AUXILIARY_PROOF.md),
[half-parameter index proof](../../1980/HALF_PARAMETER_PELL_92_PROOF.md), and
[half-binomial kernel](pell_kernel_half_binomial42.md).
Their bytes are now frozen provenance; subsequent frontier notices belong
in landing documents rather than those pinned proof files.

The ordinary input is x>0. The same24 positive witnesses remain:

    F,Jrep,W,Z,a,alpha,c,delta,eta,f,ga,h,i,j,o,phi,r,rho,
    s,tau_gap,w,y_aux,zeta,zquot.

The fixed numeral ports remain `Bm1,Kconstant,twice_cell_bits,inner_bits,MC,MF`.
For the universal theorem they are the parent's admissible compiled constants,
not arbitrary positive values: `Bm1=B-1`, `B=2^d`, d>=4; the MF port includes
the parent's fixed shift by B-1. The evaluator can also evaluate other integer
port values algebraically without asserting their universality.

The same six positive graph definitions are inherited:

    q=(B-1)Jrep+1, C=Z+W, k=eta+zeta,
    d_main=X+a*c+ga*(4a+3),
    kappa=(2d*x+inner_bits)+delta*(a^2+4a+3),
    mu=W+a*kappa+rho*(4a+3).

Here d_main denotes the computed main root, avoiding confusion with the fixed
cell width d. In particular **a and c remain independent supplied coordinates**.
Their equations a=Y(X+1) and c=kY+eta are retained, not substituted before
establishing the reverse positive map.

For each finalizer the packet emits a full symmetric reference with
X=w*q^3,Y=s*q^3. The symmetric `sos` and `pair` are the exact frozen parents;
the `triple` and `two_pairs` references are literal protected-grouping
successors. Their complete costs are113,111,109,109 and exact degrees
28,30,50,44 respectively. The asymmetric source then changes exactly one row:

    wn2 = w*n2       becomes       wn2 = w*q,
    n2 = q*q*q      remains live through Y=s*n2.

The source proves that w has this sole source consumer and no direct
comparison consumer. Under w_new=q^2*w_old, the two `wn2` values agree by
associativity. Every subsequent register, comparison, and the entire paid
finalizer then agree. This is an all-value polynomial identity over any
commutative ring. The inverse identity holds over the rationals when q!=0;
its positive integer validity at zeros requires Sections3–6.

## 2. Protected grouping and the complete off-zero correction

Write g=tau_gap, L=XY^2k, H=4a+3, Delta=a^2+H, and define the four literal units

    N0 = g^2+L*(2g-k),
    Nm = d_main^2-Delta*c^2,
    Ni = mu^2-Delta*kappa^2,
    Na = (i*c^2)^2*((j*c-r)^2-y_aux^2)+y_aux^2.

The parent's first residual is1-N0; the other three are Nm-1, Ni-1, Na-1.
The squared first residual is consequently (N0-1)^2. The four variants use

    sos:       N0=1, Nm=1, Ni=1, Na=1;
    pair:      N0=1, Nm*Ni=1, Na=1;
    triple:    N0=1, Nm*Ni*Na=1;
    two_pairs: N0*Nm=1, Ni*Na=1.

Every other residual is retained exactly. The metadata maps all13 parent
comparisons and all19 original raw comparisons to the current rows; historical
positive-definition deletions remain explicitly historical.

For every integer a, Delta is0 or3 modulo4. Thus neither Nm nor Ni can be-1.
Writing t=i*c^2, Na is congruent modulo4 to y_aux^2 if t is even and to
(j*c-r)^2 if t is odd. Hence Na also cannot be-1, without invoking the strong
auxiliary equation. An integer product equal to1 has only unit factors.
These sign exclusions recover each grouped unit as+1.

In `two_pairs`, **no first-norm sign assumption is needed**: N0*Nm=1 forces
N0=Nm=1 because Nm cannot be-1. This grouping therefore preserves the entire
integer zero set at the same scale, just like the other two groupings. The
asymmetric coordinate theorem itself remains a positive integer statement.

For an additional independent sign observation, on positive tuples V=XY^2>1,
N0=(L+g)^2-V(V+1)k^2 cannot be-1. A supposed solution T,k>0 descends through

    k'=(2V+1)k-2T, T'=(2V+1)T-2V(V+1)k.

The norm is unchanged, and T<(2V+1)k/2 gives k'>0, while
T^2-V^2k^2=Vk^2-1>0 gives k'<k. Replacing T' by its nonzero absolute value
contradicts minimal positive k. This observation is not used to enlarge the
integer grouping theorem or to skip any retained equation.

The receipt records the exact complete SOS difference as a polynomial in
N0,Nm,Ni,Na: replace the relevant singleton squares by the displayed product
squares. For example the two-pair difference from the13-row SOS is

    (N0*Nm-1)^2+(Ni*Na-1)^2
      -(N0-1)^2-(Nm-1)^2-(Ni-1)^2-(Na-1)^2.

These are full off-zero corrections, not polynomial equality at unchanged
coordinates. They combine with the separate exact w-coordinate identity.

## 3. Raw untyped packing bounds: keep the exceptional boundary

We prove reverse integrality for a positive asymmetric zero. First use Section2
to recover all four individual norm equations and restore the six positive
graph definitions. Let R denote supplied r, J denote Jrep, and MF0 denote
the unshifted fixed mask, so the actual MF port is MF0+B-1.

The exact raw source supplies

    C=Z+W, C+alpha+2d*x=q, q=(B-1)J+1,
    R=(q^2-Z-qF)*(q^2-1)+(MC+q*(MF0+B-1))*J.

The compiled constants obey 0<MC,MF0<B-1, MC=2 modulo4,
MF0=4 modulo8. In particular MF0>=4. Set

    S'=Z+qF-1,
    T'=MC*J+1+q*(MF0*J-1).

Literal expansion gives

    R=(q^2-S')*(q^2-1)+T',
    3q+1<=T'<q^2-1.

Since R>0, S'<=q^2. Since F,Z>0, S'>=q. Consequently

    q>=B>=16,                 3q+1<=R<q^4.             (1)

The boundary S'=q^2 is allowed: Z=1,F=q makes the original source's
`gap=q^2-Z-qF` equal-1, but R=T'>0. This proof does not import F+Z<q or a
stronger R bound from the coupled/normalized parent.

With X=wq and Y=sq^3,

    X>=q, Y>=q^3, E=XY>=q^4>R, 0<R+1<=E.              (2)

The equality R+1=E is not discarded. From the retained exact equations,
a=Y(X+1), c=kY+eta, k=eta+zeta. Put A=a+2 and Delta=A^2-1.
Then P=2XY^2+1>A, 6XY^2>a, and kY<c<k(Y+1).

## 4. The ordinary rank equation and exact indices

The first norm is

    (L+g)^2-XY^2(XY^2+1)k^2=1.

Its fundamental positive Pell unit has coefficient2 and first coordinate
P=2XY^2+1. A coefficient1 solution is excluded by the two consecutive squares;
coefficient2 gives P. Therefore for some n>=1,

    L+g=chi_P(n), k=2*psi_P(n).

The retained equation k=R+1+hE and P=1 modulo E imply

    2n=R+1+vE.

By (2), v<0 would make2n<=0, including the boundary R+1=E; so v>=0 and
n>=(R+1)/2>=25. The positive main norm gives c=psi_A(p), d_main=chi_A(p).
Since P>A and c>k>psi_P(n), monotonicity gives p>n. Hence p>=26 and

    c>A*Delta^2, c>2p, c>kY>=2nY>=Y(R+1)>2R.         (3)

For the first bound, psi_A(p)>=(2A-1)^(p-1)>A^5>A*Delta^2.
These inequalities are proved before typing q or using auxiliary integrality.

The actual retained strong equation is the **ordinary relaxed norm**

    rho_aux^2=Delta*(f^2-1), rho_aux=i*c^2>0.           (4)

It is not the normalized equation f^2-Delta*(i*c^2)^2=1. Apply the generic
rank argument in the pinned relaxed-auxiliary note using precisely (3),(4)
and c=psi_A(p). Its quadratic-field step needs c>A*Delta^2: writing
Delta=(F^2-1)S^2 in the fundamental integer-coefficient Pell sequence, a
proper gcd index would give h>=c/Delta but h^2<A*c/2, a contradiction.
Thus the auxiliary field index is a multiple of the main index. The ensuing
binomial congruence gives c|m. The conclusion used here is exactly

    f=chi_A(m), p|m, c|m, m>=c>2p,
    rho_aux=Delta*psi_A(m).                            (5)

The generic proof is independent of its historical parameter choice a+4;
our parameter is A=a+2, and all its stated rank hypotheses have just been
verified. We do not assume pc|m or normalized-strong divisibility.

Set U=j*c-R. By (3), U>0. The two retained auxiliary equations are

    rho_aux^2*(U^2-y_aux^2)=1-y_aux^2, U=o*f-c.

They give `(rho_aux*U)^2-(rho_aux^2-1)*y_aux^2=1`. In the positive Pell
sequence with base rho_aux, the first-coordinate divisibility by rho_aux
forces the index ell to be odd. Write ell=2h0+1. The quotient polynomial
Q_h0 satisfies

    U=Q_h0(rho_aux^2),
    Q_h0(1-A^2)=(-1)^h0*psi_A(ell),
    Q_h0(0)=(-1)^h0*ell.

These are the actual half-parameter identities of the pinned index proof.
Reducing modulo f, (4) and U=-c imply, after squaring,
`chi_A(2ell)=chi_A(2p) modulo f`. Reducing modulo c gives
`(-1)^h0*ell=-R modulo c`.

For clarity, the required strict step-down needs no parity of p. Write
ell=epsilon*z+k0*m with epsilon=+1 or-1 and0<=z<=m/2. The Pell pair at2m
is(-1,0) modulo f, so

    chi_A(2ell)=(-1)^k0*chi_A(2z) modulo f.

Since m is an integer greater than2p, f> (2A-1)*chi_A(2p).
If2z=m the left representative is0 modulo f, impossible. Otherwise both
chi_A(2z) and chi_A(2p) are below f/(2A-1). Their sum is less than f.
Odd k0 is impossible, and even k0 forces equality, hence z=p.
Thus ell=+p or-p modulo m, and also modulo c. Together with the U congruence,
R=+p or-p modulo c. By (3), both R and p lie strictly between0 and c/2;
therefore

    p=R.                                              (6)

If v>=1, (2) gives2n>=R+1+E>=2R+2, contradicting n<p=R.
Thus2n=R+1 exactly, and R is odd. This replaces the stronger E>2R argument
available in older common-q-cube proofs; E>R is sufficient here.

## 5. Power recovery and the full positive inverse

Put r0=(R-1)/2>=24. The elementary Pell growth estimates give

    c/(k/2) >= xi*(1+3/(2a))^(2r0)
                    *(1+1/(2XY^2))^(-r0) > xi,
    xi=(X+1)^(2r0)/X^r0.

The weak bound follows from psi_A(2r0+1)>=(2A-1)^(2r0) and
psi_P(r0+1)<=(2P)^r0. The strict final inequality uses only6XY^2>a,
not an upper ratio error estimate or the old X>=q^3 hypothesis.
Since c/k<Y+1,

    Y>xi/2-1>X^r0/2-1>X^r0/3,
    a>X^(r0+1)/3>2*4^r0=2^R, X<a.                    (7)

The last strict margin follows already for X>=16,r0>=1.
The sequence z_j=chi_A(j)-a*psi_A(j) starts at1,2. Its recurrence modulo
H=4a+3 agrees with2^j because4A-1=4 modulo H. The actual main-root
definition gives X=2^R modulo H. Both positive representatives are below a
by (7), so **X=2^R**.

Since X=w_new*q, the integer q divides a power of2; hence q=2^t with t>=4.
By (1), R>=3q+1>3t, so q^3 divides X. Therefore

    w_old=X/q^3=w_new/q^2

is a strictly positive integer. All other supplied coordinates remain
unchanged and positive. The exact source identity now yields a genuine
positive zero of the appropriate symmetric reference. Section2 restores
all13 equations of the selected frozen113 parent. Only at this point is
its complete compiler/input/population theorem invoked.

Conversely every positive symmetric-parent zero maps to a positive new zero
by w_new=q^2*w_old, preserving every computed register. These maps are inverse
on the full positive zero sets, not only on a chosen canonical subfamily.
They preserve the ordinary input and fixed program slice, and impose no
external duration bound. The retained Y=s*q^3 still supplies the original
population threshold; neither that multiplier nor any strong/input equation
has been removed.

## 6. Exact degrees from the emitted source

All fixed numerals have degree0; ordinary input and every witness have degree1.
Let b=Bm1, J=Jrep and

    Ltop=b^7*w*s^2*(eta+zeta)*J^7,
    Dtop=b*w*J+4*ga*a,
    Mtop=Dtop^2+2*a*c*Dtop.

Exact expansion of the actual four norm cones gives their highest forms:

| Unit | Exact degree | Highest homogeneous form |
|---|---:|---|
| N0 |12| `Ltop*(2*tau_gap-eta-zeta)` |
| Nm |4| `Mtop` |
| Ni |7| `-4*delta^2*a^5` |
| Na |10| `i^2*j^2*c^6` |

For Nm the cancellation is `(ac+X+gaH)^2-(a^2+H)c^2`.
For Ni it is the same literal input cancellation as in the pinned111 parent.
No syntactic bound at an uncancelled subtraction is reported as an exact degree.

In `sos` and `pair`, the first residual uniquely has largest degree12;
the exact complete degree24 leader is

    b^14*w^2*s^4*(eta+zeta)^2*J^14*(2*tau_gap-eta-zeta)^2.

In `triple`, the unique largest residual has degree4+7+10=21; its square has
leader

    16*delta^4*a^10*i^4*j^4*c^12*Mtop^2.

In `two_pairs`, the two products have degrees16 and17; the unique degree34
leader is

    16*delta^4*a^10*i^4*j^4*c^12.

All are nonzero polynomials for every admissible fixed b>0, independently
of every other fixed compiler numeral. The checker expands complete residual
polynomials in all supplied leaves, with fixed numerals still formal, and
checks these multivariate leaders exactly. It also verifies all four symmetric
reference degrees and records their uniform fixed-coefficient monomials.
Literal propagated upper bounds are kept separately in each ledger.

## 7. Reproduction, API and limits

With this file beside the new script/receipt and the pinned sources available
under a WIP directory, run standard-library Python from any working directory:

```sh
python /path/to/complete113_asymmetric_retained109.py \
  --root /path/to/native-stream-queue \
  --expect /path/to/complete113_asymmetric_retained109.json
```

`--output FILE` writes a fresh deterministic receipt; `--expect FILE` compares
it with exact type-sensitive JSON equality. Optimized Python (`-O`) is rejected.
The root is searched first; an absent dependency can use its same-name sibling
or flattened proof-file basename. An existing file with wrong bytes fails,
without falling through to a different copy. There are no imports of parent
code, mutable public caches, third-party arithmetic dependencies or Git fallback.

`build(variant)`, `checked`, `rewrite`, `polynomial_source`, and `evaluate` guard
entire canonical packets. `canonical_parent` returns the exact selected frozen
parent, whereas `symmetric_reference` returns the fully emitted grouping
reference. `degree_certificate` authenticates its packet before expansion.
`forward_assignment` maps all positive integer tuples. `restore_assignment`
requires exact divisibility of w by q^2 and rejects arbitrary off-zero tuples
without it; divisibility on positive zeros is proved in Sections3–5.
The explicit signed evaluator gives integer polynomial values, not a signed
zero-set theorem for the asymmetric coordinate change.

The deterministic replay checks192 whole coordinate identities (96 signed),
32 rational inverse identities,192 complete grouping corrections,2,064 retained
residual comparisons, all four full ledgers and symbolic degree certificates,
eight public positive graph roundtrips, strict malformed callers and copy
isolation, and every warm source/proof hash guard. Its finite components include
1,920 raw-packing fixtures with160 occurrences of the exceptional S'=q^2 boundary,
128 modulo4 sign checks and1,920 nearest-multiple cases. The complete Pell
restoration theorem is the proof above, not an inference from those finite
fixtures; no astronomical full accepting witness is claimed to have been
materialized. The packet covers exactly these four forms and their four emitted
symmetric references.
