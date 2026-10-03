# Computed truth fields and a factored native bound give401 operations

> The [reviewed all-unit query successor](tseytin_query_unit378.md)
> gives378 operations,62 witnesses and degree at most4713. The preceding
> [cross-offset factor family](tseytin_cross_offset_factor_partitions.md) reaches390/1664.
> Its encoding descends from the permuted-digit stage. The source, encoding
> and transfer proof below remain this frozen stage.

The [literal source](tseytin_computed_fields401.py) reduces the complete
[product-scale412 compiler](tseytin_product_scale412.md) to
**401=188M+213A**, with387 certificate gates, five comparisons,62 positive
witnesses, one fixed positive program parameter and ordinary positive
input. Its total degree is at most4712. The separate-power alternative
costs403=188M+215A and has degree bound4752. The
[receipt](tseytin_computed_fields401.json) contains all four complete
product/SOS schedules.

This transfers the established
[computed input-field](group_projective_computed_input_fields.md),
[checksum-field](group_projective_computed_checksum_field.md),
[factored-index](group_projective_factored_native_index.md) and
[smaller native-bound](neary_woods_universal_native_bound254.md) arguments
to the actual C2 compiler. All arithmetic is emitted. The three deleted
coordinates are recovered positively before native typing; the bound
coordinate is recovered positively only after its exponent is proved.
The proof below verifies that order directly for this source.

On the parent's valid program slices, every positive new zero corresponds
bijectively to a positive412 zero whose checksum is+1. Every other
positive412 zero normalizes to that slice without changing outer data.
Consequently the full ordinary-input universal relation is unchanged.
This does not assert a bijection with every parent tuple or an identical
polynomial on unchanged supplied coordinates. The overall75/87 record
is unchanged.

## 1. Positive fields from the retained scalar bounds

Use B for the history radix, P for its scale and T=P^34. At a complete
zero the ordinary global comparison still holds. Exactly as in412,

    B=65536D>=65536, P=(B−1)J+1, J>=1, B<=P,
    0<=H0,M0,Z<T,
    H=H0+2T, M=M0+T, q=16BT.                         (1)

The bounds use only the positive global sum, positive hats and the exact
repunit. They hold at D=1, before any norm sign, dyadic scale or Boolean
selector conclusion. The eight physical,24 controller and two range
lanes give the strict bounds on H0,M0,Z. In particular

    H−Z>=T+1, M−Z>=1,
    BT−H−M+Z>=(B−5)T+2,
    0<=H,M,Z<BT.                                    (2)

Denote the padded ports by A=16H+12, C=16M+10 and Zp=16Z+8.
Mathematically define

    F1=A−Zp=16(H−Z)+4,
    F2=C−Zp=16(M−Z)+2,
    F0=q−A−C+Zp−1=16(BT−H−M+Z)−15,
    F3=Zp.                                         (3)

All four fields are strictly positive by(2). Their residues modulo16
are1,4,2,8; their sum is q−1. Each is therefore less than q, and

    r=F0+qF1+q²F2+q³F3,
    q³+q²+q+1<=r<q⁴, r>q, r=1 modulo16.             (4)

The parent port comparisons become identities when F1,F2 are restored
by(3). Fixing F0 by(3) makes its checksum factor q−sum Fi identically1.
Positivity of these subtractions has been proved on the retained outer
bound locus; it is not asserted for arbitrary positive off-zero tuples.

## 2. The emitted index and its positive ordinary bound

Substituting(3) into the packing gives the exact integer identity

    S=A+1+(q+1)(C+(q−1)Zp),
    r=(q−1)S.                                      (5)

The source changes the old padded-A addition's constant12 to13, so
that register now means A+1. Its old input-port comparison is removed,
and its only new consumer is(5). It keeps the C and Zp padding gates.
The seven literal index rows are

    qm=q−1, qp=q+1,
    v=qm*Zp, u=C+v, w=qp*u,
    S=(16H+13)+w, r=qm*S.                           (6)

The field definitions(3) are used in the proof and parent restoration;
they are not extra emitted gates or hidden supplied coordinates.
The old index register name is retained. Identity(5) holds for arbitrary
integers, without any norm or checksum equation imposed afterward.

Reuse the two old bound gates, changing only the addition's operand:

    X=q(S+beta), beta>0.                            (7)

By(4)–(5), q>1, r>0 and S>0. Hence

    qS−r=S>0, X>r, r−S=(q−2)S>0.                   (8)

Also q divides X. The strict ordinary bound required for the local
rank and population arguments is therefore paid. We do not assume
X/q>r before typing; its proof is delayed to Section4.

## 3. Recover the local norm and linear signs in order

At a product or SOS zero, all ordinary residuals vanish and the displayed
integer unit products are1. In the merged-power form, the untouched
exponent52 component first has product+1 or−1. Its signed projection and
the paid query's two-parity residue certificate exclude−1 on a valid
program slice, exactly as in425/412. In the separate-power form its
product is directly constrained to1. Thus the remaining word-native
product is1, and the literal query is recovered. This step needs no
native word interpretation or history-height bound.

Write Y=q(2s+1), with supplied s>0, E=XY, k=eta+zeta,
c=kY+eta, a=Y(X+1), A0=a+2 and Delta=A0²−1. The four word norms are

    N0=g²+4XY²k(g−k),
    N1=d²−Delta c²,
    Ns=f²−Delta(ic²)²,
    N3=Delta²(ic²)²(V²−y²)+y²,
    V=of−c.

Here d=X+ac+gamma(4a+3) is the actual computed root. The remaining
linear factors are

    K=k−hE, Nk=K−r, Nl=V−jc+2K.                    (9)

No checksum factor remains. Every factor is an integer unit. N0 is a
square modulo4; Delta is0 or3 modulo4; and the N3 coefficient is a
square. Thus N0=N1=Ns=N3=1. Provisionally write Nk=epsilon,
Nl=lambda, with epsilon,lambda in{−1,1}.

The bounds(4),(8) give r>=4369, Y>=3q>=48 and

    E>2r+3, 0<r+epsilon<E,
    Y(r−1)>2(2r+3).                                (10)

The positive first-root inverse gives

    k=psi_P0(n), P0=2XY²+1>A0, n>=1.

Since P0=1 modulo E, k=n modulo E. Consequently n=K+vE for v>=0,
where K=r+epsilon, and n>=r−1. The main norm gives
c=psi_A0(p), d=chi_A0(p). Since c>k and P0>A0, monotonicity forces
p>n, hence p>=r. Pell growth and the ratio now imply

    c>2p, c>Yk>=Y(r−1)>2(2r+3).                    (11)

The full normalized strong equation has not been weakened. Ns=1 gives
f=chi_A0(m) and psi_A0(m)=ic². Strong divisibility implies p divides m.
Writing m=pb and expanding the multiple-index formula gives

    psi_A0(pb)/c = b*d^(b−1) modulo c.

The left side is divisible by c, and gcd(d,c)=1; hence c divides b.
Thus **pc divides m**, so c divides m and m>2p+1. In particular
f>2chi_A0(2p)>2c, and V=of−c>0. Put L=Delta*psi_A0(m)>1.

Set Jnew=2K−lambda. Equation(9) says V=jc−Jnew, with
0<Jnew<=2r+3<c/2 and0<p<c/2. N3=1 is

    (LV)²−(L²−1)y²=1.

Pell classification gives LV=chi_L(ell). Its index ell is positive
and odd, since chi_L(2z)=(-1)^z modulo L. The odd quotient identity gives

    V=(-1)^((ell−1)/2) psi_A0(ell) modulo f,
    V=(-1)^((ell−1)/2) ell modulo c.

Together with V=−c modulo f, squaring yields
chi_A0(2ell)=chi_A0(2p) modulo f. For completeness, choose a nearest
multiple of m and write ell=±z+jm,0<=z<=m/2. The Pell pair at2m is
(-1,0) modulo f, so the left side is(-1)^j chi_A0(2z) modulo f.
The case2z=m has residue0 and is impossible. Otherwise
chi_A0(2z)<=chi_A0(m−1)<f/3, while chi_A0(2p)<f/2.
An odd j would make a strictly positive sum below f divisible by f;
an even j forces equality of the small chi coordinates and z=p.
Thus ell=±p modulo m, hence modulo c. The second quotient identity and
V=−Jnew modulo c imply Jnew=±p modulo c; their strict windows force

    p=Jnew=2K−lambda.

Since p<=2r+3<E and n<p, the earlier congruence gives n=K exactly.
If lambda=−1, then p=2n+1. But A2=2A0²−1>P0 and2A0>Y+1, so

    psi_A0(2n)=2A0*psi_A2(n)>k(Y+1),

contradicting c=psi_A0(2n+1)<k(Y+1). Hence lambda=1. The word
product now equals Nk, so epsilon=1 too. We have proved

    n=r+1, p=2r+1, N0=N1=Ns=N3=Nk=Nl=1.             (12)

This repeats the relevant local rank/sign proof with the actual bound
X>r. It does not invoke a complete positive-scale AND theorem while
its old bound witness might be negative.

## 4. Recover the power, population and old positive gap

At the exact indices(12), put xi=(X+1)^(2r)/X^r. The elementary Pell
bounds and positive ratio give

    xi<c/k<xi(1+2/a)^(2r), Y<c/k<Y+1.

Thus Y>=X^r and a>X^(r+1)>2^(2r+1). The recurrence for
chi_A0(v)−a*psi_A0(v), with initial values1,2, agrees with2^v
modulo4a+3. The paid definition of d therefore gives
X=2^(2r+1) modulo4a+3. Both representatives lie in(0,a), so

    X=2^(2r+1).                                    (13)

The same ratio estimate has error below16r/(X+1)<1/2; the positive
fractional tail of xi is below1/4. Therefore

    Y=binom(2r,r)+sum_(j=1)^r binom(2r,r+j)*X^j.

These are the scalar ratio/exponent steps detailed in the
[raw population proof](native_binary_input_dilation129.md#2-the-raw-geometry-theorem-at-j9-and-jq);
their hypotheses r>=9, r>q, X>r and odd Y/q have all been established
here. No geometry-specific input bound is imported. Since q divides X,
q is dyadic. Also r>q ensures2q divides X. Reducing the formula for Y
modulo2q and using odd Y/q yields

    q=2^popcount(r).                                (14)

The central-binomial valuation used here is
v2((2r)!)-2v2(r!)=popcount(r), directly from the factorial valuation
formula. It does not require the native fields to have disjoint bits
in advance.

Write q=2^t. The four fields are positive and below q, so their base-q
blocks are disjoint and popcount(r)=sum_i popcount(Fi). But sum Fi=q−1
has population t, equal to(14). Binary addition can preserve total
population only without carries. The Fi are therefore pairwise disjoint
bit sets, and (F1+F3) AND(F2+F3)=F3. This is the prescribed padded AND.
The original product-scale412 history proof now applies to its outer
ports without any new endpoint assumption.

Most importantly for the coordinate map, (4),(13) give

    beta_old=X/q−r>0,

because q<r and2^(2r+1)>r²>qr. This positive integer is recovered
only now. Together with the positive fields(3), it restores a complete
positive412 tuple with checksum one.

## 5. Exact integer lift and the converse normalization

For arbitrary supplied integers, evaluate the new graph and restore
the parent's three fields by(3), and its bound coordinate by

    beta_old=beta+S−r.                              (15)

The expressions r,S do not depend on beta. They also do not depend on
the erased supplied fields. Equations(3),(5),(15) make the parent
checksum identically1, both removed port residuals identically0, and
the two X definitions identical. Every other retained register agrees,
except that the new padded-A register is explicitly one greater.
The removed checksum multiplication has the same value as its retained
input. Consequently all four complete parent/new final polynomials
agree under this integer polynomial lift. Restored fields and beta_old
can be nonpositive off zero; Section1 and Section4 establish positivity
where required.

Conversely, start with a positive412 zero on a valid program slice.
Its proved coupled theorem gives Qc=Nk=epsilon and Nl=1, with all norms1.
If epsilon=−1, the padded residues give F0=3 modulo16, so apply the
established positive normalization

    F0'=F0−2>0, r'=r−2, beta_old'=beta_old+2>0.

It preserves X, every other native coordinate and all outer data. It
makes Qc=Nk=1. If epsilon=1, no normalization is needed. In either
case the port comparisons and checksum now uniquely determine(3).
Erase these three coordinates and set

    beta=beta_old'+r'−S>0.                          (16)

The last inequality uses r'−S=(q−2)S>0. The exact graph identity proves
a new zero. On the checksum-one slice, (15) and(16), together with
unique field restoration, are inverse maps. For the negative branch
the combined formula is also beta=beta_old+r_old−S, since the two
normalization shifts cancel. It is a normalization, not an injective
map from all parent positive tuples.

This transfers every accepted ordinary input and keeps the parent's
one fixed positive program parameter. No altered query code, uncharged
input morphism, positivity oracle or weakened strong relation is used.

## 6. Exact gate count, degrees and guards

Computing F1,F2 replaces two port additions by two subtractions at
equal certificate cost and removes two comparisons. That saves2M+4A
in either finalizer. Reusing the three checksum additions to compute
F0 and deleting its factor multiplication saves another1M. Factoring
the resulting five field-definition additions and six Horner gates
into(6), with12 changed to13 in the existing padding, saves4A.
Finally(7) is a single operand change with no operation cost. The total
is **3M+8A=11 gates**, taking412 to401 and65 witnesses to62.

| Form | Certificate | Comparisons | Witnesses | Polynomial | M | A | Degree bound |
|---|---:|---:|---:|---:|---:|---:|---:|
|Merged product|387|5|62|401|188|213|4712|
|Separate product|386|6|62|403|188|215|4752|
|Merged SOS|387|5|62|401|188|213|9396|
|Separate SOS|386|6|62|403|188|215|9288|

The new literal degrees are degq=69, degS=205, degr=274 and degX=274;
the parent X had degree343. The six retained word-factor bounds are
760,1804,416,974,345,345, totaling4644. The six exponent factors still
have degrees5,7,14,22,3,3, totaling54. The maximum ordinary residual
degree drops to7 after the two port comparisons disappear. Hence the
merged product bound is4644+54+14=4712. With separate power units its
degree54 residual instead gives4644+108=4752. No on-zero expression
or canonical enormous exponent is substituted in formal degree
propagation. Both inherited main-norm cancellation identities are
checked against the actual literal subgraphs. Exact expanded universal
degree and global circuit optimality are not claimed.

`rewrite` requires the entire canonical412 packet. It also checks the
actual field, checksum, index, padding and bound rows; every private
consumer; the two unique port comparisons; the checksum factor; active
exports; fresh names; the r/S dependence cone; and a full topological
source closure. The new APIs reject altered successor metadata as well
as altered arithmetic. Historical parent records retain their earlier
field and bound meanings; use(15) before invoking parent restoration
helpers. The active metadata records A+1 and the new beta meaning.

## 7. Reproducible evidence

Run `python tseytin_computed_fields401.py` for a fresh receipt comparison;
`--write` regenerates it. The checker proves(5) symbolically, evaluates
160 complete retained-register lifts (80 signed), and checks320 complete
parent polynomial identities (160 signed). It includes zero selectors,
nonpositive formal parent gaps and negative restored fields to distinguish
off-zero algebra from positive-zero soundness.

Another450 source fixtures satisfy only the retained positive global
comparison:90 have D=1 and360 have nondyadic native scales. They check
the three positive field margins, checksum, exact packing, strict native
bound and exponential inverse margin. Another48 positive structured
checksum-branch contexts impose Qc=Nk=epsilon and Nl=1 with unrestricted
norm residuals; they check96 complete normalization outputs and positive
coordinate maps. These are component/algebra fixtures, not materialized
full giant Pell zeros. Author generation and a separate fresh default
replay pass. All eight local links and the trio's whitespace check pass.
Root independently reviewed the full source, local proof and cited scalar
ratio dependency and replayed the receipt, with no findings. Its separate
executor checked288 complete retained-register/manual-finalizer/parent
output identities(144 signed), all four degree/opcode/closure ledgers
with independent norm-cancellation propagation, and180 additional
multi-selector, uneven-global-bound contexts(30 at D=1).
