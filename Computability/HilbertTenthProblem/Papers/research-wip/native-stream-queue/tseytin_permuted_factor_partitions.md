# Complete factor partitions for the permuted-digit Tseytin387 compiler

The [source](tseytin_permuted_factor_partitions.py) and
[receipt](tseytin_permuted_factor_partitions.json) rebuild the finite
factor-group family from the complete
[permuted-digit387 source](tseytin_permuted_digits387.md).
The operation / propagated-degree frontier is

|Operations|M|A|Certificate|Comparisons|Positive witnesses|Degree bound|
|---:|---:|---:|---:|---:|---:|---:|
|387|179|208|373|5|62|4712|
|388|178|210|371|6|62|4132|
|390|178|212|370|7|62|2900|
|392|178|214|369|8|62|2210|
|394|178|216|368|9|62|1664|

All rows retain the actual fixed 24-tile C2 system, the unchanged
exponent52 source, the paid fused query loader, one fixed positive
program parameter A, and ordinary positive input x. For every computably
enumerable positive set T, the recompiled permuted-digit program recipe A_T gives

\[
 x\in T\iff\exists z_1,\ldots,z_{62}>0:\ F(x,A_T,z)=0
 \qquad(x>0).
\]

The exact finite search includes two strong bases, every disjoint factor
partition, and either SOS or one unsquared anchor. Exactness refers to
that search over the stated propagated degree bounds. No exact expanded
universal degree or lower bound over other arithmetic circuits is claimed.
The separate established 75-certificate /87-polynomial operation bounds
are unchanged.

Unlike the [earlier425 factor packet](tseytin_universal_factor_partitions.md),
the present computed checksum is identically one. Every surviving factor
is consequently +1 at a complete positive zero on a valid program slice.
Thus **all groupings in one fixed base have the same full supplied
positive zero set on those slices**. Across the two strong treatments,
only the accepted-input equivalence through positive auxiliary extensions
is asserted. The previous factor packets and their frontiers remain frozen.

This is a separate family from the
[zero-a388 partitions](tseytin_zero_a_factor_partitions.md).
The digit codes are now a,b,c,d,e,# = 0,3,1,2,4,5. Copies occur in the
order #,e,b,d,c,a, followed by the same eighteen relation tiles. A leading
sentinel still encodes v as8^|v|+raw(v). The valid primary program word S
is recompiled as

    A=8*(d*8^17*enc(S)+h6_new), d=8^64−1,

where h_new is three times the388 tail coefficient list. The paid query
endpoint is I=8*enc(query)+5 and the terminal relation remains
V_final=4096*U_final+2560. The permuted parent proves universality using
its exact literal maps, nonzero residues and zero-run bound10. No equality
of program numerals, supplied positive zeros or whole polynomials across
the two encodings is asserted. All within-base claims below use the
recompiled387 program slices.

## 1. Current source and the two factor bases

The current six normalized word factors, in order, are

    and__R15, and__P17, and__first_unit,
    and__f_square_minus_one, and__index_unit, and__linear_unit.

The six following exponent factors are

    exp__N0, exp__N1, exp__Ns, exp__N3, exp__Nk, exp__Nl.

There is no checksum factor or supplied F0,F1,F2 coordinate. There are
four ordinary residuals: the global positive bound, the two chronological
transports, and the fused query loader. After deleting only unused old
product-tree ancestors, the normalized factor core has362 gates.

For the ordinary strong alternative, put Delta=A0²−1 for the word
native discriminant and t=ic². Replace

    Ns=f²−Delta*t², R16=Delta²*t²

by the ordinary source rows

    f²−1, R16=Delta*(f²−1),

omit Ns from the factor list and retain the full comparison

    t²=Delta*(f²−1).                                  (1)

Only the private product `and__normalized_strong_Q=Delta*t²` disappears
from the core. Its other two consumers are the replaced rows. This base
has361 core gates, eleven factors and five ordinary comparisons, with
the identical list of62 supplied positive coordinates. Their i coordinate
has the corresponding ordinary strong meaning.

The source requires the entire canonical387 parent, including its codes,
ordered tiles, complete source, domain and program recipe. The parent
deliberately exports minimal metadata: no inherited checksum, computed-
field or native-bound flag is assumed or inserted into it. The checker
compares all118 native/exponent rows and the161-row ancestry of the
global bound and packed H,M,Z ports with the reviewed388 scaffold.
It then checks the exact padded ports, factored index and bound rows,
strong, auxiliary-root and square rows, and private consumer sets.
The new base records this source-verified contract explicitly. It
uses no old425 `reference_word` graph: that historical graph has different
scale, fields and bound coordinates. The new proof in Sections2–4
establishes the ordinary alternative directly. The five potentially
rebuilt coordinates are f,i,j,o,y; a source dependency guard verifies
that all main data, implicit truth fields, r,S,X,Y, power factors and
ordinary outer comparisons are independent of them.

## 2. Positive implicit fields and X>r before native typing

Let B be the history radix, P its scale, D the supplied positive height,
J the sum of the24 selector hats minus24, and T=P^34. The unchanged
positive global comparison and exact repunit imply

    B=65536D>=65536, P=(B−1)J+1, J>=1, B<=P.           (2)

Indeed J>=0 from positive hats; J=0 would give P=1, whereas the positive
global sum contains ten positive word/selected-product coordinates plus
a positive slack. The scalar lane bounds from the
[computed-field proof](tseytin_computed_fields401.md#1-positive-fields-from-the-retained-scalar-bounds)
apply unchanged: they use that global sum and positive hats, not a native
norm, dyadic typing, one-hot selectors or an initial-height conclusion.
They give

    H=H0+2T, M=M0+T, 0<=H0,M0,Z<T,
    q=16BT, H−Z>=T+1, M−Z>=1,
    BT−H−M+Z>=(B−5)T+2.                              (3)

These inequalities hold at D=1. Write the mathematical padded ports as
A=16H+12, C=16M+10, Zp=16Z+8. The implicit fields are

    F0=q−A−C+Zp−1, F1=A−Zp, F2=C−Zp, F3=Zp.          (4)

All are strictly positive by(3), sum to q−1, and have residues1,4,2,8
modulo16. Hence every field is below q. Their base-q packing satisfies

    q³+q²+q+1<=r=sum_i Fi*q^i<q⁴,
    r>q, r>=4369, r=1 modulo16.                      (5)

The actual emitted source computes, with no supplied truth-field inputs,

    S=A+1+(q+1)(C+(q−1)Zp), r=(q−1)S,
    X=q(S+beta), beta>0.                             (6)

The source's `and__padded_A` means A+1; it is not the former port A.
Identity(6) is an all-integer algebraic identity after(4), not an AND
assumption. From q>1,S>0,

    X=q(S+beta)>qS=r+S>r.                            (7)

These are proof-defined fields and identities; no extra field coordinate,
comparison, or arithmetic operation is silently supplied. The smaller
bound does not establish X/q>r before typing, and that stronger assertion
is not used here.

## 3. Unit signs for the ordinary strong base

First consider the all-factor product with its ordinary comparisons.
At a positive zero, all individual factors are integer units. As in the
complete387 parent, the independent exponent52 signed theorem, followed
by the permuted-digit two-parity fused-loader residue test, gives power
product P_exp=+1 on the valid program slice. It also restores the literal
query endpoint. This step uses no word semantics or height assumption.
The complete factor product is one, so the word product W is now+1.
For clarity, the two nonzero residues of the wrong exponent branch
are

    29966043244819123951156626953424814080,
    45854471631935696494459945720637767680,

modulo d=8^64−1. They are three times the388 residues and strictly below d, after
recompiling the valid program numeral and constant tail. The
parent proves this from its literal coefficient formula, for both
parities of x; finite literal-query fixtures are only a supplement.
Once the exponent product is+1, its theorem gives Q=8^(32x), so the
paid loader fixes I to the recoded literal query. Any later endpoint-height
argument may therefore use its binary zero-run bound10. The ordinary
base proof below postpones the parent's full chronological word theorem
until the positive restoration in Section4. The same reasoning applies to any grouping
in Section5 because its group equalities imply the full product is one.

For the ordinary strong source the word factors are the three norms

    N0=g²+4XY²k(g−k),
    N1=d²−Delta*c²,
    N3=Delta*(f²−1)*(V²−y²)+y²,

and the two linear units

    Nk=K−r, Nl=V−jc+2K,
    K=k−hE, E=XY, V=of−c.                            (8)

Here Y=q(2s+1), k=eta+zeta, c=kY+eta, a=Y(X+1), A0=a+2,
Delta=A0²−1, and d=X+ac+gamma(4a+3). All supplied coordinates are
positive. N0 is a square modulo4 and Delta is0 or3 modulo4, so N0=N1=1.
Comparison(1) makes the coefficient of V²−y² a square t². N3 is then
congruent to V² or y² modulo4, so N3=1. No pretyping sign for V is assumed
in these congruences. Write Nk=epsilon,Nl=lambda, each in{−1,+1}.

The positive first-root inverse gives k=psi_P0(n), n>=1, at
P0=2XY²+1>A0. Equations(5),(7), together with Y>=3q>=48, imply

    E>2r+3, 0<r+epsilon<E,
    Y(r−1)>2(2r+3).                                  (9)

Since P0=1 modulo E, the index equation gives
n=r+epsilon+vE with v>=0, so n>=r−1. The main positive root gives
c=psi_A0(p), d=chi_A0(p). Since c>k and P0>A0, p>n, hence p>=r.
Consequently

    c>2p, c>Yk>=Y(r−1)>2(2r+3),
    c>A0*Delta².                                    (10)

For the last bound, p>=4369 and elementary Pell growth give
c>(2A0−1)^(p−1)>A0^5>A0*(A0²−1)². The
[generic ordinary strong-rank lemma](../../1980/PELL_RELAXED_AUXILIARY_PROOF.md)
therefore applies to the full equation t²=Delta(f²−1), t=ic². It gives

    f=chi_A0(m), c divides m, m>=c>2p,
    t=Delta*psi_A0(m).

In particular f>2chi_A0(2p)>2c and V=of−c>0. Put
Jnew=2K−lambda. By(9),(10),

    0<Jnew<=2r+3<c/2, 0<p<c/2, V=jc−Jnew=of−c.

Now the retained auxiliary norm is `(tV)²−(t²−1)y²=1`.
Its positive Pell index ell is odd. The odd quotient identities and
signed chi step-down used in the
[current local sign proof](tseytin_computed_fields401.md#3-recover-the-local-norm-and-linear-signs-in-order)
apply with these bounds and c|m. Explicitly,

    V=(-1)^((ell−1)/2)*psi_A0(ell) modulo f,
    V=(-1)^((ell−1)/2)*ell modulo c.

V=−c modulo f gives ell=±p modulo m by reducing to a nearest multiple
of m and comparing the resulting chi coordinates below f. The bounds
f>2chi_A0(2p) and chi_A0(m−1)<f/3 exclude both a negative small
representative and the endpoint2z=m. Since c|m, the second congruence
and V=−Jnew modulo c give Jnew=±p modulo c. Their strict windows force

    p=Jnew=2K−lambda.

Since n<p<=2r+3<E, the earlier congruence has n=K exactly. If lambda=−1,
p=2n+1. Pell duplication at A2=2A0²−1>P0 gives
psi_A0(2n)=2A0*psi_A2(n)>k(Y+1), contradicting the retained upper ratio.
Thus lambda=+1. There is now no checksum sign left to compensate Nk:
W=N0*N1*N3*Nk*Nl=1 forces epsilon=+1. Therefore

    n=r+1, p=2r+1, N0=N1=N3=Nk=Nl=1.                 (11)

The argument used X>r, not X/q>r or an already-complete positive-scale
AND theorem. For the normalized base, the parent proves the same result
with its strong norm Ns=1 and the same(2)–(7); thus all six word factors
are+1 there too. The exponent52 proof forces all six of its factors+1
once its product is+1.

## 4. Cross-base positive completeness and source corrections

At a normalized zero, Ns=f²−Delta(ic²)²=1. Set
`i_ordinary=Delta*i_normalized`. This is positive and leaves every main
or outer coordinate unchanged. The ordinary comparison becomes zero,
its auxiliary coefficient equals the normalized one, and every ordinary
factor is+1. It is a complete positive ordinary zero.

Conversely take an ordinary positive zero. Section3 has already proved
c=psi_A0(p) with p=2r+1=3 modulo4. Rebuild only the five auxiliary
coordinates, at those same A0,c,p, by the standard full minus construction:

    m=2cp, f=chi_A0(m), i=psi_A0(m)/c²,
    Taux=Delta*psi_A0(m), y=psi_Taux(p),
    V=chi_Taux(p)/Taux,
    o=(V+c)/f, j=(V+p)/c.                            (12)

The multiple-index binomial identity gives c²|psi_A0(2cp). At p=3
modulo4 the canonical odd-quotient congruences give V=−c modulo f and
V=−p modulo c. Thus all displayed coordinates are positive integers.
The resulting normalized strong and auxiliary norms equal one, while
V=of−c=jc−p gives Nl=1. No main datum, implicit field, bound slack,
ordinary comparison or power factor changes; the source's dependency
guard checks that precise independence. This is a complete normalized387
zero on the same program/input slice, so the parent's full universal
soundness and completeness apply. No word-input or height semantics
were invoked before this positive restoration.

For arbitrary integer assignments the formal forward i change has the
exact corrections

    ordinary strong residual=Delta(1−Ns),
    ordinary auxiliary factor=normalized auxiliary factor
                          +Delta(Ns−1)(V²−y²).       (13)

Every other retained register outside the changed strong cone agrees.
These identities are audited on signed and positive assignments. They
are not identities between whole grouped polynomials, and they do not
provide an arbitrary positive-coordinate inverse. Cross-base semantics
uses(12) when necessary.

## 5. Grouping preserves each base's full positive zero set

Partition the factors of one fixed base into nonempty disjoint groups
and compute U_j as each group's product. Keep every ordinary residual
R_i. The allowed polynomials are

    sum_i R_i²+sum_j(U_j−1)²                           (SOS),
    U_a*(1+sum_i R_i²+sum_(j!=a)(U_j−1)²)−1           (anchor a).

At an integer zero all group products equal one and all ordinary
residuals vanish. Their product restores the full selected base zero.
Sections2–3 then force every individual factor to+1 on the valid program
slice. Conversely all factors are+1 at every such base zero, so every
partition and anchor vanishes on that identical supplied tuple. This
proves the stated full within-base positive-zero equality. No comparable
claim is made for arbitrary program constants outside the valid recipe,
or across the changed strong-coordinate meaning.

For n factors, g groups, m ordinary comparisons and c core gates, the
certificate has c+n−g gates and m+g equations. Both finalizers cost

    c+n+3m−1+2g.

Here m=4 or5, so the empty-residual exception never arises. Normalized
cost is385+2g; ordinary cost is386+2g. The one normalized all-factor
anchor is exactly the parent387 polynomial, with a reassociated product
tree. General regroupings need not be identical polynomials off zero.

## 6. Exact finite search of propagated degree bounds

The normalized factor weights are

    760,1804,416,974,345,345,5,7,14,22,3,3,

with maximum ordinary residual bound7. The ordinary weights are

    760,832,416,345,345,5,7,14,22,3,3,

with residual bound690. Only the word strong cone changes. The source
propagates degrees from the actual current graph and guards the two
all-integer main-norm cancellations. It imports no historical literal
native graph and uses no equality valid only at solutions to cancel a
formal leading term.

For a group weight d_j, SOS has bound2*max(r,d_j), and anchor a has
bound `d_a+2*max(r,{d_j:j!=a})`. The
[exact subset optimizer](neary_woods_universal_joint_and_coupled_partitions.md)
enumerates every possible anchor subset and uses the least-maximum-group
subset recurrence on its complement. Its pruning uses proved lower
bounds and attained upper bounds only. Thus, for every group count, the
returned plan minimizes this finite propagated objective. Literal cost
depends only on the group count, giving the frontiers stated here.

Normalized alone has387/4712,389/4705,391/3608; ordinary alone has
388/4132,390/2900,392/2210,394/1664. The normalized floor3608 is attained
by three SOS groups of weights1804,1521,1373. Its largest factor1804
forces this SOS floor. An anchor omitting1804 exceeds3608; one including
1804 but omitting974 has bound at least3752; including those but omitting
760 gives at least4298; including all three but omitting416 gives at
least4370; including all four has anchor weight at least3954. No anchor
improves the floor.

The ordinary floor1664 is attained by four SOS groups of weights
760,832,690,470. An anchor omitting832 exceeds1664; one containing it
has bound at least832+2*690=2212. The receipt also checks all4095 and2047
nonempty anchor subsets as finite floor certificates. The global floor
for these two bases is therefore1664 at394 operations. It is a minimum
of the stated bound objective, not a minimum possible actual universal
polynomial degree.

## 7. Source, receipt and evidence

`base(normalized=True|False)` returns a fresh canonical current scaffold.
`grouped(base,partition,anchor)` emits any valid grouping, with `None`
selecting SOS. `build(operations=394)` selects a combined frontier row;
`normalized=True|False` restricts selection to that subfamily. Complete-source,
degree-bound and ledger APIs require equality with the full canonical
base/plan packet, including domains, interfaces and semantic scope.

The receipt stores all23 group-count winner ledgers and seven complete
frontier schedules with hashes. Additional ordered/nonoptimal plans
exercise every possible anchor in a four-group fixture. The528 signed/positive scalar
checks compare every retained core register and independently reconstructed
finalizer, including264 signed cases. Sixty-four strong-base maps verify(13),
including32 signed maps and32 positive forward maps. Another64 signed
assignments compare the all-factor normalized polynomial directly with387.

The scalar pretyping audit evaluates actual graph rows at600 positive
global-bound contexts, including D=1 and nondyadic scales, checking every
field margin, packed-index identity and local X/Y/E bound. These contexts
are not assumed to satisfy any native norm, AND or Boolean selector rule.
Modulo-four and sign-algebra checks supplement, but do not replace, the
local rank proof. Independent Bell enumeration of smaller weighted
problems validates the unchanged optimizer. No fixture is claimed to
materialize a complete enormous Pell zero. The receipt also compares all23 schedules against their388-family plans:
every actual source loses one multiplication with additions unchanged.
Every retained register degree bound, factor weight and ordinary residual
bound agrees; the two new correction products have degree1. The direct
387 polynomial agrees with the all-factor normalized anchor on arbitrary
signed assignments, solely by reassociation. These are separate claims:
no arbitrary-point identity with the differently encoded388 polynomial
is asserted.

Twenty-four bad canonical/domain/encoding/native-contract/partition
callers are rejected. The inherited parent query audit checks96 literal
query instances, both wrong-sign residues and the ten-zero run bound.
Author generation43329 and fresh replay4170 passed. The preceding388
family and the387 parent are separately reviewed dependencies; their
receipts remain frozen.

Native independently read the full source, proof and dependencies and
passed fresh1892. One API wording issue was corrected: the complete-source,
degree-bound and ledger APIs require full canonical equality; the lower-level
degree_dictionary helper propagates guarded norm bounds. No findings remain.
His independent subset recurrence reproduced all23 group-count objectives,
both floors and the combined frontier. It checked23 actual388-to387
ledger/complete-degree transfers(−1M, same A),37 winner/novel-plan
degree/domain/closure ledgers,444 core/group/manual-finalizer outputs
(222 signed),74 zero-selector assignments,96 full strong-forward maps
(48 signed), and two five-coordinate support audits. A separate118-row
native/exponent plus161-row pretyping comparison and480 new uneven
global-bound source contexts(96 at D=1,408 nondyadic) checked every
positive-field, index and X/Y margin. Nine links and whitespace passed.
These remain finite algebra/source fixtures, not complete native Pell zeros.
