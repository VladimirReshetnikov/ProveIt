# Computing the history scale gives257 operations and degree1384

> Successor: [the dominated-endpoint rewrite](neary_woods_universal_height256.md)
> gives256 operations at the same43 witnesses and degree bound1384, with
> accepted-input equivalence on valid shifted slices. Its inverse affine
> height-slack map need not preserve positivity. This parent remains unchanged.

The [literal source](neary_woods_universal_history_scale257.py) replaces the
history scale definition in the [258-operation compiler](neary_woods_universal_offset258.md).
The default complete polynomial costs **257=133M+124A**, with **43 positive
witnesses**, four positive program parameters, ordinary positive input and
conservative total degree **at most1384**. Its certificate has256 operations
and one final product comparison. The independent fifth duration-bound
interface is also supported. The [receipt](neary_woods_universal_history_scale257.json)
records the actual emitted schedules and checks.

The saving is one addition. The much lower degree comes from computing the
history scale as a sum of witnesses instead of a product involving the loader.
No zero equation is used for degree cancellation. The fixed U9 table, all
numeral recipes, ordinary input, physical counter, duration, program-offset
minus-one convention and positive-coordinate count are unchanged. The
established75/87 frontier is separate.

The new and parent positive zeros are related by adding1 to one private
history-bound witness, on the inherited valid program/input slices. This
is not an identity of the complete polynomials on arbitrary assignments.
The new negative repunit branch is excluded before chronological decoding;
it is not dismissed by presuming that the new scale was already a repunit.

## 1. The paid definition and literal rewrite

Use lower-case b for the history radix, D for its digit-height bound, c_h
for its fixed multiplier, and P for its scale. The frozen source has

    b=c_h D, c_h=2^(L+1)>=8, D>=4,
    S_i=Shat_i-1>=0, J=sum_(i=0..3) S_i,
    G=H_U+H_V+ZUhat0+ZVhat0+ZVhat1+beta,
    P=(b-1)J+1, N_G=P-G.                              (1)

All six terms of G are positive, including beta. The old N_G is one
integer factor in a grouped unit finalizer. The new source instead defines

    P=G, N_G=P-(b-1)J.                                (2)

The row for P uses the operands of the old private G row, which disappears.
The repunit product (b-1)J remains paid. Its subtraction from P replaces
the old N_G subtraction. Thus exactly one addition is removed, with no
new supplied coordinate or changed group/anchor schedule. Source guards
reconstruct the complete canonical258 caller, then check the old P/G/unit
rows, every G/beta consumer and every recursive active interface export.
Every resulting gate must reach the emitted complete output.

At a new positive zero all integer factors in every group are units. In
particular

    P=(b-1)J+epsilon, epsilon in{-1,+1}.                (3)

This signed equation is the only repunit fact used in the next section.
The source does not pay an extra equation to choose its sign.

## 2. Pretyping fields despite the negative repunit

Equation(2) gives P>=6 and each of H_U,H_V and the three product hats
strictly below P. Equation(3) rules out J=0. As b>=32,

    J>=1, b<=P+2, J<=(P+1)/(b-1)<=P/6.                (4)

The unhat products Z_U,Z_V0,Z_V1 are nonnegative and below P; no selector
or selected-product semantics have yet been assumed. Let

    C=S0+P*S1+P^2*S2+P^3*S3,
    C_m=J(1+P+P^2+P^3),
    H_b=H_U+P*H_V+P^2*H_V,
    Z_b=Z_U+P*Z_V0+P^2*Z_V1,
    M_b=(b-1)((S1+S2)+P*S0+P^2*S1),
    H_r=H_U+P*H_V, R=(D-1)J, M_r=R(P+1).

These are the actual unchanged packed-history expressions. They give

    H=H_b+P^3*C+P^7*H_r+b*P^9,
    M=M_b+P^3*C_m+P^7*M_r+(b-1)*P^9,
    Z=Z_b+P^3*C+P^7*H_r.                              (5)

Every coefficient in M_b is at most P+1, not necessarily below P.
Consequently this proof does not split its three lanes yet. Instead,

    H_b,Z_b<P^3, C<P^4,
    0<=M_b<2P^3,
    C_m+2<P^4,
    0<=R<P, H_r,M_r<P^2.                              (6)

For C_m+2, use J<=P/6<=P-2 in its four-place sum. For R, use
c_h(D-1)J<(b-1)J<=P+1 and c_h>=8. It follows directly that

    H_b+P^3*C<P^7, Z_b+P^3*C<P^7,
    M_b+P^3*C_m<P^7.

Thus each complete lower block in(5) lies in[0,P^9), including every
possible carry from the P+1-sized mask coefficients. In particular

    floor(H/P^9)=b, floor(M/P^9)=b-1, Z<P^9.          (7)

The values b,b-1 need not yet be base-P digits. Nonetheless (4)--(6) imply

    H,M<2P^10,
    H+M-Z<3P^10,
    P^11-H-M+Z>=2.                                   (8)

For the middle bound, H-Z=bP^9+H_b-Z_b and the lower M block is below
P^9, so H+M-Z<(2b)P^9+P^3<3P^10 for P>=6,b<=P+2.
Also H-Z>=bP^9-(P^3-1)>0. Since C_m-C has coefficients J-S_i>=0,

    M-Z >=(b-1)P^9-P^7 H_r-Z_b
         >(b-2)P^9-P^3>1.                           (9)

These are integer inequalities before dyadic typing.

The recoder, its paid input/duration bound, loader scale, mask-gap
parameterization and possibly signed mask unit are all unchanged. Their
pretyping proof supplies low native ports a0,b0,z0 in(0,q0), where q0 is
the low padded scale. Joining(5) gives ports

    A=a0+q0 H, Bport=b0+q0 M, F3=z0+q0 Z,
    q=q0 P^11.

Equations(8)--(9) restore the same positive computed truth fields
F1=A-F3, F2=Bport-F3, F0=q-A-Bport+F3-1 and their identity
sum Fi=q-1. Their padding residues and all large-index lower bounds are
unchanged. This checks the precise hypothesis needed for native sign
recovery, without using the sign of(3) or chronological decoding.

## 3. Native typing and the repunit sign

Apply the independent native rank and shifted-population arguments in
[the260 proof, Sections2--3](neary_woods_universal_history_units260.md).
The changed history proof obligation is exactly the positive-field and
scale-range argument in Section2 above. The geometry/recoder definitions,
full strong equations, positive ratio slacks, paid loader congruence and
low-word duration bound have not changed. Norm signs are recovered
modulo4; local rank and the duplication inequality recover the linear
signs. The checksum-one low-nibble population obstruction excludes the
joint negative index before history decoding. The actual paid loader
excludes the geometry negative index; the recoder Mersenne congruence
then excludes the negative mask sign. This order does not use N_G=1.

The resulting complete joined AND types q=q0 P^11 as dyadic and gives
H AND M=Z. Indeed q0 and P are positive dyadic factors; Section2 bounds
the high words below P^11, and the unchanged low words below q0, so
splitting the joined words at q0 is legitimate. In particular P is now
a power of two. As P>=6, it is divisible by4.

If epsilon=+1, (3) already is the desired repunit. It also gives b<=P.
If epsilon=-1, b is unconditionally divisible by4 because c_h>=8.
Reducing P=(b-1)J-1 modulo4 gives J=3 mod4, hence J>=3. Consequently

    b=1+(P+1)/J<P.                                  (10)

This excludes the exceptional J=1 case without any assumed top-lane
semantics. In this negative branch b and b-1 are genuine base-P digits.
Equation(7), dyadic P and H AND M=Z therefore imply

    b AND (b-1)=0.

So b is a power of two, say b=2^v with v>=3. Write P=2^s. The negative
branch would give 2^s=-1 modulo2^v-1. Reducing s modulo v leaves
2^r,0<=r<v, which is at most2^(v-1), strictly below2^v-2. It cannot
represent -1. This contradiction proves

    N_G=1, P=(b-1)J+1.                               (11)

Now the complete original history lanes, including canonical selected
products and ranges, apply. If the positive branch had P=b,J=1, its
already dyadic P gives dyadic b directly; otherwise the reserved lane
gives dyadic b as above. Then D=b/c_h is dyadic, and the usual divisibility
argument yields P=b^T with positive duration T. No malformed low mask
carry remains, since (b-1)J=P-1 after(11).

## 4. Positive parent restoration and valid input scope

Once the history lanes are typed, H_U,H_V<=(D-1)J and the disjoint
exceptional classes satisfy Z_U<=H_U and Z_V0+Z_V1<=H_V. Thus the new
supplied slack is uniformly positive by a large margin:

    beta=P-H_U-H_V-Z_U-Z_V0-Z_V1-3
        >=((c_h-4)D+3)J-2>=17.                       (12)

Set beta_parent=beta-1>=16 and leave every other supplied coordinate
unchanged. Equation(11) makes the old computed P equal the new P, while
the old global sum is P-1. Hence its global unit is1. Every remaining
source value, factor, group and comparison is identical. This gives a
positive258 zero. Its theorem proves acceptance on the unchanged valid
program slice, including the true sentinel load__tag_input+1 and the
original exact physical counter. In particular no modified language or
unpaid input code is introduced.

Conversely, at every parent258 positive zero on a valid program/input
slice, the parent sign proof gives its global unit+1. Set
beta_new=beta_parent+1. Then its new global sum equals the old P, so every
remaining computed value is unchanged and the new unit is1. All groups
and comparisons hold. This map and the previous one are inverse on
these positive zero sets, and preserve all outer coordinates. There is
no claim that arbitrary invalid parameter slices have the same positive
zeros or that these maps equate arbitrary off-zero polynomials.

An algebraic identity is still available on the +1 repunit locus: if
beta_new is assigned (b-1)J minus the sum of the five other positive
history coordinates, plus1, the affine lift beta_parent=beta_new-1
makes all retained source registers and complete outputs identical.
The checker tests this conditional identity with signed as well as
positive assignments; positivity on actual new zeros follows from(12).

## 5. Literal degree, guards and reproducible checks

The new P row is an ordinary sum of supplied witnesses, so its propagated
polynomial degree is1. This is a property of the emitted graph, independent
of(11). Every other degree is propagated through its actual row, retaining
only the frozen, guarded exact polynomial cancellation in each main norm.
The default native-scale degree bounds are1 and16. Its factor bounds are

    14,40,9,209,490,114,24,264,6,96,6,96,4,4,4,4,

which sum to1384. There is no remaining ordinary residual; the final
product-minus-one gate costs one subtraction. These are upper bounds,
not assertions of exact degree or circuit optimality.

The builder also handles the inherited strong/scale choices, fifth-bound
interface and selected grouped schedules. Every one loses exactly one
addition; degree is recomputed, not copied from258. The receipt covers32
canonical base/interface choices and44 distinct selected schedules.
This is a mapped family, not a new exact optimization over all partitions.

```sh
python3 neary_woods_universal_history_scale257.py
```

The checker independently reconstructs the intended scale substitution,
all remaining registers, all group products and both anchored/SOS scalar
finalizers. It also verifies complete parent output identities on the
+1 locus and positive parent extensions. Further exact component checks
cover both pretyping repunit signs, nondyadic P, every separated block
bound and negative dyadic/Mersenne residues. Five incompatible source or
export mutations are rejected. These finite checks supplement the proof;
none is represented as a materialized full Pell zero.

Author receipt generation and a separate fresh default replay pass. The
receipt checks76 complete ledgers,608 scale-substitution outputs and608
conditional parent outputs, with304 signed assignments and304 positive
parent extensions. Its1,920 weak-repunit fixtures include960 negative
units and1,876 nondyadic scales;3,584 dyadic negative-repunit exclusions
and five admissible negative divisor cases check the modular sign argument.
All four local links resolve.

Franklin independently reviewed the full proof and source and passed a fresh
default replay with no findings. His own executor checked256 complete scale
substitution outputs (128 signed) and256 conditional parent/register identities
(128 positive extensions), across all16 bases and both interfaces. Separate
packed-lane formulas checked1,920 edge-concentrated weak-bound fixtures
(960 negative units);10 dyadic-P negative-repunit fixtures fail the actual
reserved top AND. An exact weighted/offset univariate specialization attains
all16 displayed factor bounds, summing1384. This uses finite substituted
numerals and is not an exact-degree claim for the actual enormous fixed
constants. His four-link audit also passes.

Root independently reviewed the full source/proof and the260,275 and
slope-class dependencies, then passed a fresh default replay with no
findings. A separate executor with manual P overrides and conditional beta
maps checked256 complete outputs and retained-register identities (128
signed), across32 canonical base/interface choices. Independently assembled
packed words passed6,480 extreme pretyping cases, including3,240 negative
units and6,192 nondyadic scales. Those cases concentrate selector mass and
positive-coordinate mass separately, with D between4 and65, c_h in
{8,16,64} and J between1 and17; strict field margins, top floors and low-mask
carry bounds all passed. These algebraic and component fixtures are not
full native Pell zeros. The trio is frozen after the author and both
independent reviews. No frozen parent, shared navigation or Git state is
changed by this packet.
