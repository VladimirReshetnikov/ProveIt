# A forced first production gives a complete U9 compiler in247 operations

The accepted positive-upper248 compiler has a **247=129M+118A** successor,
with the same43 positive existential witnesses, ordinary positive input,
and four fixed positive program parameters. The optional separate fifth
program-duration parameter has the same cost. Total degree remains
**at most936**. All input, variable-duration history, native predicates,
and endpoint arithmetic remain paid. The separate universal84 bound is
unchanged.

The actual loaded tag word starts with c. Every matching tile word
therefore starts with P_c. Its selector S0 and selected lower-history word
ZV0 are both strictly positive. Supplying them directly removes the
shared P^2+P correction: both affected packs now subtract the already paid
P^2. No new gate is required. The change gives a bijection of complete
positive zero tuples on valid inherited U9 slices, after proving the
inverse global slack positive at every child zero.

## 1. The exact language restriction

Keep the fixed tile order0=P_c,1=P_b,2=D_b,3=D_c. The accepted U9 metadata
Section5 specifies

    PREFIX=u^[1] Bcal(S1 tau(Pphys)),
    w=PREFIX DATA_w1 ... DATA_wn MIDDLE MU^(128n) TAIL.

The fixed-halt bridge Section4 defines u^[1] to mean u with its first
letter removed. The actual fixed U9 production begins bcb. Thus w begins
cb, independently of the recognizer's program parameters, the ordinary
input and its permitted padding. This is a property of every valid
loaded word; it does not assert that every such word has a match.

The four-tile theorem uses

    h(s)10^beta=E(w)g(s),
    e(b)=10^beta1, e(c)=1, E(w)1=e(w).

A nonempty matching word starts with a production tile and has the block
form (P followed by beta-1 deletion tiles)^T, T>=1. Appending a1 and
using the injective word code gives

    d1 ... dT b = w v1 ... vT.                      (1)

The first letter of d1 therefore equals the first letter of w, namely c.
The first production tile is consequently P_c. Since w begins cb and
beta>=2, the second letter of d1 is b and the second tile is D_b. Thus
S2>0 as well. This proof uses the exact word equation and does not assume that every block is a legal tag step
past the first short queue.

For any radix b and properly typed scalar history, write

    S0=sum_j [tile_j=P_c] b^j,
    ZV0=sum_j [tile_j=P_c] V_j b^j.

The lower initial state is the positive loaded sentinel, and every lower
affine update has positive slope and nonnegative offset. Therefore all
V_j>0. Since the first tile is P_c, both S0>0 and ZV0>0. The prior248
matching-word proof separately supplies ZU>0 for the upper selected
class {P_b,D_b}; that coordinate stays as in248.

## 2. Complete affine change and the one saved row

Use either frozen248 interface. Rename its positive supplied coordinates

    hist__Shat0  -> hist__S0,
    hist__ZVhat0 -> hist__ZV0.

Let g denote hist__global_bound. The map from new coordinates into the
old248 polynomial is

    Shat0_old=S0+1,  ZVhat0_old=ZV0+1,
    g_old=g-1,      all other supplied coordinates fixed.       (2)

The other selector hats retain their old meaning S_i=Shat_i-1, i=1,2,3.
The remaining selected lower hat is ZV1=ZVhat1-1. Define G12=S1+S2,
G03=S0+S3. Then the intended unchanged exits are

    J=S0+S1+S2+S3,
    P=HU+HV+ZU+ZV0+ZVhat1+g,
    Ctree=G12+P*S0+P^2*S1,
    Zb=ZU+P*ZV0+P^2*ZV1.                           (3)

The parent computes J by subtracting4 from the four hats. In the child,
replace that fixed subtraction by3. The parent global sum and child
P agree because the added1 in oldZVhat0 cancels the subtracted1 in oldg.

The parent shared correction is tail=P^2+P. Before applying(2), its
controller and selected packs are

    G12+P*(Shat0+P*Shat1)-tail,
    ZU+P*(ZVhat0+P*ZVhat1)-tail.

After(2), these equal, respectively,

    G12+P*(S0+P*Shat1)-P^2,
    ZU+P*(ZV0+P*ZVhat1)-P^2.                       (4)

Thus delete the one addition

    hist__repunit_tail__64=hist__P2__51+hist__P__10

and make its two subtraction consumers use hist__P2__51. The paid
P+1 row remains live in the independent range mask; it is not deleted.
All physical masks, hierarchy masks, range packs and native factors have
the same exits under(2).

There are two compensated fixed constants. Put A=2^(beta+2), C=2^L,
and d=production_offset. The upper difference is A-2 and the lower
difference is C-2. Their values do not change. The actual recipes change

    upper_constant: A+4 -> A+3,
    lower_constant: C+d+10 -> 12.                  (5)

The upper transport contains Shat0 with coefficient1 through its group
sum. The lower transport contains d*Shat0+(C-2)*ZVhat0. Hence precisely
those shifts in(5) cancel the additional constants in(2). If fixed
numerals are treated as independent formal ports, the map includes

    upper_constant_old=upper_constant_new+1,
    lower_constant_old=lower_constant_new+lower_difference+d.   (6)

It does not identify arbitrary old/new constant ports. The actual U9
recipes satisfy(6).

The static edit consists of six consumer renamings, the J subtraction
change and the two tail-consumer changes: nine edited rows and one
deleted row, with238 literal retained row records and no new rows. Two
literal retained rows consume the changed fixed constants. No source
reordering is required. Every source row, supplied port and fixed numeral
role remains live. The old Shat0 and ZVhat0 each have exactly the three
consumers exhibited in the saved delta, and tail has exactly those two.

These identities exhaust all exits of the changed cones. The complete
polynomials satisfy the all-ring identity

    F247(new)=F248(Shat0=S0+1,ZVhat0=ZV0+1,g_old=g-1,others),   (7)

with(6) included for formal numeral ports. This is an algebraic identity,
not merely equality at accepting computations.

## 3. The inverse domain is restored before parent soundness

Take a positive child zero on a valid U9 program slice. Its virtual
parent values in(2) are positive except that g_old might initially be0.
Do not apply the complete positive248 theorem at that stage.

The unchanged recoder prefix makes the geometry discriminant strictly
positive on every positive child tuple. The new history packs are
nonnegative before equations: G12,S1,S3,ZV1>=0, S0,ZV0,ZU>0, and the
remaining histories are positive. The low and high outputs retain their
positive decompositions from248. Cancel the nonzero geometry multiplier
at this zero. The sixteen unscaled parent-form integer factors are units.

The direct pretyping hypotheses are the same ones checked in248. P is
still a sum of six positive quantities, so P>=6. Each history/product
coordinate is belowP. The virtual hat ZV0+1 is belowP, since the other
five summands give P-ZV0>=5. All four unshifted selectors are nonnegative,
with S0>=1. The signed global-repunit relation gives

    P=(b-1)J+epsilon_G, epsilon_G in {-1,1},
    b=c_h D, c_h>=32, D>=1,
    J>=1, J<=P/6, b<=P+2, 0<=(D-1)J<P.             (8)

Every selector and subgroup is at mostJ. The actual hierarchy mask stays

    Mtree=J+P*(J+(b-1)J*G12)
         =J+P*(G03+(1-epsilon_G)G12)+P^2*G12.     (9)

Thus the signed250/248 estimates give Ctree<P^3 and Mtree+2<P^3, including
epsilon_G=-1 and D=1. The unchanged physical and range expressions are

    Hb=HU+P*HV+P^2*HV, Mb=(b-1)Ctree,
    Hr=HU+P*HV, Mr=(1+P)(D-1)J,
    H0=Hb+P^3*Ctree+P^6*Hr,
    M0=Mb+P^3*Mtree+P^6*Mr,
    Z=Zb+P^3*Ctree+P^6*Hr, T=P^8.

They obey 0<=H0,M0,Z<T and all prior top-field margins. In particular
H=H0+2T,M=M0+T satisfy H-Z>=T+1, M-Z>=1 and
bT-H-M+Z>=(b-5)T+2. The four joined implicit truth fields are positive
before any mask typing and have the same residues1,4,2,8 and sum q-1.
No estimate here requires g_old>0.

Apply the same individual native recovery steps in the proved order:
norm signs, rank, coupled-linear sign, joint population/index sign,
dyadic factor recovery, geometry/low-mask signs, and history Mersenne
sign. They give P=b^t, t>=1, J=1+...+b^(t-1), the disjoint selectors,
0<=U_j,V_j<D and their exact selected products. The complete parent
compiler and its chronology have still not been invoked.

Now ZU<=HU and ZV0+ZV1<=HV. Since HU,HV<=(D-1)J,

    g=P-HU-HV-ZU-ZV0-ZV1-1
      >=P-2HU-2HV-1
      >=((c_h-4)D+3)J
      >=31.                                       (10)

Consequently g_old=g-1>=30>0. All virtual parent witnesses are positive.
Equation(7) is now a genuine positive248 zero. Its accepted full theorem
supplies the loaded U9 matching word, exact endpoints and halting.
There is no circular appeal to parent soundness with a zero slack.

## 4. Completeness and complete paid scope

Conversely take a positive248 zero on a valid U9 slice. Its matching word
starts with P_c by Section1, so Shat0_old-1>0 and ZVhat0_old-1>0. Set

    S0_new=Shat0_old-1, ZV0_new=ZVhat0_old-1,
    g_new=g_old+1,

and retain all other witnesses. Equations(5)--(7) give a positive child
zero. These maps are inverse bijections of complete positive zero tuples
on the valid inherited program slices, with identical raw input and
program parameters. Malformed arbitrary positive program tuples are not
claimed to have this word-language property.

For every recursively enumerable set S of positive integers the same
effectively supplied four program parameters therefore satisfy

    x in S iff exists43 positive witnesses: F247(x,params,witnesses)=0.

The fifth separate duration parameter is optional as before. The source
keeps all43 witnesses, all duration and range obligations, and the
ordinary-input loader. It neither supplies a word length externally nor
charges an input exponent, controller, simulation or iteration as free.

Each complete source has247=129M+118A operations. Before its final
subtraction the certificate costs246=129M+117A, with one comparison to
the already paid geometry discriminant. Both variants retain eleven
fixed numeral roles; the new lower_constant is the fixed literal12.
The affine change(2), fixed-numeral map(6) and accepted parent bound936
give degree at most936. No source-array degree propagation or exact
degree claim is made.

**Remark 1 (the language hypothesis cannot be dropped).** The unqualified
claim that every nonempty four-tile match contains P_c would be false.
For beta=2,u=cb,w=bb, the two tiles P_b,D_b give a match: both sides of
the binary word equation equal10011001100. Here S0=ZV0=0. This is a
counterexample on the general binary-tag interface, not an actual loaded
U9 input, which necessarily starts with c.

**Remark 2 (the off-zero inverse remains partial on positive domains).**
At a positive supplied child tuple with g=1, equation(2) gives g_old=0.
The all-ring identity is valid there, but not the unconditional positive
parent implication. Bound(10) is proved specifically at child zeros.
No unconditional existence of a matching history is asserted.

**Open question 1 (credited next language restriction).** Root suggested
also examining a production-class sum or P_b-selected word. This packet
uses the P_c positivity needed above and also records the forced second
tile D_b, hence S2>0. The earlier draft listed D_b with the unresolved
occurrences; root supplied the second-letter argument that settles it. Occurrence of P_b or D_c individually is not proved
here. No additional saving from S2 or either unresolved occurrence claim
is asserted; a useful positive coordinate alone does not remove a gate.

## 5. Authentication and fresh evidence

The source and proof of248 were read in full as inert data/text, along
with the relevant complete250 signed pretyping proof. The four-tile
proof lines1--230, U9 metadata lines178--253, U9 chain lines1--200 and
fixed-halt bridge lines96--137 and166--204 bind the language argument.
Earlier compiler, machine and native theorems retain their established
scope; this is not a new complete audit of their implementations.

Only new static graph construction, exact independently handwritten
polynomial-cut identities and small scalar/word diagnostics are run.
No predecessor, archived, supplied or frozen helper is imported or run;
no saved source array is evaluated or used for degree propagation. The
repository is unchanged. The final evidence pins and diagnostic counts
are recorded below.

The fresh writer and exact saved-receipt comparisons in normal and
optimized Python modes from `/` passed before freezing. The receipt
contains both complete247 arrays (494 rows), six independently written
polynomial-cut identities,672 signed pretyping contexts (336 negative
repunit and224 height-one),210 typed word-occupancy/slack cases, and
Remark1's exact non-U9 word counterexample. These bounded checks do not
establish universality by sampling or materialize native Pell witnesses.

Evidence SHA256:

- Helper: `db9ecad324c6082f6c734cfe7fb55fc64a9d4e76920b2bff2127775d1392c771`.
- Receipt: `85e91368ddb3b4764879cd8591d730a60ed95e569026ec8ad7a0b6600739968e`.

The following frozen dependency bytes are authenticated. Paths lie in
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue`;
byte authentication does not broaden the proof-read scope above.

| Dependency | SHA256 |
| --- | --- |
| `neary_woods_positive_upper248_tesla.md` | `f3329cf28090e39a219ac4e3d8882b99fc5bab72ae0507647a193cbdb514d557` |
| `neary_woods_positive_upper248_tesla.json` | `bab6ba8d61e9fac494ca42124b043c358597d19bf1ebf8f8699b2c054ff476bc` |
| `neary_woods_hierarchical_history250_tesla.md` | `1bb41ed9eae9e77b2a9236c49508a55538f2ff84d1cd245f3bccec4dee39a330` |
| `binary_tag_four_tile_history.md` | `2cb8d1736852d525d4668f40eacdc8fa090c426f100110421521c85910e1e4b2` |
| `neary_woods_u9_tag_metadata.md` | `c98383dc28e3757691727ec57a208ececd32d117e97155c3d33d8de5c675b01a` |
| `neary_woods_universal_u9_tag_chain.md` | `7159fbae99ca020c2f9a10eb8560c13f56e53b6f81cd2f17f045097480f8ff03` |
| `binary_tag_fixed_halt_bridge.md` | `1519d918fc8e8e71f341df56d4f724c5a23b4ee10af5fff8e258228f5971f3a8` |
