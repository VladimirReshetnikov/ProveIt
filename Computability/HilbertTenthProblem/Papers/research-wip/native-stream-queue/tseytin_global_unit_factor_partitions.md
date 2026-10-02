# Four factor bases for the global-unit Tseytin compiler

The [source](tseytin_global_unit_factor_partitions.py) and
[receipt](tseytin_global_unit_factor_partitions.json) optimize all disjoint
factor partitions and SOS/anchor finalizers in four specified bases:
normalized or ordinary word strong treatment, each with either the new
[global unit](tseytin_global_bound_unit385.md) or the retained global
equality of [shared-offset386](tseytin_shared_offsets386.md).

Their combined operation / propagated-degree frontier is:

|Operations|M|A|Certificate gates|Comparisons|Degree bound|Strong / global treatment|
|---:|---:|---:|---:|---:|---:|---|
|385|178|207|374|4|4714|normalized / unit|
|386|177|209|372|5|4134|ordinary / unit|
|387|177|210|370|6|4132|ordinary / equality|
|388|177|211|371|6|2900|ordinary / unit|
|390|177|213|370|7|2210|ordinary / unit|
|392|177|215|369|8|1664|ordinary / unit|

Every row retains62 positive witnesses, one fixed positive program
parameter A, ordinary positive input x, the actual24-tile C2 system,
the complete exponent52 relation and paid query loader. The valid program
recipe is unchanged from the permuted-digit parent: a,b,c,d,e,# have
digits0,3,1,2,4,5 and copy tiles are ordered #,e,b,d,c,a. The parent
universal theorem therefore gives the same ordinary-input representation
for every computably enumerable positive set on its valid program slice.

The387/4132 row remains useful: moving the global equality into the unit
product saves an operation but adds a degree-two factor. Omitting the
equality option would lose that point. Exactness refers only to the
four bases and the stated propagated objective, not exact expanded degree
or a lower bound over other arithmetic circuits. The independent
75-certificate/87-polynomial bounds are unchanged.

Within one fixed base, all groupings have the same full supplied positive
zero set on valid program slices. Switching global treatment shifts its
slack by one and gives a positive-zero bijection at fixed strong treatment.
Switching strong treatment can rebuild five private auxiliary coordinates;
only accepted-input equivalence is asserted for that change.

The global-unit absorption and reserved-bit sign mechanism already appear
in the [joint-bound unit packet](group_projective_joint_bound_unit.md).
The385 parent transfers that mechanism to this concrete paid C2 compiler;
this packet adds its four-base literal partition search. Neither is
presented here as a newly discovered general unit-sign principle.

## 1. Current guarded source and all four bases

The normalized word factors are

    and__R15, and__P17, and__first_unit,
    and__f_square_minus_one, and__index_unit, and__linear_unit.

With the global-unit option append

    G=P__30−global_lhs__40.

The six exponent factors follow:

    exp__N0, exp__N1, exp__Ns, exp__N3, exp__Nk, exp__Nl.

There are no supplied truth fields F0,F1,F2 and no checksum factor: the
computed checksum is identically1. The global-unit bases retain three
ordinary comparisons, namely the two chronological transports and the
fused query comparison. The equality bases retain those three and the
original global comparison. No query construction, input exponentiation
or native bound is assumed without its paid source.

For the ordinary strong option, use the exact guarded replacement from
[the preceding factor family](tseytin_permuted_factor_partitions.md).
Writing Delta for the word native discriminant and t=ic², replace

    Ns=f²−Delta*t², auxiliary coefficient=Delta²*t²

by the retained comparison

    t²=Delta*(f²−1),                                  (1)

and auxiliary coefficient Delta*(f²−1). Remove Ns from the factor list.
Only its private Delta*t² product disappears from the factor core. This
is the full ordinary strong equation, not a weakened norm.

The four literal cores, after deleting only unused product ancestors, are:

|Strong|Global|Core gates c|Factors n|Ordinary comparisons m|Complete cost at g groups|
|---|---|---:|---:|---:|---:|
|normalized|unit|362|13|3|383+2g|
|normalized|equality|361|12|4|384+2g|
|ordinary|unit|361|12|4|384+2g|
|ordinary|equality|360|11|5|385+2g|

`source_contract` requires the whole canonical selected385 or386 packet,
including program recipe, domains, codes and tile order. It separately
compares all118 native/exponent rows and the161-row pretyping ancestry
with the guarded permuted387 scaffold. The unit choice adds exactly G
to that pretyping cone. The shared386 offset rewrite is already guarded
by its own complete parent and private-consumer checks; it changes no
native or pretyping row. No inherited metadata flag is accepted as proof
of the current norm, computed-field or checksum contract.

The auxiliary dependency guard projects onto f,i,j,o,y and verifies that
all main data, fields, r,S,X,Y, exponent factors, G when present, and
ordinary outer comparisons are independent of those coordinates.
Every emitted gate reaches the complete final output.

## 2. Signs before grouping, including the ordinary strong option

Write B=65536D, P=(B−1)J+1, and let Sigma be the sum of the ten positive
history and selected-product ports. In the equality bases
Sigma+beta_old=P. In the unit bases G=P−Sigma−beta initially has either
unit sign. Thus in either treatment

    Sigma≤P, each port<P, J≥1, B≤P.                  (2)

The global-unit proof establishes the scalar lane bounds from precisely
these inequalities, including D=1 and the possible G=−1 case. With
T=P^34, q=16BT, H=H0+2T, M=M0+T, it gives

    0≤H0,M0,Z<T,
    F0=16(BT−H−M+Z)−15>2,
    F1=16(H−Z)+4>0, F2=16(M−Z)+2>0, F3=16Z+8>0,
    sum Fi=q−1, r=sum Fi*q^i=(q−1)S,
    r≥q³+q²+q+1, r=1 mod16,
    X=q(S+beta_native)>r, Y=q(2s+1)≥3q.              (3)

This is pretyping algebra; no AND condition or total word-product sign
has been used. The source comparisons verify the same cone for all four
bases, so the proof applies to the actual emitted fields and bound.

At any grouped integer zero, every group product is1 and the retained
ordinary comparisons hold. Every individual factor is therefore an
integer unit. The unchanged exponent52 signed theorem and valid program's
paid query residue exclusion force the exponent product to+1 before word
semantics or initial-height recovery. Its sign classification then makes
all six exponent factors individually+1. The recoded query and its
binary zero-run bound are unchanged.

For a normalized word base, the global-unit theorem proves all its
word factors+1 independently of G's sign. For the ordinary strong base,
the same conclusion follows as follows, without presuming its word product
is positive. The first and main norms are+1 by their modulo-four
obstructions. Equation(1) makes the auxiliary norm coefficient a square,
so that norm is+1 as well. Write

    K=k−hXY, Nk=K−r=epsilon, Nl=V−jc+2K=lambda,
    epsilon,lambda in {−1,+1}.                        (4)

The detailed ordinary rank proof in the preceding factor packet uses
only(1),(3) and these individual unit conditions through the recovery
of lambda=1. In particular XY>2r+3, Y(r−1)>2(2r+3), the first Pell index
satisfies n≥r−1, and the main index p>n. The very large lower bound on r
gives c>A0*(A0²−1)² and c>2p. The full ordinary strong-rank theorem then
gives c dividing its auxiliary index m, m≥c>2p, and a positive root
V=of−c. Strict signed residue windows yield p=2K−lambda; n<p<XY makes
n=K. If lambda=−1, p=2n+1 contradicts the upper ratio by Pell
duplication. Thus lambda=1 without a word-product sign assumption.

At this stage n=r+epsilon and p=2rho+1 with rho=r or r−2. The ratio,
root-projection and population proof of the global-unit parent gives

    X=2^(2rho+1), q=2^t, popcount(rho)=t.              (5)

It applies equally to the ordinary case: its proof uses the recovered
indices and the unchanged main/first ratio, with rho>q and X>rho, not
the former strong coefficient or G's sign.

If epsilon=−1, the four base-q fields of rho=r−2 are
F0−2,F1,F2,F3, all positive and below q by(3). Their low residues modulo16
are15,4,2,8. Writing them16A_i+l_i, their sum q−3 gives
sum A_i=q/16−2, while their low-bit population is7. Consequently

    popcount(rho)=sum popcount(A_i)+7
                  ≥popcount(q/16−2)+7=t+2,            (6)

contradicting(5). This uses binary population subadditivity, not Boolean
selector typing. Therefore epsilon=1, and every ordinary word factor
is+1. In the global-unit case the complete product now forces G=1.
In the equality case the same conclusion about the existing factors holds
without a G factor. No checksum sign remains to absorb a negative index.

## 3. Full positive semantics between bases

For either fixed strong treatment, G=1 is exactly
Sigma+beta=P−1. Set beta_old=beta+1 to recover the equality base. Conversely
an equality-base positive zero has a typed chronological history. The
sum of each side's four selected unhat products is at most its history;
therefore

    Sigma≤2(H_U+H_V)+8≤4(D−1)J+8,
    beta_old=P−Sigma≥(65532D+3)J−7>1.                 (7)

So beta=beta_old−1 is positive. This proves a full positive-zero bijection
between global treatments at fixed strong treatment, on the valid slices.
For the ordinary case, the following normalized auxiliary restoration
establishes the same typed-history bounds without changing the outer ports.

At a normalized zero, the positive forward change
i_ordinary=Delta*i_normalized makes(1) hold and leaves every other factor
and outer coordinate unchanged. At an ordinary zero, Section2 has already
given p=2r+1=3 mod4. Rebuild the five auxiliary coordinates canonically:

    m=2cp, f=chi_A0(m), i=psi_A0(m)/c²,
    Taux=Delta*psi_A0(m), y=psi_Taux(p),
    V=chi_Taux(p)/Taux, o=(V+c)/f, j=(V+p)/c.          (8)

The standard multiple-index identity and odd-quotient minus congruences
make all five positive integers, with normalized strong and auxiliary
factors1 and V−jc=−p. The source dependency guard proves that this changes
no main datum, field, bound, G, exponent factor or outer comparison.
It restores a complete normalized zero, so the selected parent's universal
and chronological theorem applies. An arbitrary positive inverse for the
old ordinary auxiliary tuple is not claimed.

For arbitrary signed assignments the audited strong-map corrections are

    ordinary strong residual=Delta*(1−Ns),
    ordinary auxiliary factor=normalized auxiliary factor
                           +Delta*(Ns−1)*(V²−y²).    (9)

The global shift changes only global_lhs by1 among retained equality-core
registers; G=1 minus the old equality residual. These are exact core
identities. They do not assert whole-polynomial equality across strong
or global treatments.

## 4. All groupings and exact literal costs

Partition the factors of a fixed base into g nonempty disjoint groups,
with product U_j in group j. Retain every ordinary residual R_i and use

    sum_i R_i²+sum_j(U_j−1)²,                          (SOS)
    U_a*(1+sum_i R_i²+sum_(j!=a)(U_j−1)²)−1.          (anchor a)

An integer zero forces all residuals zero and all group products1. Their
product restores the selected base unit equation. Section2 makes every
individual factor+1 on the valid program slice. Conversely, every such
base zero makes every grouping vanish on the identical supplied tuple.
This proves full within-base positive-zero equality, not merely equality
of accepted inputs.

The certificate has c+n−g gates and m+g comparisons. Both finalizers cost

    c+n+3m−1+2g.                                      (10)

Here m≥3, so no empty-residual special case occurs. The table in Section1
follows from the literal cores. Only the one-group normalized anchor
equals its selected385 or386 parent polynomial on arbitrary integers,
by reassociation; general groupings need not.

## 5. Exact finite propagated objective and floors

The normalized equality weights are

    760,1804,416,974,345,345,5,7,14,22,3,3,

with maximum ordinary residual bound7. The ordinary equality weights are

    760,832,416,345,345,5,7,14,22,3,3,

with residual bound690. For each unit variant insert G's weight2 after
the word factors. All degree values come from the emitted graph with the
same two guarded all-integer native/exponent norm cancellations. No
equation valid only at solutions is used to lower a formal degree.

For group weights d_j, SOS has bound2*max(r,d_j); anchor a has
bound d_a+2*max(r,{d_j:j!=a}). The
[subset optimizer](neary_woods_universal_joint_and_coupled_partitions.md)
enumerates each possible anchor subset and solves the least-maximum-group
recurrence on the remainder. Its attained upper bounds and proved pruning
lower bounds give an exact minimum of this finite objective for each
group count. Equation(10) then yields:

|Strong|Global|Nondominated operation / degree bounds|
|---|---|---|
|normalized|unit|385/4714,387/4707,389/3608|
|normalized|equality|386/4712,388/4705,390/3608|
|ordinary|unit|386/4134,388/2900,390/2210,392/1664|
|ordinary|equality|387/4132,389/2900,391/2210,393/1664|

The normalized floor3608 is attained by three SOS groups of weights
1804,1521,1375 for the unit option, or1804,1521,1373 for equality. Its
largest factor forces that SOS floor. An anchor omitting1804 exceeds3608;
one including1804 but omitting974 has bound at least3752; including those
but omitting760 gives at least4298; including all three but omitting416
gives at least4370; including all four has weight at least3954. Adding
G's nonnegative weight cannot invalidate any lower bound.

The ordinary floor1664 is attained by four SOS groups760,832,690,472
with G, or760,832,690,470 without it. An anchor omitting832 exceeds1664;
one containing it has bound at least832+2*690=2212. The receipt separately
checks every nonempty anchor subset:8191,4095,4095 and2047 across the four
bases. The combined floor is1664 at392 operations. It is a floor for this
propagated objective only.

## 6. API and evidence

`base(normalized=True|False,global_unit=True|False)` returns a fresh
canonical scaffold. `grouped(base,partition,anchor)` supports arbitrary
ordered valid partitions and `None` for SOS. `frontier` and `build`
accept either Boolean selector or `None` to combine choices; default
`build(operations=392)` selects the combined frontier. Complete-source,
degree-bound and ledger APIs require full canonical packet equality.
The low-level `degree_dictionary` is a guarded norm-bound propagator,
not a canonical packet validator.

The receipt stores all48 group-count winner ledgers and complete selected
frontier sources with hashes, plus additional nonoptimal ordered plans
and every anchor in a four-group test. Complete source execution is
compared with independently formed group products and finalizers on signed
and positive assignments. Separate strong maps check(9); global maps
check the exact slack shift; normalized full-product outputs are compared
with both literal parent polynomials. Source guards reject changes in
domains, program recipe, codes, ancestry, factors and plans.

Both strong bases are tested on actual source pretyping contexts with
G=±1, including D=1 and Sigma=P, without assuming native Pell zeros or
one-hot selectors. The unchanged optimizer has its own independent small
Bell-enumeration audit. These are finite source/component checks, not
materialized complete compiled Pell witnesses. Full mathematical scope
rests on Sections2–4 and the cited parent proofs.

Author writer35673 and fresh24434 passed on the final four-base source
and receipt. It records48 winner ledgers and14 complete selected sources;
1,088 complete core/group/manual-output checks include544 signed cases.
The two global treatments each have80 strong-map corrections(40 signed)
and80 direct parent-polynomial identities. Another160 full global-slack
core maps include80 signed cases. The432 actual pretyping contexts include
144 at D=1 and216 with G=−1. Twenty-four malformed callers are rejected.
All seven local links resolve.

Root's full proof/source/dependency read and fresh68552 passed with no
findings, including the four source contracts and cross-global/strong
scope. Native's independent full proof/source/dependency review and
fresh99774 also passed with no findings. Its separate subset recurrence
reproduced all48 optimal group-count objectives, four floor certificates,
the six-point frontier and the finite-family floor1664. Its own source
oracle checked56 full degree/opcode/closure ledgers,448 complete
core/group/direct-finalizer maps(224 signed,112 zero-selector cases),
96 strong correction maps(48 signed) and96 global-slack maps(48 signed).
It compared all118 native/exponent and161 pretyping rows for each global
option. Seven local links and whitespace checks passed. These independent
fixtures retain the source/component scope stated above.
