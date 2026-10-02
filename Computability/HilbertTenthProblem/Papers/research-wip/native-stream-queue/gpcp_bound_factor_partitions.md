# Exact factor tradeoffs with signed bounds in the complete U15,2 compiler

The [source](gpcp_bound_factor_partitions.py) and
[receipt](gpcp_bound_factor_partitions.json) optimize a precisely restricted
64-base family built from the [767-operation signed-bound compiler](gpcp_positive_bound_units767.md).
The choices are its two initial-value interfaces, eight normalized/ordinary
strong masks, and four paired-bound switches. All disjoint factor groupings
and SOS/anchor finalizers are considered, subject to one explicit completeness
condition: the geometry index bound factor H_I, when present, shares its group
with another enabled bound factor or the global factor G.

The combined operation / exact formal-polynomial degree frontier is:

|Operations|M|A|Certificate|Comparisons|Witnesses|Degree|Ordinary strong mask|
|---:|---:|---:|---:|---:|---:|---:|---:|
|767|352|415|714|18|125|228339|0|
|768|351|417|712|19|125|154765|4|
|769|350|419|710|20|125|153683|6|
|770|353|417|714|19|126|9484|0|
|771|352|419|712|20|126|7280|4|
|772|351|421|710|21|126|6198|6|
|773|352|421|711|21|126|6156|4|
|774|351|423|709|22|126|5074|6|
|775|352|423|710|22|126|4106|4|
|776|351|425|708|23|126|3384|6|
|777|352|425|709|23|126|3304|4|
|782|351|431|702|27|126|3046|6|

The low three mask bits mark ordinary strong treatment for geometry,
recoder AND and history AND respectively. The first three rows compute the
initial history value; the remaining rows supply it and retain its paid
comparison. All displayed points enable both bound pairs except782, which
enables only the geometry pair. Every source retains three fixed positive
program parameters, ordinary positive input x, the complete fixed U15,2 table,
57 tiles, input recoder, program frame and padding convention.

The computed-initial-only frontier is
767/228339,768/154765,769/153683,770/119410,772/110164,774/101326.
The supplied-initial-only frontier is the770-through782 portion of the table.
The degree floors in these interfaces are101326 and3046 respectively.
These are exact optima only for the64 bases, the stated admissible groupings
and their literal objective. Older stages and other circuits are outside this
claim. The independent75-certificate/87-polynomial bound is unchanged.

The semantic distinctions matter. At fixed strong treatment, the explicit
slack map gives a full positive surjection onto the corresponding unconverted-
bound strong-mask parent, with a positive section. Groupings may have different
supplied positive zeros. Across strong masks, only the outer projection outside
up to15 private auxiliary coordinates agrees; the converse can rebuild five
coordinates per changed core. No full supplied-zero surjection across masks,
arbitrary division of an ordinary strong witness, or off-zero polynomial
identity across bases is claimed.

## 1. The64 complete source contracts

Start with the canonical767 parent for a selected initial interface and its
AND-bound and geometry-bound Boolean switches. `rewrite_base` requires full
packet equality with that parent, including source, domains, program data,
factors, comparisons and semantic metadata. Both switches disabled give the
literal771 base. The actual geometry remains q=x+input_slack, q^64 and
B_geo=2^63*q^64. No alternative geometry is accepted by this interface.

In each of the three native namespaces write A0=a+2, Delta=A0²−1 and t=ic².
The literal register named `A` is Delta. A normalized strong core has

    Q=Delta*t², Ns=f²−Q, K=Delta*Q,
    N3=K*(V²−y²)+y².                                  (1)

For an ordinary bit, remove Ns from the factor list, retain the full comparison

    t²=Delta*(f²−1),                                  (2)

and replace its auxiliary coefficient by Delta*(f²−1). The old Ns register
becomes f²−1, the coefficient row changes, and only the now-private Q row is
deleted. The guard checks all three literal definitions and the exact two
consumers of Q before rewriting. No ratio, first-index, auxiliary linear,
main-root, input padding or chronological comparison is removed.

Current factors and comparisons are rebuilt from the guarded source. Old
claims that all three cores are normalized or all factors are positive are
not copied as current metadata. The remaining normalized strong factors and
ordinary strong comparisons are recorded explicitly. All domains, program
codes, tile order and active history geometry remain the selected parent's.

The checker rebuilds dependencies from actual rows for all15 possible
`f,i,j,o,y_aux` coordinates. Their direct consumers are local. Each auxiliary
norm and linear residual has no other core's auxiliary dependence. Every main
or first-root datum, scale, ratio input, checksum, G, H, program-frame value and
outer comparison is independent of these coordinates, apart from the stated
local auxiliary and strong equations. This is the required simultaneous
extension contract, not an inherited assertion.

Public constructors check strict Boolean and mask types before caching.
Complete-source, degree and ledger APIs reconstruct and require equality with
the complete current packet, including partition order, anchor and companion
rule. Every emitted gate reaches the full polynomial output. No private chain
is counted after its last consumer is removed.

## 2. Ordinary strong treatment with the signed bounds

At any grouped integer zero every group product is1 and every ordinary
comparison holds. Thus every individual factor is an integer unit. The first
and main norms exclude−1 modulo4, independently of either checksum or G.
A retained normalized strong norm has the same sign obstruction. In an ordinary
core, (2) makes the auxiliary coefficient the square t², so its auxiliary norm
also excludes−1 modulo4. Hence all remaining native norms are+1 before any
bound, checksum or global sign is decided.

The unchanged unconditional positive-port proof of767 gives positive native
quantities and F3>=8. In either AND core, C=q_native−sum F_i is an integer unit;
the padded comparisons give F1=4,F2=2,F3=8 modulo16. Therefore the packed index
is r=1 or3 modulo16, whereas X=w*q_native=0 modulo16. An enabled bound H=±1
first gives X−r=beta+H>=0. The residues make this strict, with gap at least15
or13. A disabled bound retains its original strict comparison. No checksum
sign has been used to recover X>r.

For geometry, enabled units initially give only X>=J>=B_geo. The literal
width64 geometry pays B_geo>=2^127 and J>q; disabled bounds are stronger.
Use r=J in that core. With Y=q_native*(2*odd_half+1), E=XY and
P0=2XY²+1>A0, the first and main Pell classifications give

    k=psi_P0(n), n=r+1 modulo E, n>=r+1,
    c=psi_A0(p), p>n,
    c>A0*Delta², c>2p, c>2(2r+1).                      (3)

For the geometry inequalities the weak X>=r is sufficient because r is so
large; for AND, the original strict bound has already been restored. These
are precisely the margins checked by767 and the
[raw geometry proof](native_binary_input_dilation129.md#2-the-raw-geometry-theorem-at-j9-and-jq).
The positive first-root-gap inverse is unchanged.

In a normalized core the established strong divisibility gives pc dividing
its auxiliary index. In an ordinary core the full ordinary rank theorem uses
(2) and c>A0*Delta² to give f=chi_A0(m), c|m, m>=c>2p and
t=Delta*psi_A0(m). These give the same strict signed-index windows. The
retained V=jc−(2r+1)=of−c is positive; its two minus congruences force
p=2r+1. The fixed-minus parity theorem gives r odd. A wrapped first index
n>=r+1+E would exceed p, so n=r+1 exactly.

The ratio-first growth and true main-root congruence now give
X=2^(2r+1), also in the weak geometry case: its lower ratio proves
a>X^(r+1), and X>=r>=8 implies X^(r+1)>2^(2r+1). The exact binomial tail
and odd-scale valuation therefore give q_native=2^popcount(r). The two
negative-checksum contradictions of767 remain valid before a global sign is
known. Both checksums become+1. Every remaining local norm is also+1.
For geometry, X−J>1 and J−B_geo>0 follow, the latter from J odd and B_geo even.
The index gap may still equal1.

Alternatively, once a local main index and its odd r are recovered, that
ordinary core can be normalized immediately by the construction in Section3.
This restores a full normalized767 tuple without presuming a checksum or
G sign, and then the reviewed767 proof supplies its remaining conclusions.
Both routes preserve all non-auxiliary data.

## 3. Exact scope of the strong maps

At a normalized zero, set i_ordinary=Delta*i_normalized and retain every other
coordinate. Equation(2) holds, its auxiliary coefficient and norm retain their
values, and the removed normalized strong factor was1. This gives a positive
ordinary zero, even when some bound or global signs are negative.

At an ordinary zero keep the local main data, let J0=2r+1=3 modulo4 and
c=psi_A0(J0), and use the canonical construction from the
[three-core normalization proof](gpcp_normalized_strong_compiler.md#3-a-positive-converse-with-fifteen-fresh-auxiliaries):

    m=2cJ0, f=chi_A0(m), i=psi_A0(m)/c²,
    T=Delta*psi_A0(m), y=psi_T(J0), V=chi_T(J0)/T,
    j=(V+J0)/c, o=(V+c)/f.                             (4)

Multiple-index divisibility and the odd quotient congruences make all five
strictly positive integers. They restore the normalized strong and auxiliary
norms and the retained linear equation. Section1's literal dependency guard
makes the constructions independent across the three cores, changing none of
the bounds, signs, ratios, fields, checksums, transport or program data.

This proves equality of the outer projections across masks. It does not
recover an arbitrary original normalized five-coordinate tuple, nor assert
that every ordinary i is divisible by Delta. For signed algebraic checks the
actual correction identities under the forward map are

    ordinary strong residual=Delta*(1−Ns),
    ordinary N3−normalized N3=Delta*(Ns−1)*(V²−y²).     (5)

They are not identities of the two complete polynomials.

## 4. Signed bounds, projections and the companion condition

Let H_i be each enabled native bound, with its private beta_i, and retain
G=P_history−Sigma−beta_global. After native signs and checksums are recovered,
the complete product implies only G*product H_i=1. Individual signs need not
be positive. The767 proof derives the original strict native gaps and typed
history bound without assuming these signs. Thus its formal slack projection
is positive on grouped zeros:

    beta_i,parent=beta_i,new+H_i,
    beta_global,parent=beta_global,new+G−1.            (6)

It targets the corresponding unconverted-bound771 strong mask at the same
interface. In particular G_parent=1. The typed history margin
P_history−Sigma>1 ensures the global coordinate in(6) is positive, including
G=−1. The ordinary strong comparisons and all other coordinates retain their
values. The full parent norm/checksum/global product is1.

Every partition is sound by this argument, but a positive section preserving
the parent outer data needs a sign choice for each separate group. At a
parent zero let d_i be an original bound gap. A desired sign H_i=e_i uses

    beta_i,new=d_i−e_i.                               (7)

Both signs are positive for the two AND X bounds and geometry X bound, since
their parent gaps exceed1. For a desired sign G=g use

    beta_global,new=beta_global,parent+1−g;            (8)

both signs are always positive. However the geometry index gap can be1. At
that boundary H_I=+1 would make its new beta zero, while H_I=−1 is always
available. This is an actual geometry possibility, as documented in767;
it cannot be excluded by choosing an uncharged strict margin.

Require the group containing H_I to contain one enabled other H or G. Choose
H_I and one such companion at sign−1; choose every other flexible sign+1.
All remaining factors are already+1. Every group product is then1, all the
slacks (7)–(8) are positive, and projection(6) returns the exact parent tuple.
If H_I is absent, choose all flexible signs+1. The API implements these sections
and rejects partitions that violate the companion rule.

This proves a full positive surjection and right inverse at fixed strong mask.
In the special fixed-mask setting, different admissible groupings retain a
common parent projection, but their supplied zero sets need not be equal.
Combined with Section3 it proves the same ordinary-input universal projection
throughout the64 bases, retaining the actual program recipes.

The condition is not claimed necessary for accepted-input universality. It is
necessary for this uniform sign-only section at the gap-one outer datum: a
group with H_I and only forced+1 factors would force H_I=+1. A different padding
or outer-reconstruction theorem would be needed to include excluded groupings.
No such theorem or unconstrained-factor optimum is assumed here.

## 5. Literal costs and exact polynomial degrees

Let k be the number of ordinary strong bits, h the number of enabled bound
units (0,2 or4), and t=0 for computed initial value or1 for supplied initial
value. The factor core, factor count and original ordinary-comparison count are

    c=692−k+h, n=15−k+h, m=21+t+k−h.                  (9)

At g groups both finalizers cost

    c+n+3m−1+2g = 769+3t+k−h+2g.                     (10)

This charges all fixed-numeral products, group products, residuals and the
finalizer. An ordinary bit deletes exactly its private Q multiplication,
removes one factor and adds one ordinary comparison. The literal graph count
verifies(9)–(10) for every emitted winner.

The guarded degree propagator rechecks the three main-norm expansions from
the actual current rows. All their other terms have strictly lower degree than
2ac*gamma*(4a+3). Every other row uses its literal operation. Ordinary strong
replacements use the actual degree of Delta*(f²−1), not a zero-set substitution.
The new bound factors retain the strict highest forms proved by767.

An explicit modular evaluation certifies that each factor's highest homogeneous
form and a highest-degree original residual are nonzero. Each full output also
has a nonzero highest-form evaluation. These certify exact formal-polynomial
degrees with all supplied coordinates and symbolic program parameters assigned
degree1, before specializing a program slice. A fixed program can have a lower
degree. The evaluation is a proof of nonvanishing of an integer polynomial;
it does not use a finite-field zero as a substitute for a positive integer zero.

Write d_i for factor degrees, r for the largest original residual degree, and
w_j=sum_(i in group j)d_i. Then the exact output degrees are

    SOS: 2*max(r,w_1,...,w_g),
    anchor a: w_a+2*max(r,{w_j:j!=a}).                 (11)

Products of nonzero leading forms are nonzero, and a nonempty real sum of
squares has a nonzero leading form at its maximal degree. These facts justify
the objective for every admissible partition, not only the displayed winners.

## 6. Exhaustive companion-constrained optimization

If H_I is present, every permitted partition has some eligible companion b in
its group. Contract {H_I,b} to an atom of their summed weight. Unrestricted
partitions of these atoms expand to exactly the partitions containing that
pair. The union over all eligible b is exactly the permitted family. Every
anchor position and group weight is preserved; after expanding, the literal
cost still uses the original n factors in(10).

The implementation evaluates the equivalent direct subset recurrence.
`opt(S,g)` is the least possible maximum group weight over g legal nonempty
groups partitioning S. A legal block either omits H_I or contains an eligible
companion. A subproblem containing H_I without any companion is infeasible;
with H_I it can have at most|S|−1 groups. Every first block containing the least
bit is enumerated, and its complement is optimized recursively. This removes
only the symmetry of group order. All possible legal anchor subsets are then
considered using the same exact recurrence on their complements.

A feasible greedy upper bound first contracts H_I with an available companion.
Lower bounds use the largest factor, ceiling(total/g), and the compulsory
H_I-plus-lightest-companion weight when H_I remains. Pruning uses only these
valid lower bounds and strict-improvement comparisons. Thus it preserves the
exact minima established by the recurrence; the contraction equivalence
explains precisely which finite family is exhausted.

For an unlimited number of groups, all factors may be singletons except H_I,
which is paired with its lightest available companion. Their maximal weight
is exact. Enumerating every legal anchor and applying this rule to its
complement proves the stored floor certificate. Each floor is checked attained
by a computed group-count winner. There are960 such optimal records over the
64 bases: all group counts through n, or through n−1 when H_I is present.
The minima of the two interfaces are exactly those stated above.

No older checksum stage, unsupported code permutation, other base rewrite,
illegal companion grouping or different finalizer is included in this optimum.

## 7. Reproducible evidence and limits

Default execution recomputes the complete receipt; `--write` regenerates it.
All960 winners have literal operation, degree and full output-liveness checks.
Distinct frontier sources are stored in full. The checker also exercises each
of the64 bases with positive and signed exact integer assignments, verifies the
whole grouped output by an independent factor formula, and checks every retained
parent register under(6) and all local strong corrections(5).

At arbitrary tuples, the ungrouped complete products satisfy

    F_bound+1 = G*product H_i*(F_parent(projected)+1),   (12)

because the formal projection makes every removed bound residual zero and
G_parent exactly1. This is a checked off-zero identity; the positivity claims
remain restricted to zeros. It is not asserted for two arbitrary grouped
finalizers. Their individual complete outputs are checked directly instead.

Small cases independently enumerate set partitions and every SOS/anchor choice
to validate the constrained objective. Separate abstract slack/sign checks
include the gap-one H_I boundary and both G branches. Malformed canonical
parents, masks, partitions, companions, metadata, degree callers and map callers
are rejected. Finite assignments and abstract sign fixtures do not materialize
full compiled Pell zeros. Universality follows from the positive projections,
sections and the reviewed complete parent, not from these fixtures.

Author writer8734 and fresh34163 passed with the same source and receipt.
They cover960 optimal literal ledgers and15 saved full sources. The64 base
fixtures and15 selected-source fixture sets together check376 complete grouped
outputs,376 fixed-mask slack projections and376 strong correction maps,
with188 signed assignments and79 zero-selector contexts. Independent small
enumeration checks28 contexts,16,205 legal partitions and78,809 objectives.
The sign audit checks580 admissible partitions and15,660 positive sections,
including349 excluded gap-one cases. All37 malformed callers are rejected;
five local links and source/note whitespace checks pass.

Substrates independently reviewed the full proof, source, dependencies,
degrees and exact DP; fresh11209 passed with no findings. Its separate audit
checked all960 degree/opcode/liveness ledgers,128 nonzero leading certificates
over two primes across64 bases, all15 saved sources,128 complete SOS/slack/
strong maps(64 signed),60 additional selected manual outputs(30 signed),
64 zero-selector contexts and all three frontier filters. Its earlier
independent restricted-growth enumeration checked35 new weight contexts,
18,997 legal partitions and92,162 SOS/anchor objectives;929 sign-capacity cases,
3,480 positive sections and64 dependency contracts also passed. The public DP
matches that independently tested recurrence. All five local links and
whitespace checks passed. No source or receipt change was required.

Root independently read the full proof, source, dependencies and constrained
DP; fresh86125 passed with no findings. The final source and receipt remain
unchanged from the author and Substrates replays.
