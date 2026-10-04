# One positive coordinate for each balanced high quotient

The complete fixed-table source retains **2,462=1,124M+1,338A operations** and exact degree **35,587**, while reducing the positive witness count from150 to **146**. The diagnostic remains302=126M+176A operations and degree1,363, with51 rather than55 positive witnesses. This is a witness reduction, not a new operation bound.

Each of the four signed high quotients in the frozen [balanced-output source](matrix193_balanced_output_scout.md) is replaced by one positive hat minus an already paid half-scale. Every other source row and the full paid finalizer remain literal. The source, receipt and this proof are separate new artifacts; no frozen predecessor is changed.

The fixed-program recipe, ordinary input, controller, physical selection lanes, native kernel and eight fixed coefficient ports are unchanged. Arbitrary coefficient assignments and the small diagnostic are not asserted to define universal programs. The established universal84 bound is unchanged.

## 1. Exact source edit and the inherited interface

The helper authenticates nine predecessor artifacts as inert text or JSON. The immediate parent trio has hashes:

| Artifact | SHA-256 |
|---|---|
| matrix193_balanced_output_scout.py | e567a5be0cb656dfc984aa86fb306584dd837b7c24568659af222c781266d76a |
| matrix193_balanced_output_scout.json | 63a4b6b269ba177603cbebec51848bc6fbcd3c04115bb3dbb367dd63a2f7c9bf |
| matrix193_balanced_output_scout.md | cfc892b2c7a577d2348c3583d968e04ab271f065003cc0bfa6316a9f05f3abde |

The remaining pins are the three packed-output artifacts, atomic JSON and proof, and marked-loader JSON. All nine exact hashes are saved in the new source and receipt. No predecessor Python is executed or imported; the fresh standalone helper uses copied source text plus the explicit new arithmetic and new structural checks.

Recall the actual positive packing interface

    D=x+Hfix+height_slack, c0=D-1, B=K*D,
    E_e=edge_hat_e-1, J=sum_e E_e,
    P=(B-1)J+1, Q=C*P.

C is the fixed even numeral2^93 for the actual table and16 for the diagnostic. Each fixed selected block has length l, with l=144 or194 in the actual array and l=2 in the diagnostic. The source already pays

    T=Q^(l-1), Qhalf=(C/2)*P, T_half=Qhalf*Q^(l-2).

Thus T_half=T/2 is an exact polynomial identity over every commutative ring; the source does not use division. On every positive supplied tuple with the valid coefficient recipe, J>=0, P>=1 and Q>=C, so T_half is a strictly positive integer even before imposing any zero equation.

For each of the four products the sole changed row is

    old: high=high_positive-high_negative,
    new: high=high_hat-T_half.

The old two positive ports disappear and one new positive port is supplied. All four rows remain paid subtractions. No upper-bound comparison on high_hat is added. The literal source reconstruction in the receipt checks that these are the only four row changes, that the exact supplied-port difference is as stated, and that every native cut, comparison-wire pair and final output wire is retained.

## 2. The high tail has the required two-sided bound

The balanced parent's soundness proof first forces its twenty comparisons through the integer finalizer. Block and global positive bounds then permit the native bootstrap and joined AND, independently of any signed extraction equation. After one-hot typing, its selected signed words satisfy

    U_r=Z_r-c0*S_group(r),  |U_r|<=D*J<P.

The centered block and reversed coefficient polynomial expand as

    U_block=sum_(r=0)^(l-1) U_r Q^r,
    A_j(Q)=sum_(r=0)^(l-1) a_(j,r)Q^(l-1-r),
    F_j=A_j(Q)*U_block=sum_(h=0)^(2l-2) c_h Q^h.

The fixed choice C>2M_block*l and |a_(j,r)|<M_block imply |c_h|<Q/2. Integrality and even Q therefore give |c_h|<=Q/2-1.

The middle extraction has the form

    F_j=low+T*(dot+Q*high),
    high=sum_(h=l)^(2l-2) c_h Q^(h-l).

There are l-1 terms in high, with exponents0 through l-2, exactly as in the already bounded low tail. Hence

    |high| <= (Q/2-1)*(T-1)/(Q-1) < T/2=T_half.         (1)

This is a bound on the entire signed integer quotient, not just its coefficients. It holds for every typed positive parent zero, including negative products, negative quotients and zero selected blocks. The parent's paid open bounds on low and dot make their two-stage decomposition unique; after these terms are fixed, its high difference is necessarily the quotient in (1). The freedom to shift both old high ports by the same amount does not change that difference.

## 3. Full all-ring pullback and positive zero equivalence

Let F_new and F_old denote the complete polynomials. Keep every common supplied coordinate and make, separately for each product, the substitution

    high_positive=high_hat, high_negative=T_half.

Every retained producer agrees, including the changed high wire. Thus over every commutative ring,

    F_new=F_old(high_positive=high_hat,
                high_negative=paid T_half).             (2)

The half-scale depends only on retained packing ports and not on any changed high coordinate. This is a complete polynomial pullback, not merely a zero-set identity.

On the positive source domain both substituted parent ports in (2) are positive. Therefore every positive new zero maps directly to a positive balanced-parent zero before any new appeal to typing or quotient bounds. Its ordinary-input soundness follows from the already proved parent theorem on the same valid fixed-program slice.

Conversely, at any positive parent zero put

    high_hat=high_positive-high_negative+T_half.         (3)

The full bound (1) proves this is a strictly positive integer, indeed less than T. All other supplied coordinates are kept. Formula(3) reproduces exactly the old high value, hence all retained rows and the complete finalizer vanish. There is no need to retain the old unrestricted high-pair offset.

Consequently the full positive zero sets have the same projection to every common supplied coordinate other than the changed high coordinates. Here, unlike the previous packed-to-balanced transition, the low/dot positive ports and their slacks **are** retained: their definitions are unchanged. Both block hats/slacks, every native witness, input, fixed coefficient, state/edge port, height/global slack, terminal field and population quotient are retained as well. The comparison excludes the old high_positive/high_negative ports and the new high_hat ports. It is not a bijection of full witness tuples because the old high-pair common offset is free.

This exact transfer inherits all ordinary-input and native positivity conclusions. In particular x=0, absent LOADs and an empty TILE word retain the parent's conventions; the mandatory SWITCH still gives a nonempty physical history. A zero high quotient uses high_hat=T_half>0. Strictly positive ordinary input is the restriction x>0. Completeness does not require recomputing native witnesses when starting from a parent zero, since all native cuts remain identical.

## 4. Exact degree despite the new tie

The native packing functions and all native factors are unchanged. Their exact degree sum remains34,039 for the actual source and1,351 for the diagnostic, with the same all-value main-norm cancellation as in the parent.

Count every supplied coordinate and ordinary x as degree one, and the valid fixed program coefficients as degree zero. Write D_top=x+height_slack and J_top=sum_e edge_hat_e. Then

    Q_top=C*K*D_top*J_top, c0_top=D_top.

For a block of length l, let S_last_top be the last group's selector leader and let a0 be the first coefficient of its reversed polynomial. The centered block has leader -D_top*S_last_top*Q_top^(l-1). The left extraction product therefore has leader

    -a0*D_top*S_last_top*Q_top^(2l-2)

at degree4l-2, with a zero contribution understood when a0=0.

The new high subtraction also contributes at degree4l-2 on the right: -T*Q*T_half has leader -Q_top^(2l-1)/2. All its other terms, and all low/dot terms, have lower degree. Hence the full left-minus-right extraction residual has leader

    D_top*Q_top^(2l-2)
       * ((C*K/2)*J_top-a0*S_last_top).                 (4)

This expression cannot vanish identically on any valid fixed-program slice. In both complete arrays the SWITCH edge is present in J_top and absent from each fixed block's last selector. Its coefficient in the bracket is C*K/2, a nonzero fixed number. The other factors are also nonzero polynomials. This argument handles the degree tie without a zero-set substitution or an assumption about the sign of a0.

Thus each block has an extraction residual of exact degree4l-2. The longest actual length194 gives degree774. Every other comparison has degree no greater than774, and the real sum of squared residuals has exact degree1,548. Multiplying by the unchanged nonzero native product and subtracting1 gives exact degree34,039+1,548=35,587. For l=2 the same argument gives residual degree6, SOS degree12 and total1,351+12=1,363.

## 5. Full ledger and a checked neutral reassociation

| Complete source | Packing | Native | Outer producers | Finalizer | M | A | Total | Positive witnesses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Diagnostic |93|63|84|62|126|176|302|51|
| Actual fixed table |896|63|1,441|62|1,124|1,338|2,462|146|

The number of comparisons remains twenty. All source rows and free ports are live. There are no new literals; the actual array still uses684 distinct integer literals with maximum absolute value C=2^93. The four removed high-negative ports account for the complete witness reduction.

A related shared-offset reassociation does not save operations in its direct schedule. For a pair of products of the same length, with dot already needed by the history equations, write

    offset=T_half*(1+Q^l),
    RHS=low_positive+T*dot+Q^l*high_hat-offset.

T,Q^l and T_half are already paid. Per block the current two right sides, including their private low/high subtractions but excluding the retained dot producers, cost4M+8A. The alternative pair costs4M+6A plus1M+1A for its shared offset, namely5M+7A. Both totals are twelve operations. Omitting the paid offset would falsely suggest a saving. This is only a comparison of these two explicit local schedules, not an optimality or arbitrary-circuit lower bound. The emitted complete source keeps the simpler literal four-row change.

## 6. Fresh verification and its limits

The standalone helper emits both entire sources and authenticates the full four-row predecessor relation, exact witness change, retained native cuts and comparisons. It checks dependency order, all-row/all-port liveness, complete operation counts and fixed coefficient recipes. Its output contains its own source SHA-256 and all nine dependency hashes. JSON parsing rejects duplicate keys, and exact receipt comparison is recursive and type-exact.

Thirty-two complete modular source evaluations agree with separately written direct formulas. Ten diagnostic histories, x=0 through4 with zero or two IDLEs, are evaluated through all literal nonnative rows. A complete dense diagnostic specialization has exact degree1,363 with leading coefficient579,573,152 modulo1,000,000,007. These finite calculations support the source implementation; the uniform degree theorem is Section4.

The2,992 finite signed-convolution checks now verify the strict **high**-tail bound as well as low/middle bounds and positive high_hat. They include1,032 negative high quotients and280 zero products. These are arithmetic components, not compiler histories.

The saved83-TILE plus SWITCH trajectory is freshly reconstructed. Its four signed decompositions, twenty mathematical outer comparisons, positive supplied outer witnesses, positive native input fields and joined AND all check. Two products and two high quotients are negative. Its packing digest remains exactly `69354b5e33fc40c1990a31713d5ae17b53265374f1590b2ae26b6082f983f610`, and all ten diagnostic packing digests match the balanced parent. The large fixture is the illustrative x=0 context; it is not a numerical universal-program instance. Its enormous literal outer DAG is not reevaluated with giant integers, and no full native Pell tuple is materialized. The full modular DAG checks and the exact mathematical fixture have these distinct scopes.

Run the new helper from any directory with `--root` set to the absolute native-stream-queue path and `--expect` set to this receipt; `--output` writes a deterministic receipt. Normal and optimized replay checks remain active through explicit exceptions. Fresh normal and optimized exact replays from `/` both pass.
