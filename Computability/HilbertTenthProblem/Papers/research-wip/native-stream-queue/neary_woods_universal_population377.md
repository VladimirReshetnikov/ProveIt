# Combining the explicit U9 reductions: 377 operations

The complete source now gives one fixed universal polynomial in
**377=183M+194A operations**, with **66 positive existential witnesses**,
**20 comparisons** and four positive program parameters besides the
ordinary positive input x. The certificate costs **318=163M+155A**.
Its total degree is **at most 2285**, including all program coordinates.
Keeping the history checksum separate gives **379 operations at degree
at most2241**, with the same66 witnesses and21 comparisons.

The [source](neary_woods_universal_population377.py) and
[receipt](neary_woods_universal_population377.json) compose three reviewed
changes to the [389-operation parent](neary_woods_universal_population_projection389.md).
The separate best established universal bounds remain75 certificate
operations and [87 polynomial operations](complete75_normalized_strong87.md).
No exact degree, optimal circuit or formalization claim is made here.

## 1. Composition of the three proofs

First apply the [joint scale bound](neary_woods_universal_population_joint_bound386.md).
Replace Q=q+power_gap and z+output_slack=Q with Q=q+z+g.
Both blocks have two additions. Restore the parent's supplied gaps as

    power_gap_old=z+g, output_slack_old=q+g.

This lift is positive on every positive supplied tuple. At a parent
zero the complete recoder theorem gives q=2^n, Q=q^D and
z<= (Q-1)/(2^D-1), where the actual fixed D>=3. Thus q<=Q/4 and
z<Q/7, proving the inverse g=Q-q-z positive. The transformation
preserves positive zero sets bijectively and saves one witness and one
comparison, hence **1M+2A** in the complete polynomial.

Next apply the [shared history arithmetic](neary_woods_universal_shared_history382.md).
The history already computes P2,P3,P6,P7, T=H_U+P*H_V and two disjoint
selector-hat sums. It can compute

    P9=P7*P2, P11=P9*P2,
    Hb=T+P2*H_V,
    sum_i Shat_i=(Shat1+Shat2)+(Shat0+Shat3).

These identities save **5M+2A**, shorten raw history161 to154 and leave
every residual and the whole output polynomial identical on all integer
assignments. The rewrite changes no witness, comparison, scale,
selected-history interpretation or counter rule.

These first two changes compose without an additional hypothesis.
The joint bound changes only the two recoder scale-bound rows; the
history rewrite checks and changes its own private rows. Its public
history expressions and native scale P^11 have identical values. The
source checks both rewrite orders and emits the resulting complete
379-operation polynomial. This form already inherits the full ordinary
input and universal program theorem through the positive bijection.

Finally apply the [padded checksum sign theorem](neary_woods_universal_population_checksum387.md).
Let C be the history checksum and U the previous unit product. Replace
the separate comparison C=1 by one extra factor C in U. The remaining
outer comparisons and all sign-safe norm factors hold at a new zero.
If C=-1, positive fields satisfy sum Fi=q_history+1 and Fi<q_history;
the raw native kernel therefore recovers

    q_history=2^m, popcount(r_history)=m.

The unchanged four-bit padding forces field residues(3,4,2,8) modulo16.
Their low population5 and high-part sum2^(m-4)-1 instead give
popcount(r_history)>=m+1, a contradiction. This uses only the restored
native equations and positive bounds, before invoking the full AND
interpretation. Hence C=1, and the other checksum is also1 from the
product. The new and old positive zero sets on the same coordinates
are identical. Adding one multiplication and removing one residual
subtraction, square and sum gives a net saving of **2A**.

The history identity preserves every expression needed by this sign
proof, including q_history>=16 and F3>=8 on all positive supplied
tuples. The joint scale lift likewise retains a positive initial tag
sentinel and the unchanged positive history domain. Thus all three
proofs apply in the stated order, giving **389-3-7-2=377**.

## 2. Fixed ordinary-input universality

The actual machine remains the original1968-state U9-derived binary
clockwise table, with CTS half-length z_CTS=59101, period118202,
binary tag parameter beta=1182020 and fixed data width

    D=47946621298704238734708993009920.

All eleven fixed-numeral roles retain the exact parent recipes. The
four positive program values A_S,B_S,T_S,E_S are fixed per recursively
enumerable set S. The sentinel E_S dominates the fixed physical tape
overhead; the actual dyadic duration n exceeds it. The physical input
still has64n+b_S cells and exact least dyadic counter128n. The valid
U9 input slice has at least six persistent A symbols, the DATA ordering
is positive and the selected history remains chronological and complete.
Arbitrarily long leading-zero padding supplies the original completeness
argument for every ordinary positive input x in S.

Consequently the fixed emitted polynomial F satisfies

    x in S iff exists y_1,...,y_66>0:
    F(x,A_S,B_S,T_S,E_S,y_1,...,y_66)=0.

These changes neither require arbitrary parameter tuples to be valid
programs nor weaken the actual simulator's counter initialization.
The witnesses remain complete positive native extensions supplied by
the parent theorem and the proved coordinate maps. They are not giant
numerical objects materialized in the finite checker.

## 3. Counts and degree alternatives

| Form, J/Ahat projected | Certificate | Comparisons | Positive witnesses | Polynomial | Degree upper bound |
|---|---:|---:|---:|---:|---:|
| Raw SOS, no unit merge |302|52|85|457|544|
| Native units, separate checksum |311|24|66|382|1405|
| Native units, merged checksum |312|23|66|380|1449|
| Normalized, separate checksum |317|21|66|379=183M+196A|2241|
| Normalized, merged checksum |318|20|66|**377=183M+194A**|**2285**|

The normalized projected-coordinate alternatives are also retained:

| Projected coordinates | Separate checksum: operations / witnesses / degree bound | Merged checksum: operations / witnesses / degree bound |
|---|---:|---:|
| Neither |385 /68 /2204|383 /68 /2248|
| Ahat only |382 /67 /2206|380 /67 /2250|
| J only |382 /67 /2239|380 /67 /2283|
| J and Ahat |379 /66 /2241|377 /66 /2285|

The Ahat-only entry has the better degree bound at the shared operation
count. These are reproducible tradeoffs, not a proof of optimality.
Both duration-bound interfaces have the same counts; the default uses
four program values, while the optional independent duration bound is
a fifth parameter. The 40 ledgers cover all three forms, both interfaces,
four coordinate choices and both checksum settings where applicable.

Q remains degree one under the joint scale bound. Exact history
identities preserve the output degree; guarded propagation over the
shorter DAG also reproduces the parent upper bounds. The added history
checksum has degree at most44, so its merger raises the product bound
by44 while the previous residual maximum stays a valid upper bound.
For the default the product has degree at most1955, its largest residual
at most165, and1955+2*165=2285. No leading-coefficient noncancellation
is asserted.

## 4. Whole-source verification and audit interfaces

The writer and fresh default compare 640 complete original/final output
identities or corrections,320 signed and320 positive, using a separate
straight-line evaluator. The original389 coordinates are restored
directly from q,z,g. Every shared certificate register is compared except
the deliberately changed private history V-region register; the removed
output-bound residual is zero. An additional640 complete evaluations
compare the opposite order of the joint-bound and history rewrites.

For the separate-checksum forms the old and new complete outputs agree
exactly under the positive lift. For merged forms they obey the exact
correction, with S the sum of squares of the remaining residuals,

    F_389(L(y))-F_377(y)=U*(C-1)*(C-2-S).

The sign theorem, not an off-zero identity, proves the final equality of
positive zero sets. Each fixed-numeral role receives one consistent
finite value through all compared DAGs. These formal substitutions do
not reproduce all cross-role identities of the actual enormous fixed
coefficients. Positive cases use recoder radix4 and mask7, and verify
the coordinate lifts and the history positivity bounds explicitly.

The saved `complete_parent389`, `joint_scale_parent`, `arithmetic_parent`
and `checksum_parent` identify the distinct proof stages. Older unit or
projection audit functions must receive the appropriate restored parent
coordinates and source. The combined checker does not pretend that
historical metadata automatically accepts the changed gap interface.

```sh
python3 neary_woods_universal_population377.py
```

Author writer, fresh default and source/proof checks pass. Native and
reduction reviewers independently passed the final proof/source/fresh
replay with no findings. Their separate audits add160 and320 complete
original-to-combined identities/corrections respectively,80 and160 signed.
Native also checked144 named-DAG commutations across every applicable
rewrite order, including all six orders with the checksum; the reduction
reviewer checked320 checksum-first output comparisons. All local links
resolve. Root additionally verified that every one of the377 arithmetic
gates is an ancestor of the final output: no counted dead gate remains.
