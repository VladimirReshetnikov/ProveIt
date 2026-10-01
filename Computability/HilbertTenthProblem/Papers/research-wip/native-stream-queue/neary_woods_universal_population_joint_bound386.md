# Joining two scale bounds: an explicit 386-operation universal polynomial

The [389-operation U9 construction](neary_woods_universal_population_projection389.md)
can combine its two positive bounds on the recoder scale Q. The result
is one fixed universal polynomial using **386=188M+198A operations**,
**66 positive existential witnesses**,21 comparisons and four positive
program parameters besides the ordinary positive input x. The certificate
still costs **324=167M+157A operations**. The total degree remains
**at most2241**, including all program coordinates.

The ordinary input, actual fixed U9 machine, production and all eleven
fixed-numeral roles are unchanged. The separate best established
universal bound remains [87 operations](complete75_normalized_strong87.md).
The [source](neary_woods_universal_population_joint_bound386.py) and
[receipt](neary_woods_universal_population_joint_bound386.json) include
the complete386-gate DAG and its source/output audit. No exact-degree
claim is made.

## 1. The two bounds and their shared positive gap

In the parent, write q for the outer recoder parameter. It is supplied
in the raw form and computed as x+input_slack in the two projected
forms. The parent has the source rows and comparison

    Q=q+power_gap,
    output_bound=z+output_slack,
    output_bound=Q.                                (1)

The supplied z is the spread output. Both gaps are positive supplied
coordinates. In the new source retain the name `power_gap` for a new
positive coordinate g, and replace(1) by

    joined_scale_floor=q+z,
    Q=joined_scale_floor+g.                        (2)

Delete only the old `output_slack` coordinate and its comparison.
Both circuits use two additions in this block, so the certificate
cost is unchanged. The comparison and one witness disappear.

The new Q depends on the supplied z, but z does not depend on Q.
Neither the raw q nor the computed x+input_slack depends on z or g.
There is therefore no cycle. The source audits every old use of both
slacks: `power_gap` occurs only in Q, and `output_slack` only in its
private addition. The old output-bound register occurs only in its
comparison. No public register, other comparison or norm factor is
silently discarded. A stable topological sort restores source order.

## 2. Exact positive lift and the converse inequality

For every new positive supplied tuple, restore the two old coordinates
by

    power_gap_old=z+g,
    output_slack_old=q+g.                          (3)

Both are positive without assuming any comparison, native typing or
valid program. The old value of Q becomes q+z+g, precisely the new Q,
and its old output bound becomes z+q+g=Q. Every other supplied coordinate
is unchanged.

For the inverse direction, use the actual full parent recoder theorem.
At every positive parent zero, including zeros with arbitrary positive
program parameters, that theorem gives

    q=2^n,  Q=q^D,  n>=2,
    z=spread_D(x),  0<x<q,
    0<z<=(Q-1)/(2^D-1),                           (4)
    D=47946621298704238734708993009920.

Only D>=3 and q>=2 are needed for the following estimate:

    q/Q=q^(1-D)<=1/4,
    z<Q/(2^D-1)<=Q/7.

Thus

    q+z < 11Q/28 < Q,
    g=Q-q-z > 17Q/28 > 0.                         (5)

The restored coordinate is an integer, since all three terms are
integers. The old comparisons force power_gap_old=Q-q and
output_slack_old=Q-z, so(3) recovers both of them from(5). Hence
restoration and deletion/reparameterization are inverse on positive
zero sets, with every input and program parameter fixed.

This converse deliberately uses the full parent theorem. The new gap
need not be positive on an arbitrary old positive tuple: q=2,Q=3,z=2
satisfies both individual strict bounds in(1), but Q-q-z=-1. Such a
tuple cannot satisfy(4). No claim is made that the two unrestricted
positive coordinate domains are in bijection.

There is no circular use of (4) in soundness. A new positive zero first
lifts by the unconditionally positive formulas(3) to the unchanged
parent source. Its established theorem then applies. Conversely, an
old positive zero already satisfies(4), which proves(5) before the
new gap is chosen. This order applies to the raw, unit and normalized
forms separately.

## 3. Complete polynomial identity and universal input contract

For any integer assignment to the new supplied coordinates, allow(3)
to take arbitrary signs. Induction through the two certificate DAGs
shows that every shared register has the same value. The only deleted
residual, output_bound-Q, is identically zero. All other comparisons
and every factor in the safe unit product agree. Therefore, for each
of the three finalizers,

    P_new(y)=P_parent(L(y))                         (6)

as an exact integer polynomial identity under the lift L in(3).
The new packet records the full unmodified source as `joint_scale_parent`.
Older projection/unit audit interfaces must receive the restored parent
coordinates; the changed meaning of `power_gap` is explicit in metadata.

For a positive new zero, (3) and(6) give a positive parent zero. For a
positive parent zero, (5) defines the inverse positive gap and(6) gives
a new zero. This proves a positive zero-set bijection for each complete
form, not merely a same-language implication. It preserves the exact
recoder output and actual duration. The independent history checksum,
all thirteen normalized unit factors, both native ratio slacks and
all strong relations remain untouched.

The parent ordinary-input universality theorem therefore transfers
directly. For every r.e. subset S of the positive integers it supplies
four fixed positive parameters A_S,B_S,T_S,E_S. The sentinel E_S forces
the dyadic duration n above the fixed U9 physical overhead b_S; the
exact initial tape has64n+b_S cells and its least dyadic counter is128n.
The same paid loader and independent selected history prove halting of
the same actual fixed production. The valid U9 slice still has at least
six A symbols, and arbitrarily long leading-zero padding gives
completeness for ordinary x.

Consequently the emitted fixed polynomial F satisfies

    x in S iff there exist y_1,...,y_66>0 such that
    F(x,A_S,B_S,T_S,E_S,y_1,...,y_66)=0.

The program parameters are fixed per S and are not counted as positive
existential witnesses. No malformed-parameter simulation claim is
needed. The fixed numerals retain exactly the same recipes and degree
zero; every use remains a charged source operation.

## 4. Literal counts and degree alternatives

There is no certificate cost change. Removing one comparison removes
one residual subtraction, one square and one sum addition from each
finalizer, saving **1M+2A**, with one fewer positive witness.

| Form, both earlier coordinate projections | Certificate operations | Comparisons | Positive witnesses | Polynomial operations | Degree upper bound |
|---|---:|---:|---:|---:|---:|
| Raw SOS |309|52|85|464=204M+260A|544|
| Native units |318|24|66|389=185M+204A|1405|
| Three normalized strong units |324|21|66|**386=188M+198A**|**2241**|

The optional independent fifth duration-bound parameter has the same
counts. The source also retains all four choices of the earlier J/Ahat
projections, giving these normalized alternatives:

| Earlier projected coordinates | Polynomial operations | Positive witnesses | Degree upper bound |
|---|---:|---:|---:|
| Neither |392|68|2204|
| Ahat only |389|67|2206|
| J only |389|67|2239|
| J and Ahat |386|66|2241|

The J-only choice is retained for reproducibility; Ahat-only has the
better degree bound at the same cost. In every choice Q remains degree
one because q,z,g all have degree one. The new floor also has degree
one. The source reruns the parent's guarded degree propagation over
the actual changed DAG. Every downstream degree bound is unchanged;
for the default normalized form the product bound1911 and largest
outer residual bound165 give1911+2*165=2241. These are conservative
upper bounds, not assertions about nonzero leading coefficients.

The two additions formerly belonged to separate bounds. Metadata now
records three width-constraint operations for Q=q+z+g and the existing
mask multiplication R=(2^D-1)J, rather than retaining the old two-gate
width entry. The global certificate ledger stays unchanged because
the output-bound addition has been reused, not duplicated.

## 5. Executable evidence and scope

The24 ledgers cover three finalizers, two duration-bound interfaces
and four earlier projection choices. The checker verifies576 complete
shared-register/residual/final-output identities under(3),288 on signed
tuples and288 on positive tuples. It checks every restored supplied
coordinate is positive in the latter cases, and that inverse
reparameterization recovers every original new coordinate exactly.

Every fixed-numeral role receives one finite integer consistently
throughout the two complete DAGs. These formal coefficient
specializations need not satisfy all cross-role arithmetic relations
of the actual huge fixed numerals. They check the algebraic identity;
the actual positive theorem uses their unchanged fixed recipes.

An additional1365 exact spread families at widths3,4,7,13,31 and
durations2,4,8 verify the converse bound and both restored gaps.
These are genuine outer arithmetic values, not materialized full
native Pell zeros or examples at the astronomical actual D. The
general proof(4)–(5), combined with the parent positive converse,
provides those complete witnesses. The explicit negative inverse
example above guards against broadening the statement to all old
positive supplied tuples.

```sh
python3 neary_woods_universal_population_joint_bound386.py
```

Author writer and fresh-default replay passed. Root's independent full
proof/source review and fresh replay passed without findings.
Substrates' independent full proof/source review and fresh replay also
passed without findings; its own literal executor checked192 additional
complete source/residual/output identities,96 signed, across all24
configurations. All four local links resolve. The source and receipt
were unchanged during final review.
