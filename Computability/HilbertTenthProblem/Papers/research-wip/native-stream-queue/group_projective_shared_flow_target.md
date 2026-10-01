# A shared edge-checksum sum removes one sparse-flow addition

Whenever the fixed macro table has a path of length at least three,
its sparse flow computation can reuse an edge-checksum partial sum to
save **one addition**. Every retained register, comparison and complete
output polynomial stays identical over arbitrary integer assignments.
The rewrite composes with the [port-bias compiler](group_projective_port_bias_folding.md)
and the [joint-bound unit](group_projective_joint_bound_unit.md).

For the illustrative ten-letter table, the latter composition gives
**259 certificate / 276 polynomial operations**, six comparisons,
42 positive witnesses and exact degree **3504**. This is another
fixed-table compiler improvement; no numerical universal alphabet is
instantiated and the separate numerical 75/88 bounds remain unchanged.

## 1. The shared sum and the exact target identity

In the sparse macro controller, partition edges into internal, first,
last and hub edges. First edges leave the hub and enter a positive
internal state; internal edges connect successive positive states.
Write

    I=sum_internal Ehat_e, Fraw=sum_first Ehat_e,
    F=sum_first c_e*Ehat_e,

where c_e is a first edge's target-state number. The state enumeration
starts at one, so the sorted first-state numbers satisfy

    1=c_1<c_2<...<c_b.

When an internal edge exists, the checksum's first addition is already

    checksum1=I+Fraw.                                    (1)

Let V be the weighted internal source sum and n the number of internal
states. The existing sparse flow computation uses

    shared=V-n(n+1)/2,
    target_partial=shared+I,
    target=target_partial+F.                             (2)

The right side of the flow comparison is B*target. Every nonzero state
occurs once as a target in the path construction, so target is exactly
`sum_e target_state(e)*(Ehat_e-1)`.

Reexpress the weighted first sum as

    F=Fraw+sum_(j=2)^b (c_j-1)*Ehat_j.

Substitute (1) into (2) to obtain

    target=shared+checksum1+sum_(j=2)^b (c_j-1)*Ehat_j.    (3)

The resulting target is exactly the same polynomial. No flow equation,
bit partition, signed-state bound or other certificate comparison is
assumed in this identity.

If no internal edge exists, every macro has length at most two. The
parent uses a different sparse-flow fragment, and this packet leaves
it unchanged. Thus the saving indicator is exactly

    theta=1 if some macro has length>=3, otherwise0.

## 2. Why the literal saving is always one addition

The parent has two cases for its weighted first sum. If c_2=2, it
already starts from Fraw and uses coefficients c_j-1 for the remaining
terms. Otherwise it starts from Ehat_1 and uses coefficients c_j.
The case b=1 has no weighted products or sum gates.

For c_2>2, every c_j-1 for j>=2 is at least two. Replacing coefficient
c_j by c_j-1 therefore changes no multiplication count. For c_2=2,
the second coefficient is already one and is represented by a register
copy; every other product is unchanged. Fixed-numeral multiplications
remain paid in both cases.

The old weighted sum uses b-1 additions and its two target additions
use two more. Formula (3) needs b additions. Therefore

    old additions=b+1, new additions=b,
    multiplication count unchanged.                         (4)

This also holds for b=1: a single addition of shared and checksum1
replaces the two additions in (2). No padded edges, new state numbers,
ordinary-input constants or witness variables are introduced.

The [source](group_projective_shared_flow_target.py) checks the actual
raw checksum operands and reconstructs the parent's entire weighted
first fragment, including its fixed coefficients and coefficient-one
aliases. It audits that every deleted register is used only within
that private fragment or by target, and never by a comparison. It
replaces the fragment, keeps the target register by name, and orders
the resulting source topologically. All other retained registers have
the same polynomial values as before.

## 3. Complete costs and degree tradeoffs

Use the preceding parent notation

    C=3m+3h+p+185+f_flow-3min(h,3)-epsilon,
    nu=1+chi,
    L=m+18 if epsilon=0, L=2m+10 if epsilon=1.

Here p and f_flow retain the original port and sparse-flow ledger
values. Let s be the actual port-bias saving and theta the indicator
above. The new saving is accounted for separately, so it is not counted
twice by changing f_flow in C.

| Variant | Certificate | Polynomial |
|---|---:|---:|
|Four-field SOS|C-2-s-theta|C+33-3chi-s-theta|
|Unshifted six-field product|C-2-s-theta|C+27-3chi-s-theta|
|Shifted-X product|C-2-s-theta|C+24-3chi-s-theta|
|Strong-unit product|C+1-s-theta|C+24-3chi-s-theta|
|Joint-bound unit product|C+3-s-theta|C+23-3chi-s-theta|

Each variant retains exactly its parent's comparison count, positive
witness list and exact degree. This follows from identity of the
complete final polynomial; no equation is substituted to estimate a
smaller off-zero degree.

For the ten-letter joint-bound example, s=theta=1:

| Mask reuse | Computed P | Certificate / polynomial | Comparisons / positive witnesses | Degree |
|---|---|---:|---:|---:|
|Yes|Yes|259 / 276|6 / 42|3504|
|No|Yes|260 / 277|6 / 42|2928|
|Yes|No|259 / 279|7 / 43|1774|
|No|No|260 / 280|7 / 43|1486|

The strong-unit alternatives cost 277, 278, 280 and 281 operations at
respective degrees 3502, 2926, 1773 and 1485, with the same witness
counts as the corresponding table rows. Some of these choices are
dominated by another switch choice; no claim of a minimal frontier is
made here. The unshifted supplied-P choices cost 283/degree1211 or
284/degree995 with 44 witnesses. The four-field no-mask supplied-P
choice costs 290/degree802 with 46 witnesses.

For the shifted-X certificate before the two unit merges, the same
example has 254 certificate operations and a 277-operation polynomial
at degree4298, with eight comparisons and42 witnesses. Keeping the
separate certificate and single-polynomial objectives explicit avoids
presenting the larger merged certificate as a certificate-cost saving.

## 4. Executable evidence

The [receipt](group_projective_shared_flow_target.json) stores 130 option
ledgers and one complete ten-letter source plus its finalizer. The
fixtures include empty tables, tables with only length-two paths,
single long paths, multiple paths with consecutive first-state weights,
and multiple paths whose first-state weights have gaps. They cover
all five parent variants and both optional compiler switches.

Across 3,120 assignments, including 1,040 signed assignments, the checker
compares every surviving register, every residual and the complete
output polynomial to the actual parent. It also independently reconstructs
the target from the original target-state weights and edge counts.
These finite checks supplement the exact source audit and identities
(1)-(4); they are not evidence of universality for a numerical fixture.

Run normally for deterministic receipt comparison, or with `--write`
to regenerate it. Every earlier parent remains reproducible.

Independent full proof/source review and a fresh default replay passed
without findings. A further 120 signed source evaluations on sixteen
independent tables covered identity, shifted and unshifted weighted-sum
cases across all five variants. The direct target-state sum, every
retained register, every residual and complete output agreed.
