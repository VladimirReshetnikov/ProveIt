# Sharing the four-tile history: 382 operations

Three exact arithmetic identities remove **5M+2A** from the complete
[389-operation U9 source](neary_woods_universal_population_projection389.md).
The resulting fixed universal polynomial uses **382=184M+198A operations**,
**67 positive existential witnesses**, **22 comparisons** and four positive
program parameters besides the ordinary positive input x. Its certificate
costs **317=162M+155A operations**. The degree remains **at most2241**.

Every comparison residual and the entire output polynomial are unchanged
over all integer assignments. Thus the change preserves the same positive
witness tuples, not just the represented input set. The actual U9 machine,
its fixed production, all eleven fixed-numeral roles, the exact minimal
counter initialization and the complete selected history are unchanged.
The separate best established universal bound remains
[87 operations](complete75_normalized_strong87.md).

The [source](neary_woods_universal_shared_history382.py) and
[receipt](neary_woods_universal_shared_history382.json) contain the complete
arithmetic DAG, all comparisons and coordinates, and the guarded rewrite.
No change is made to an earlier packet.

## 1. The retained history interface

The [four-tile tag history](binary_tag_four_tile_history.md), after
[slope-class selection](pcp_affine_slope_class_history.md), has four
chronological selectors, one selected upper-history class and two
selected lower-history classes. Its fixed AND scale is P^11. The
compressed source's raw history costs161 operations, of which64 belong
to its native prescribed-AND kernel. Its other97 gates implement all
geometry, selection, transport and packing expressions.

Write U=H_U, V=H_V and h_i=Shat_i. Relevant already-paid expressions are

    T=U+P*V,
    Hb=U+P*((1+P)*V),
    G12=h_1+h_2,       G03=h_0+h_3,
    J=h_0+h_1+h_2+h_3-4.

T is used by the two-history range region. Hb repeats the histories
in the three selected-product lanes. G12 is used by the upper-slope
class and its transport; G03 is used by the lower upper-slope offset
sum. They are already part of the paid source.

The rewrite changes none of those interface polynomials. It also
retains every original selector, selected output, positive global
bound, comparison, native coordinate and fixed coefficient.

## 2. Three exact savings

The original source constructs its needed powers through these ten
multiplications, in an order respecting their dependencies:

    P2=P*P,        P3=P2*P,
    P6=P3*P3,      P7=P6*P,
    P4=P2*P2,      P8=P4*P4,      P9=P8*P,
    P5=P4*P,       P10=P5*P5,     P11=P10*P.

Only P2,P3,P6,P7,P9,P11 are needed elsewhere. Keep the first four
and replace the last two target expressions by

    P9=P7*P2,      P11=P9*P2.

The results remain P^9 and P^11 for every integer P, including zero
and negative P. The private registers P4,P8,P5,P10 disappear. This
saves **four multiplications**, without hiding the cost of any power.

Next use

    Hb=U+P*(1+P)*V = T+P2*V.

The original implementation uses two multiplications and one addition
after the existing factors are available. The new implementation uses
one multiplication and one addition, because T and P2 are already paid.
It saves **one multiplication**. The private register called
`V_region__67` now stores P2*V rather than P*(1+P)*V; its sole consumer
is the rewritten Hb addition. Hb itself is unchanged.

Finally compute the raw selector sum as

    h_0+h_1+h_2+h_3 = G12+G03.

The original three-addition chain is replaced by one addition using
the two existing group sums. The subtraction of4 in J remains paid.
This saves **two additions**. Both group sums depend only on supplied
selector hats, so making them available before J introduces no cycle.

The raw history therefore costs **154=72M+82A operations**, with90
wrapper gates and the same64-gate native kernel. This is a literal
seven-gate saving; no comparison or witness is removed.

## 3. Consumer checks and full polynomial identity

The helper `rewrite_rows` verifies every old power definition, range
expression, selector-sum row and reused group sum. It checks the complete
source-consumer sets of all deleted registers and of the changed
private V-region register. None may occur in a comparison or exported
interface. An added consumer causes an explicit rejection.

All remaining rows are retained. The helper changes the five displayed
right-hand sides, deletes exactly seven rows, and performs a stable
topological sort. The existing source validator checks uniqueness of
registers, every operand dependency and every fixed-numeral role.

The three identities prove, by induction along the resulting DAG,
that every retained certificate register except the deliberately
changed private V-region register has its old value. In particular,
every comparison residual and every unit factor is identical. Each
finalizer therefore computes exactly the same polynomial:

    F_new(x,program,witnesses)=F_old(x,program,witnesses)

on all integer assignments. This applies to the raw SOS and to both
safe-unit finalizers. No sign assumption or vanished residual is used
in the arithmetic identity.

Consequently the complete positive witness theorem is inherited
without any new extension or normalization argument. The selected
histories remain chronological; their bounds, common duration,
one-hot selection, selected affine products and carry-free transports
are exactly those of the parent. The ordinary input x, all four
program coordinates, and every native positive witness remain the
same coordinates with the same values. In particular no counter
condition has been weakened.

The public `rewrite(old)` accepts any compatible complete source with
this literal history, without assuming that its total cost is389.
This permits independent changes outside the guarded history region
to compose with the seven-gate saving. It updates the raw child
history metadata as well as the actual complete source. It does not
claim compatibility with arbitrary slope-class layouts or reapply
the saving to a history already rewritten.

## 4. Full ledgers and degree

| Form, both coordinate projections | Certificate | Comparisons | Positive witnesses | Polynomial | Degree upper bound |
|---|---:|---:|---:|---:|---:|
| Raw SOS |302|53|86|460|544|
| Native units |311|25|67|385|1405|
| Three normalized strong units |317|22|67|**382=184M+198A**|**2241**|

The normalized alternatives retain the parent's degree tradeoff:

| Projected recoder coordinates | Polynomial operations | Positive witnesses | Degree upper bound |
|---|---:|---:|---:|
| Neither |388|69|2204|
| Ahat only |385|68|2206|
| J only |385|68|2239|
| J and Ahat |382|67|2241|

Both duration-bound interfaces have these counts. The optional fifth
program parameter remains optional exactly as in the parent; the
default has four program parameters and one ordinary input coordinate.

Since the full polynomial is identical, its actual degree is unchanged,
whether or not that degree has been computed. The source also reruns
the parent's conservative propagation on the shorter DAG, including
the literal guards for the main-norm cancellation identities. The
default unit-product bound remains1911 and the largest outer-residual
bound remains165, giving1911+2*165=2241. No exact-degree claim or new
highest-coefficient assertion is made.

The unchanged parent universal theorem therefore supplies, for every
recursively enumerable S, fixed positive program values A_S,B_S,T_S,E_S
such that

    x in S iff there exist y_1,...,y_67>0 with
    F_new(x,A_S,B_S,T_S,E_S,y_1,...,y_67)=0.

The fixed program values are not existential witnesses. Universality
uses the actual already-proved U9 input slice; arbitrary positive
parameter tuples are not asserted to encode programs.

## 5. Checks and their scope

The24 literal ledgers cover all three forms, both duration-bound
interfaces and all four recoder-coordinate projection choices.
The checker compares all retained residuals, all unit factors and
the entire output on576 complete assignments,288 signed. Each fixed
numeral role receives one consistent finite integer throughout both
DAGs; those algebra fixtures do not impose all cross-role relations
of the actual huge coefficients.

An additional256 direct local checks include P=-7,-2,-1,0,1,2,3,11.
Seventy-two genuine positive affine-history paths, of lengths1 through6,
preserve all scalar packing interfaces, both transports and the joined
AND value. Their placeholder native coordinates are not claimed to
be full numerical Pell zeros or complete accepting tag runs.

Four malformed contracts are rejected: a leaked private power, a
comparison consuming the changed private region, an altered old
power definition and repeated application. The complete positive
native extensions and universal input theorem are inherited by exact
polynomial identity, rather than inferred from these finite tests.

```sh
python3 neary_woods_universal_shared_history382.py
```

Author writer and fresh default passed. Reduce_complete75's independent
full proof/source/fresh-default review passed after correcting a
tuple/list receipt-comparison issue in the command-line wrapper; the
arithmetic source and receipt were unchanged. That review added192
independent complete certificate/residual/output identities,96 signed,
across all24 configurations, and checked all six local links. No
remaining finding was reported. Root's independent full
proof/source/fresh-default review also passed without findings.
