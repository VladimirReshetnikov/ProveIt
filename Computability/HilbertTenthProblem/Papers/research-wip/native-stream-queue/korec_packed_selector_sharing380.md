# Paid control sums reduce the U21 compiler to380 operations

The [literal successor](korec_packed_selector_sharing380.py) saves **17
additions** from the [zero-range397 compiler](korec_packed_zero_range397.md).
Its default is **380=141M+239A**, with379 certificate operations, one
comparison,50 positive witnesses, one fixed positive program parameter and
ordinary positive input. The conservative degree bound remains **21549**.
The inherited second program-radix interface costs **379=142M+237A**, with
50 witnesses and degree bound40706.

This is an exact identity of complete polynomials on the same supplied
integer coordinates. It preserves every parent comparison, native factor,
public interface and chronological condition. The change only reuses
selector sums already paid inside the control formulas. The
[receipt](korec_packed_selector_sharing380.json) records all six supported
base sources and both finalizers. This independent actual strongly universal
U21 route does not improve the separate U9 or75/87 frontiers.

## 1. A disjoint cover by already computed registers

The frozen parent uses34 positive selector hats. Write

    E_i=edge_i_hat-1, 0<=i<34,
    J=E_0+E_1+...+E_33.                              (1)

The emitted definition of J is a left-associated chain of33 additions.
Its intermediate registers `partition_34` through `partition_65` are
private; only `partition_66`, the final J, is used by the rest of the
compiler.

The source already computes these five sums for its current or following
control labels:

| Register | Selector indices in its sum |
|---|---|
|`coefficient_tail_213`|1,4,10|
|`coefficient_tail_203`|3,6,7,15,16,18,26|
|`Z5_131`|5,17,19,23|
|`coefficient_tail_184`|12,20,22,24,31,33|
|`coefficient_group_176`|28,29|

Every coefficient in these five sums is exactly one. Their supports are
pairwise disjoint and cover22 selector indices. The remaining indices are

    0,2,8,9,11,13,14,21,25,27,30,32.                  (2)

Consequently J is also the sum of the five paid registers in the table
and the twelve individual selectors in(2). These17 operands require16
additions, saving33-16=17 additions. The identity holds for all integer
selectors, with no positivity, one-hot, chronology or zero equation used.

The actual new operand order is stored as `TERMS` in the source. The proof
checker traverses the original addition graph for each chosen register,
rejects overlaps within a sum, verifies the displayed supports, and verifies
that their combined support contains each of0 through33 exactly once.
It also checks that the original J has precisely that support. The table
is therefore validated against emitted arithmetic rather than treated as
an informal annotation.

A bounded disjoint-cover search suggested this schedule. No optimality is
claimed over other addition circuits, subtraction identities, alternative
control labels, or changes to the counter compiler.

## 2. Guarded graph rewrite and exact equivalence

`rewrite(old)` accepts only one of the six complete canonical zero_range397
packets: the three `fields`, `range_unit`, and `units` forms in each inherited
program interface. It verifies the literal original J chain, the actual
U21 table, its34 expanded edges and eight counters. Every erased prefix
must be consumed only inside that chain. Recursive guards reject exports
through interfaces, comparisons, public registers or native restoration
metadata. The paid sums and their transitive addition definitions are
checked before the rewrite.

Delete the32 private intermediate prefixes, replace the final J definition
with the16-addition schedule, and retain its original name `partition_66`.
Fifteen new intermediate registers are introduced as computed registers,
not existential coordinates. A stable topological sort places the already
paid control sums before the new J. Their defining cones contain only
selector additions and so do not depend on J, P, a native witness or the
chronological radix. No cyclic definition or free control value is added.

Every retained original register now has exactly its former value: the
only changed input to the rest of the graph is J, and Section1 proves that
value identical. Induction through the topological source proves equality
of all retained outputs, ordinary residuals, native factors and complete
polynomials. The removed diagnostic prefixes can be restored as

    partition_(i+33)=sum_(j=0)^i E_j, 1<=i<=32.        (3)

All supplied parameters and witnesses are literally unchanged. Thus the
identity map is a bijection of positive zeros for each supported parent
form, on every parameter slice where that parent's theorem applies. In
particular all paid initial-input, counter-range, control, termination,
native-bound and sign conditions remain exactly the same. No fresh private
native extension or off-zero witness adjustment is necessary for this
successor.

The one-program interface uses the parent's actual positive U21 program
index and ordinary input. The two-program variant retains its fixed positive
index E and fixed dyadic radix parameter C>=4 with C>E. Their separate
universality proofs and positive-domain conventions are inherited without
change. This exact rewrite makes no new assertion identifying tuples between
those two interfaces or between different native forms.

## 3. Literal counts and unchanged degrees

Each new chosen sum has degree one in the supplied selector hats. The new
J therefore has exactly the same propagated degree as the old J. Every
other retained arithmetic definition is unchanged, so its propagated degree
is unchanged too. In particular the inherited guarded main-norm polynomial
cancellation receives the same operands and bounds. The checker requires
equality of the complete degree dictionaries, not only the displayed maximum.
These remain conservative upper bounds rather than exact polynomial degrees.

The product-finalizer counts are:

| Program interface | Native form | Operations | M | A | Comparisons | Witnesses | Degree bound |
|---|---|---:|---:|---:|---:|---:|---:|
|one parameter|fields|382|142|240|4|50|21540|
|one parameter|range_unit|381|142|239|3|50|21549|
|one parameter|units|380|141|239|1|50|21549|
|two parameters|fields|381|143|238|4|50|40690|
|two parameters|range_unit|380|143|237|3|50|40706|
|two parameters|units|379|142|237|1|50|40706|

For the two forms retaining ordinary comparisons, the all-SOS finalizer
has the same operation count as the product finalizer. For `units`, squaring
the single residual adds one multiplication:381 and380 operations in the
two respective program interfaces. Their degree bounds are43098 and81412.
All twelve literal finalizer ledgers are checked directly; each loses
exactly17 additions and no multiplication relative to its own parent.
The complete emitted source closure is also checked so that every remaining
gate contributes to the requested output.

Run `python3 korec_packed_selector_sharing380.py`; `--write` regenerates the
receipt. Across the six bases, the checker evaluates192 complete retained
source/restoration identities, including96 signed assignments. Both
finalizers give384 complete polynomial identities, including192 signed
output cases. Formula(3) restores every deleted diagnostic register, and a
separate scalar sum checks the new J directly from all34 supplied hats.
Six malformed callers exercise private consumers, recursive exports,
comparisons, an altered paid sum and attempted repeat application.

These arbitrary-integer source checks support the exact algebraic identity;
they are not claims of materialized complete native Pell zeros. Author receipt
generation and a fresh replay pass. Independent full proof/source review and
a separate fresh replay pass without findings. Its separate executor checks144
complete retained-register and manual prefix-restoration maps, plus288 whole
finalizer identities; half the assignments are signed. The review also verifies
the disjoint support cover, acyclic dependency order, all six literal ledgers
and unchanged complete degree dictionaries.
