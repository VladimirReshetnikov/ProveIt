# Degree tradeoffs for the complete two-core universal polynomial

The [two-index construction](neary_woods_universal_joint_and_arithmetic.md)
gives301 operations with total degree at most2475. Selectively normalizing
strong witnesses and regrouping unit factors gives a family of lower-degree
alternatives, including **305=143M+162A with degree at most1144** and
**308=142M+166A with degree at most1076**. Every construction retains51
positive witnesses and four fixed positive program parameters besides
the ordinary positive input. All degree bounds include those parameters.

The [source](neary_woods_universal_joint_and_partitions.py) and
[receipt](neary_woods_universal_joint_and_partitions.json) enumerate the
specified finalizer family and supply complete literal sources for its
seven undominated operation/degree pairs. These are conservative degree
bounds. The search does not establish exact degrees or global arithmetic
optimality. The separate75-certificate/87-polynomial frontier is unchanged.

## 1. Sixteen compatible complete sources

Begin with the ordinary-unit form of the
[303 packet](neary_woods_universal_joint_and_units.md), whose original
complete final polynomial costs305 operations. Independently choose
whether to normalize the geometry and joint-AND strong witnesses, and
whether to absorb each of their first-index comparisons. This gives
sixteen combinations of four binary choices.

Each strong normalization uses exactly the parent's guarded rewrite,
including its audit that the five reconstructed auxiliaries of each core
affect only that core's strong/auxiliary obligations. Soundness restores
i_old=Delta*i; completeness chooses that core's canonical positive
auxiliaries. Either subset therefore preserves the accepted outer
relation. Different normalization choices need not have identical
positive native witness tuples.

Each index rewrite uses the guarded source and sign proof of the
[two-index packet](neary_woods_universal_joint_and_arithmetic.md). That
proof needs only integer unit factors and zero retained residuals.
It restores the full strong equation before recovering each index sign;
neither Boolean typing nor a positive checksum is assumed prematurely.
Index rewrites preserve the same positive tuples for a fixed strong
treatment. The two rewrites do not change each other's defining rows.

For any chosen base let N_1,...,N_n be its listed unit factors and let
r_1,...,r_m be its remaining comparison residuals, excluding the single
old product comparison. Its proved finalizer is

    F=product_i N_i * (1+sum_j r_j^2)-1.

Every positive zero of this complete source has **every N_i=1** and
every r_j=0. This conclusion includes the signed checksum and any
index factors; it follows from the cited full positive sign proofs.
The fixed U9 table, coefficient recipes, exact counter, paid ordinary
input loader, history and terminal constraints are unchanged.

## 2. Two complete ways to group the factors

Partition the factor indices into g nonempty groups and put

    V_h=product_(i in group h) N_i.

The ordinary sum-of-squares finalizer is

    F_SOS=sum_j r_j^2 + sum_h (V_h-1)^2.               (1)

Alternatively select exactly one group a to remain unsquared:

    F_a=V_a*(1+sum_j r_j^2+sum_(h!=a)(V_h-1)^2)-1.    (2)

Both have exactly the base's positive zero set in the same supplied
coordinates. For(1), a zero makes each summand zero. For(2), the
parenthesized integer is at least1. Its product with the integer V_a
is1, so both integers equal1. In either case all residuals vanish and
all V_h=1. Their product is the original product of all N_i, so this
tuple is a zero of the complete base polynomial. Conversely, the
base's proved N_i=1 and r_j=0 make(1) and(2) vanish for every partition.

No assumption that arbitrary off-zero factors are positive is needed.
No rational or signed witness is introduced by grouping. Neither
grouped polynomial is claimed identical to the old polynomial away
from their common positive zero set.

## 3. Literal cost and degree formulas

Delete the original product chain and retain precisely the dependency
closure of all individual factors and original residuals. Let B be the
number of arithmetic gates in this closure. The literal audit verifies
that this removes exactly n-1 multiplication gates; no comparison or
factor dependency is deleted. Rebuilding the grouped products costs
n-g multiplications.

For(1), there are m+g comparisons in an ordinary SOS. For(2), there are
m+g-1 squared residuals, followed by addition of1, multiplication by
V_a, and subtraction of1. Both schedules cost exactly

    B+n+3m-1+2g.                                     (3)

Here m>0 in every base. Each subtraction, multiplication and addition
is charged once, including all scalar constants. The source validates
the complete certificate and output schedule and retains all51 supplied
positive coordinates. The certificate ledger counts all group-equals-one
conditions, including the unsquared anchor when present.

Let d_i bound deg(N_i), let D_h=sum_(i in group h) d_i and let r bound
the maximum degree of an original residual. Literal propagation with
the parent's two guarded main-norm cancellations gives

    deg(F_SOS) <= 2 max(r,D_1,...,D_g),
    deg(F_a)   <= D_a+2 max(r,{D_h:h!=a}).             (4)

For a sole anchor the maximum in(4) is r. These are upper bounds;
possible additional cancellations are not ruled out. Fixed coefficient
recipes have degree zero, while ordinary input, program and witness
coordinates all have degree one.

The checker enumerates **1,286,789 partitions** across the sixteen
bases, evaluates(4) for SOS and each possible anchor, and records the
best propagated bound at every group count. Removing dominated pairs
gives the following complete frontier **within this specified family**.

| Polynomial operations | M | A | Degree upper bound | Certificate | Comparisons |
|---:|---:|---:|---:|---:|---:|
|301|144|157|2475|260|14|
|302|143|159|1707|258|15|
|303|143|160|1522|256|16|
|304|143|161|1296|257|16|
|305|143|162|1144|255|17|
|307|143|164|1110|254|18|
|308|142|166|1076|252|19|

For example, the305 source normalizes only the geometry strong witness
and absorbs only its index. It separates the joint auxiliary factor,
whose degree is at most572, from the product of the other eight factors,
whose degree is at most538. The SOS uses the original residual bound206,
so its degree is at most2*572=1144. The308 source keeps both strong
comparisons, absorbs only the geometry index, and uses group degree
bounds252,572,244. The572 group is the anchor, giving572+2*252=1076.

Both parameter interfaces are supported: four program coordinates with
program_E also bounding duration, or an independent positive fifth
duration-bound coordinate. Their costs, witness counts and degree bounds
coincide. The raw parent's356-operation,64-witness,degree-at-most580
SOS remains a lower-degree alternative outside this unit-partition family.

## 4. Verification and its limits

The receipt records all sixteen finite searches and complete sources for
the seven frontier points in both parameter interfaces. It checks896
complete output identities,448 on signed supplied tuples. Each check
executes the original base separately, compares every retained factor
dependency, and directly forms(1) or(2) from the base factors/residuals.
Finite numeral-role substitutions are consistent across both executions;
positive cases use radix4 and divisor7. They verify arithmetic identities,
not giant numerical positive Pell extensions.

The positive zero-set proof is Section2 together with the complete parent
proofs. The finite partition enumeration establishes only the best values
of the conservative formulas(4) in the stated family. It is not a lower
bound for other Diophantine representations or other polynomial circuits.

```sh
python3 neary_woods_universal_joint_and_partitions.py
```

Final review passed. The author writer and fresh replay passed, including
a fresh replay after correcting the compiled packet's anchor/SOS metadata.
Two independent reviewers checked the full proof and literal source
without findings. One ran a fresh exhaustive replay and384 additional
complete output identities,192 signed, across96 partitions covering all
sixteen bases and both interfaces. The other independently reconstructed
the dependency closure for all32 base/interface choices, checked all
sixteen degree envelopes and added384 arbitrary grouped output identities,
192 signed. These extra cases include unselected partitions and anchors.
All five local links resolve. The exact positive equivalence rests on
the proofs above; the finite checks retain their stated algebraic scope.
