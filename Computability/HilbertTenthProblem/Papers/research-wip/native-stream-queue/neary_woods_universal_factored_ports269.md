# Factor the native index directly through its ports: a269-operation U9 polynomial

The [regrouped-family successor](neary_woods_universal_computed_ports_partitions.md)
optimizes degree bounds across all16 inherited strong/scale bases, retaining
this269 endpoint and improving intermediate options to275/1094,276/1048,
277/734 and278/706. Its finite propagated-objective minimum608 is reached
at279 operations; it is not an all-circuit or exact-degree lower bound.

The [computed-fields275 construction](neary_woods_universal_computed_ports275.md)
has an algebraic successor costing **269=136M+133A**, with **255=131M+124A
certificate operations**, **five comparisons**, **43 positive witnesses**,
four positive program parameters and degree **at most3853**. Six additions
disappear. The complete polynomial, its supplied coordinates and its positive
zero set are identical to the selected275 parent's, including off-zero
integer polynomial values. No new native typing or positivity theorem is
needed for this step.

The [source](neary_woods_universal_factored_ports269.py) and
[receipt](neary_woods_universal_factored_ports269.json) retain every fixed
numeral multiplication and the parent's complete ordinary-input/program
interface. An intermediate factorization without affine folding costs272.
The separate75-operation certificate and87-operation polynomial frontier
remain unchanged.

## 1. Factor the packed truth fields

Write q for the joined native scale, A and B for its padded input ports,
and Z for its output port. The275 source computes

    F1=A-Z, F2=B-Z, F0=q-A-F2-1,
    r=F0+q(F1+q(F2+qZ)).                           (1)

The three field definitions use five additions/subtractions. The packed
Horner expression uses three multiplications and three additions. Neither
the fields nor its five intermediate packing registers has a surviving
consumer outside this block. The final r does: its positive-scale bound
and native index factor must retain exactly their old values.

As an identity over Z[q,A,B,Z],

    r=(q-1)[1+A+(q+1)(B+(q-1)Z)].                 (2)

Both sides expand to

    q-1+qA-A+q^2B-B+q^3Z-q^2Z-qZ+Z.

The new schedule pays q-1,q+1,A+1, then the three products and two
remaining sums in(2): **3M+5A** instead of **3M+8A**. It saves three
additions, yielding272=136M+136A with258 certificate operations.
There is no division by q-1 and no assumption that q is positive or
dyadic in this identity.

The source guards all eleven original producer rows. Every erased name
must have only a replaced arithmetic consumer and must be absent from
comparisons, positive free coordinates, unit factors, group products,
nested public registers and interfaces. The final packed register keeps
its old name and all downstream consumers.

## 2. Fold two existing affine expressions

In(2), A is used only through A+1. Its exact existing producers are

    A_low=joint_A_sum+12,
    A=A_low+fusion_high_A.

Compute instead

    A_low_plus_one=joint_A_sum+13,
    A_plus_one=A_low_plus_one+fusion_high_A.        (3)

This uses two additions instead of the previous three, saving one more.
The fixed13 is an ordinary literal operand in a paid addition; no
multiplication by a fixed nonunit numeral is omitted from the ledger.

For the output port, put m=Q-1=`modulus`, h=`quotient_hat`, and
L16=`joint16B`. The literal source already defines Q=m+1. Its old rows
give

    product=mh,
    right0=product+z, right=right0+2,
    Ahat=right-Q,
    scaled_Z=L16*Ahat, difference=scaled_Z-L16,
    Z_low=difference+8.                            (4)

Thus

    Ahat-1=m(h-1)+z,
    difference=L16[m(h-1)+z].                     (5)

Replace the six rows producing product through difference by the four
rows for h-1, m(h-1), m(h-1)+z, and its product with L16. Keep the
difference register, Z_low and every high-output register unchanged.
The old subgraph has2M+4A; the new one has2M+2A. This saves two additions.
Identity(5) uses the guarded literal producer Q=m+1, not a zero-set
comparison. It holds on signed assignments and for arbitrary materialized
values of the fixed numeral roles.

Combining(2),(3),(5) removes six additions in all, with no change in
multiplication count. All source references to the deleted registers are
checked. The seven incompatible-caller regressions include altered Q and
padding producers, a private consumer, a new comparison, nested exports,
and a colliding fresh register.

## 3. Complete polynomial and positive-domain equivalence

Every retained certificate register has exactly its parent's value.
In particular the packed native index, both native scales, all norm and
index/linear factors, each group product and every comparison agree.
The grouped finalizer therefore has exactly the same value:

    P269(v)=P275(v) for every integer supplied tuple v. (6)

This is stronger than equality of accepted outer instances. Parameters,
witness lists and positive domains are unchanged, so the identity map
is a bijection of the complete positive zero sets, even for arbitrary
program parameters. The inherited universality theorem itself remains
scoped to the effective valid U9 program slices and synchronized padding;
no new interpretation of invalid program parameters is asserted.

The earlier275-to282 converse still has its checksum-normalization scope.
To use an earlier coordinate helper, first select the stored
`factored_pack_parent` and pass the unchanged supplied tuple to that
parent's helper. This successor does not pass its shortened source to a
helper that expects the deleted field gates.

`restore_parent_registers` is a diagnostic expansion of the erased
internal registers, not a list of extra arithmetic gates in the emitted
polynomial. It reconstructs exactly the old register values for audit.
Historical fusion/projected-coordinate metadata is retained under explicit
historical keys; live interfaces include only available names. In the
folded source the available loader port is Ahat-1, named `factored_unhat`.
The former Ahat is restored by adding1 diagnostically. No existential
coordinate is removed or reconstructed.

## 4. Counts, degrees and selected-family scope

The default certificate has255 gates and five comparisons. Its anchored
finalizer pays14 further operations, giving269=136M+133A. The intermediate
without affine folds has258 certificate gates and272 polynomial gates.
Both retain43 positive witnesses. Every emitted gate reaches the complete
output; neither intermediate counts unused diagnostic reconstructions.

The all-folded images of the selected275 family are:

| Polynomial operations | Degree upper bound | Positive witnesses |
|---:|---:|---:|
|269|3853|43|
|270|3437|43|
|271|3391|43|
|272|2273|44|
|273|1505|44|
|274|1459|44|
|275|1142|44|
|276|1098|44|
|277|764|44|
|278|734|44|
|279|608|44|

The279/608 option has250 certificate gates and ten comparisons. The
separate fixed43-witness alternative costs276 with degree at most1344,
250 certificate gates and nine comparisons. These are the twelve
selected parent schedules, not a new exhaustive grouping search.

Because the full polynomials are identical, every valid parent degree
bound remains valid. Independently propagating the literal rewritten
source gives the same full degree records, including each factor bound,
for all tested schedules. Both main-norm cancellations retain their exact
guarded polynomial identities. No zero-set relation is used to reduce an
off-zero degree; displayed degrees are conservative upper bounds.

## 5. Reproducible checks

```sh
python3 neary_woods_universal_factored_ports269.py
```

The checker emits48 ledgers: twelve selected parent schedules, both
program-bound interfaces and the two folding modes. It verifies1,536
whole-polynomial and retained/restored-register identities, including768
signed assignments and768 positive supplied assignments. Unit factors
and the semantics of every named group product are checked as well.

A separate exact coefficient-dictionary expansion proves(2) and(5)
without numerical sampling. Seven incompatible-callers are rejected.
Each emitted source has unique producers, available operands and complete
output ancestry. The supplied parameters, witness domains, comparisons
and conservative degree records agree with the corresponding parent.
These off-zero algebra checks do not claim numerical full positive Pell
zeros or valid chronological histories.

Author receipt generation and a fresh default replay pass. Native's
independent full proof/source review and fresh default replay also pass,
with no findings. A separate literal executor checked512 complete output
identities, including256 signed assignments, across all sixteen
post-specialization strong/scale bases, both program interfaces and both
folding modes. Every surviving source register and unit factor matched;
the complete degree dictionaries were unchanged in all64 composition
contexts. These additional fixtures use the new partition-base builders
and are off-zero algebra checks, not full positive Pell witnesses.

Gibbs's second independent proof/source review and fresh default replay
also pass, with no findings. Independent symbolic expansions verify both
local identities. A separate numeral-aware executor checks256 complete
output, retained-register and group identities, split evenly between
signed and positive assignments, across sixteen contexts: both folding
modes, both program interfaces and four parent schedules, including the
fixed43-witness alternative. The erased fields and Ahat are reconstructed
manually without the author's restoration helper. Live metadata, supplied
domains, comparisons and degree records agree throughout.
