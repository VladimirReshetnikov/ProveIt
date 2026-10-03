# Factoring the complete U15 history index: 532 operations

The [compiler](u15_packed_factored_index532.py) and
[complete receipt](u15_packed_factored_index532.json) reduce the direct U15
ordinary polynomial from536 to **532=219M+313A** operations. The raw natural
half-tape interface drops from338 to **334=126M+208A**. Both are exact
polynomial identities on the parent's unchanged supplied coordinates.
The separate87-operation universal benchmark is unchanged.

| Interface | Certificate | Complete polynomial | Positive witnesses | Comparisons |
|---|---:|---:|---:|---:|
| Raw natural half tapes |302=115M+187A|334=126M+208A|51|11|
| Positive ordinary input |440=188M+252A|532=219M+313A|87|31|

## The four-operation saving

The history AND kernel computes its truth fields rather than supplying them
as witnesses. Write `q=native__q`, `A=native__padded_A`,
`B=native__padded_B`, and `Z=native__F3`. Its definitions are

```
F1 = A-Z,
F2 = B-Z,
F0 = q-A-F2-1,
r  = F0 + q*(F1 + q*(F2 + q*Z)).
```

Substituting those definitions gives the integer polynomial identity

```
r = (q-1)*(A+1+(q+1)*(B+(q-1)*Z)).
```

For example, expanding the right hand side gives
`q-1+(q-1)*A+(q*q-1)*B+(q*q*q-q*q-q+1)*Z`, exactly the
expansion of the original definitions. No positive, native, typing, or
zero assumption is used.

The original source computes `A=native__scaled_A+12`. Its only live
consumers outside that defining gate belong to the removed block. Replacing
the same one addition by `A+1=native__scaled_A+13` pays for the shifted
constant without an extra gate. The old five digit-definition operations
and six Horner operations become seven operations: the two radix shifts,
three products, and two inner additions. Thus twelve gates, including the
old A definition, become eight: exactly four additions disappear.

The existing `native__bs_packed` name is retained for r, so every downstream
consumer sees the identical integer. No register outside the removed block
uses any other removed intermediate. All retained comparison operands,
semantic registers, tag registers and computed loader fields remain equal.

## Complete proof and inherited theorem

The compiler pins the536 source and its inherited lineage, including after
cache warming. It checks the twelve literal incoming rows before rewriting.
A sparse polynomial calculation in the four independent inputs
`scaled_A,q,B,Z` proves the local identity coefficientwise. An independently
interned complete source DAG then proves equality of every retained residual,
named semantic/tag/loader value, and the final sum of squares, using only the
proved equality at the packed-index cut.

The source is topologically sorted, every gate reaches the final output,
and the complete finalizer is charged. The eleven raw or31 ordinary
comparisons remain. Exact degree1936 transfers from the
[reviewed536 parent](u15_packed_joint_affine536.md) because the full polynomial
is identical; the new source also reproduces the formal upper bound1936.
The ledger conservatively keeps `exact_degree_claimed=False`, separately
from this inherited exact-degree proof.

The ordinary input loader, four fixed positive program numerals on the
inherited effective valid-program slices, positive witnesses and unbounded
first-halt relation are all retained. The raw inputs `L0,R0` remain natural;
the other supplied raw coordinates are positive. The parent's positive
graph correspondence to611 is inherited by identity, with its weighted
tape-residual correction unchanged. No claim is made that arbitrary program
numerals encode valid programs.

## Metadata and public interface

`build`, `canonical_parent`, `checked`, `polynomial_source`, `evaluate` and
`identity` expose copied canonical data. The immediate parent is536. Exact
Boolean switches, exact integer assignments and complete coordinate keys
are enforced; `signed=True` enables integer algebraic evaluation. Public
packets are matched with exact types, so equal-valued floats or Booleans do
not substitute for integer coefficients.

The old `computed_definitions` and `computed_truth_fields` are removed from
live metadata. `proof_only_truth_reconstruction` retains the historical six
rows solely to describe the former truth values. Its scope explicitly says
these are neither emitted gates nor new witnesses. No arithmetic operation
needed by the actual equation is hidden in those reconstruction rows.

## Replay

From the maintained artifact directory:

```sh
python u15_packed_factored_index532.py
```

Use `--root` to select the dependency directory in an isolated copy and
`--write` only to regenerate the complete receipt. The default replay checks
the saved JSON with exact types. Assertions must remain enabled.

The author replay checks96 full polynomial/index identities,48 on signed
assignments, and2,016 retained scalar residual identities. It rejects465
malformed calls and checks six defensive-copy boundaries. These finite
checks support the exact polynomial proof; they do not enumerate the
unbounded positive solution set or construct astronomical Pell witnesses.

The [independent full review](review_u15_factored532.md), [portable checker](review_u15_factored532.py) and [receipt](review_u15_factored532.json) confirm both complete polynomial identities, exact degree1936, strict public interfaces and source authentication. They also check composition with the binary affine rewrite, giving523 ordinary/325 raw operations with the identical polynomial.
