# Exact selector sharing reduces the C2 compiler to428

The [literal successor](tseytin_selector_sharing428.py) saves **12 additions
or subtractions** from the [complete universal440 source](tseytin_universal440.md),
giving **428=200M+228A**, with408 certificate operations, seven comparisons,
65 positive witnesses, one fixed positive program parameter, ordinary
positive input, and degree at most5868. Its separate-power alternative
costs430 and has degree at most5814. The same two identities reduce the
[standalone C2 word predicate](tseytin_c2_word_history.md) from374 to362.

Each complete polynomial is identical to its corresponding parent on the
same supplied integer coordinates. All factors, comparisons, public ports,
program conventions and positive domains remain unchanged. In particular,
the exact ordinary-input exponent projection and the paid query-loader
sign exclusion are inherited literally. No new universality or native
sign proof is used, and no frozen parent source is changed.

## 1. Eight paid blocks replace the selector-sum suffix

Write \(S_i=\texttt{Shat}i\). The parent pays a chain computing the sum of
all24 supplied selector hats. Its first six-term prefix
`selector_sum__8` is already needed elsewhere. The following eight
registers are independently paid by that prefix, the control words, or
the slope masks:

| Register | Selector indices in its sum |
|---|---|
|`selector_sum__8`|0,1,2,3,4,5|
|`linear_group__362`|6,7|
|`linear_group__364`|8,9|
|`linear_group__366`|10,11|
|`linear_group__368`|12,13|
|`group_sum__223`|14,16,21,23|
|`group_sum__230`|15,17,20,22|
|`linear_group__374`|18,19|

Their supports are disjoint and their union is exactly0 through23.
Consequently the old `selector_sum__26` equals the sum of these eight
registers over arbitrary integers. In particular, the two cross groups
`group_sum__223` and `group_sum__230` together cover the four pairs
(14,15),(16,17),(20,21),(22,23) using only two paid groups. The saving
does not use only the consecutive control pairs.

The old suffix after the retained six-term prefix costs18 additions.
The new eight-term sum costs7. Delete the17 private prefixes
`selector_sum__9` through `selector_sum__25`, add six temporary sums,
and retain the final name `selector_sum__26`: the net saving is **11A**.
The row `J__27=selector_sum__26−24` is unchanged. No one-hot selector,
nonnegativity or chronological equation is assumed in this identity.

Each reused block is a pure sum of supplied selector hats, so moving its
computation ahead of J introduces no dependency on J, the chronological
radix or the native kernel. A topological sort makes the new schedule
explicit.

## 2. The two update words share their constant offset

The parent computes the following four additions/subtractions:

```
linear_shared_sum__410 = linear_sum__392 + linear_sum__409
linear_constant__411 = linear_shared_sum__410 - 58328
linear_shared_sum__429 = linear_sum__392 + linear_sum__428
linear_constant__430 = linear_shared_sum__429 - 58328.
```

Both intermediate shared sums are private. Replace these rows by

```
c2_shared_update_offset = linear_sum__392 - 58328
linear_constant__411 = c2_shared_update_offset + linear_sum__409
linear_constant__430 = c2_shared_update_offset + linear_sum__428.
```

This saves **one more addition/subtraction**. Both update values remain
identical for arbitrary integer assignments, including those for which
the new shared offset is negative. It is a computed register, not a
new positive witness.

All19 erased diagnostic registers restore by the original selector
prefix sums or the two displayed shared-sum formulas. Every other old
register keeps its value, by the two identities and induction through
the retained source. This proves the complete polynomial identities for
both finalizers and the identity bijection on supplied positive zeros.
No formal inverse needs an extra positivity hypothesis.

## 3. Canonical guards and inherited degrees

`build(context='universal', merge_units=True)` emits the default.
`merge_units=False` emits the separate-power parent alternative.
`context='word'` emits only the canonical standalone coupled word
predicate, with its inherited unit product. Every context supports
`polynomial_source(packet, sum_of_squares=False)` and its squared variant.

`rewrite` requires equality with the complete corresponding canonical
parent. The local `rewrite_rows` helper additionally checks the literal
selector chain, the exact disjoint block supports, and all four rows of
the shared offset. Every erased register must have exactly its displayed
sole consumer. Recursive active-export guards reject hidden references
through domains, comparisons, factors, interfaces, group products or
native restoration metadata. Fresh temporary names are required, and
source order and closure are checked. The local helper alone certifies
no arbitrary host's universal semantics.

The selector blocks and both update linear forms have degree one in the
supplied coordinates. The new offset also has degree one. Every retained
register therefore has the same propagated degree as before; the checker
compares them individually. The two parent main-norm cancellation graphs
are untouched. The complete inherited degree dictionaries remain valid
for every context and finalizer. These are upper bounds, not claims of
exact degree after fully expanding the universal polynomial.

## 4. Literal ledgers and verification

| Context | Certificate | Comparisons | Witnesses | Polynomial | M | A | Product degree | SOS degree |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
|C2 word predicate|345|6|52|362|161|201|5814|11352|
|Universal, separate power|407|8|65|430|200|230|5814|11352|
|Universal, merged units|408|7|65|428|200|228|5868|11460|

The ordinary product and SOS finalizers have the same operation count
in each row. All gates are live. The standalone word predicate still
requires its encoded-word input; only the universal contexts include the
paid ordinary-input loader and exponent relation.

The [receipt](tseytin_selector_sharing428.json) stores all six complete
schedules, their literal ledgers, supplied domains and source hashes.
Author receipt generation and a separate fresh default replay pass.
Its192 complete retained-register and
manual-restoration maps include96 signed assignments and six assignments
with all unhat selectors zero. Both finalizers give384 complete output
identities, including192 signed cases. The scalar sums independently
check each of the three changed retained outputs. Eight malformed callers
exercise private consumers, nested exports, altered block support,
an altered offset, temporary collisions, missing comparisons and repeat
application. No source fixture is claimed to be a complete giant Pell zero.

Run `python3 tseytin_selector_sharing428.py`; `--write` regenerates the
receipt. Independent full proof/source/dependency review and a separate
fresh replay passed without mathematical findings. Its own three symbolic
coefficient-vector proofs verify the block partition;288 retained-register
and restoration cases include144 signed cases and18 all-zero decoded
selector cases. Its576 complete parent and independently computed finalizer
outputs include288 signed cases. All six degree/opcode/closure audits
pass, as do29 local and three complete canonical rejections. Root source
and proof review and a further fresh replay also pass. All four local
links resolve. The chosen exact sharing does not assert global optimality
among other addition circuits, control codes or compiler models.
