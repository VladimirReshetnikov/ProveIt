# Two more paid selector pairs give the U21 source378

The [literal successor](korec_packed_selector_sharing378.py) saves exactly
**two additions** from [selector-sharing380](korec_packed_selector_sharing380.md).
Its default is **378=141M+237A**, with377 certificate operations, one
comparison,50 positive witnesses and degree at most21549. It retains one
fixed positive program parameter and ordinary positive input. The separate
two-program interface costs **377=142M+235A**, with376 certificate operations,
one comparison,50 witnesses and degree at most40706.

The complete integer polynomial is identical on the same supplied
coordinates. All source comparisons, domains, interface registers and
native factors remain unchanged. Thus both complete halting directions
follow directly from the parent. No new mask, native sign, chronology,
program convention or endpoint argument is used. The independent U9 and
75/87 frontiers are unaffected.

## 1. Two exact additions reused across control and action

Write `E_i=edge_i_hat-1`, as in the parent. The decrement action currently
computes

```
D5_110 = E_4 + E_16
D5_111 = D5_110 + E_18.
```

The following-control source already pays for

```
coefficient_tail_198 = E_18 + E_16.
```

Replace the first two additions by

```
D5_111 = E_4 + coefficient_tail_198.
```

The other replacement uses a paid decrement pair in a control sum. With
`L=linear_sum_164`, the parent has

```
D4_109 = E_14 + E_28
linear_sum_165 = L + E_14
linear_sum_166 = linear_sum_165 + E_28.
```

Keep `D4_109`, delete `linear_sum_165`, and set

```
linear_sum_166 = D4_109 + L.
```

Each change replaces two additions by one while reusing a register that
already has other consumers. Both identities hold over arbitrary integers,
including negative selector values. Their proof uses only associativity
and commutativity of addition; no one-hot or bit assumption is needed.
The two shared pairs depend only on the displayed edge leaves. The changed
source can therefore be topologically sorted without a cyclic dependency.

The removed registers can be restored exactly as

```
D5_110 = E_4 + E_16
linear_sum_165 = linear_sum_164 + E_14.
```

Every retained register equals its old value by induction through the
source. Consequently every old residual and factor, and either complete
finalizer, is identical. Erasing or restoring the two computed diagnostic
registers does not add or remove any supplied witness.

## 2. Guarded source interfaces

`rewrite(old)` accepts only a complete canonical selector380 packet in
one of its three forms (`fields`, `range_unit`, `units`) and either of its
two program interfaces. Exact equality to the canonical parent includes
the supplied domains and all public metadata.

The local `rewrite_rows(old_packet)` helper checks the seven involved
literal rows and returns a topologically sorted source list. Each erased
prefix must have exactly its displayed sole consumer. Recursive guards
reject exports through supplied parameters, auxiliaries, ordinary or full
comparisons, outer pairs, factors, group products, public registers,
interfaces or native restoration metadata. The helper verifies the source
before and after rewriting and the exact two-addition decrease. It leaves
all metadata and domains to its caller.

This row helper is an exact local graph identity, not a standalone theorem
that an arbitrary host is a complete universal compiler. A separate host,
such as a factor-partition builder, must guard its own complete canonical
base before inheriting that theorem. This packet emits only the six parent
forms; it does not modify or reoptimize the frozen partition packet.

Both reused values and both changed outputs have degree one in the supplied
coordinates. Every retained operand bound is therefore unchanged. The
checker requires equality of the complete inherited degree dictionaries
for both finalizers in every context, including the guarded main-norm
cancellation. These numbers remain propagated upper bounds, rather than
claims of exact polynomial degree.

## 3. Literal ledgers and verification

Every entry retains50 positive witnesses. Product-finalizer counts are:

| Program parameters | Form | Certificate | Comparisons | Polynomial | M | A | Degree bound |
|---:|---|---:|---:|---:|---:|---:|---:|
|one|fields|369|4|380|142|238|21540|
|one|range unit|371|3|379|142|237|21549|
|one|all units|377|1|378|141|237|21549|
|two|fields|368|4|379|143|236|40690|
|two|range unit|370|3|378|143|235|40706|
|two|all units|376|1|377|142|235|40706|

For `fields` and `range_unit`, the SOS and product finalizers have equal
operation counts. For `units`, squaring the single residual adds one
multiplication, giving379 or378. The corresponding SOS degree bounds in
table order are43016,43034,43098,81256,81288,81412. Every final source has
all gates live, and every one loses exactly two additions and no
multiplications from its own parent.

The [receipt](korec_packed_selector_sharing378.json) records the complete
six product schedules, both finalizer ledgers and their source hashes.
Run `python3 korec_packed_selector_sharing378.py`; `--write` regenerates it.
Author receipt generation and fresh replay pass. Across the six contexts,
384 complete retained-register/restoration maps include192 signed
assignments. Both finalizers give768 whole-output identities, including384
signed cases. Two direct scalar selector sums also verify each changed
output. Seven malformed callers exercise extra consumers, nested exports,
a changed reused sum, missing comparisons and attempted repeat application.
These are exact source/component audits; no complete Pell tuple is claimed.

The bounded discovery scout represented183 existing homogeneous selector
forms with integer-polynomial coefficients in D and tried120 eligible
one-gate replacements. It found these two distinct savings. That search
is not an optimality proof for other addition circuits or control codes.

Independent full proof/source review and a fresh replay pass without findings.
A separate executor verifies288 complete retained-register and manually
restored-prefix maps (144 signed), including24 assignments with every
selector zero, and576 complete outputs (288 signed) against both the parent
source and independently evaluated scalar finalizers. Twelve closure,
opcode and complete-degree audits pass; naive propagation also preserves
every retained register degree. Its33 malformed local-helper callers and
two malformed canonical callers are rejected. The three local links and
whitespace pass. A second full proof/source review and final fresh replay
also pass, confirming the twelve ledgers and signed-check scope. Neither
review claims complete native Pell fixtures. Source and receipt are unchanged
by this provenance addition.
