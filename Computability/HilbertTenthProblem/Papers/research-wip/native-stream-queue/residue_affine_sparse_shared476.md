# Paid selector and payload sharing in the U21 residue-affine compiler

The complete literal source in [the receipt](residue_affine_sparse_shared476.json)
has **476 = 176M + 300A operations**, **67 positive witnesses**, two fixed
program parameters and ordinary positive input. It improves the pinned
[504-operation sparse residue-affine source](residue_affine_sparse_program_radix504.md)
by **28 operations: one multiplication and 27 additions/subtractions**.
The certificate portion has **456 = 169M + 287A** operations and retains
seven comparisons in the parent's convention. Every emitted row reaches
the complete polynomial output.

This is a polynomial identity on identical supplied coordinates, not a
relaxation of the residue graph, chronology, loader or native constraints.
Consequently the full positive zero sets are identical. The existing
U21 ordinary-input theorem and fixed program recipe transfer directly.
The inherited uniform degree bound is **at most 5160**; no exact degree or
minimal circuit claim is made. This independent substrate remains above
the separate 84-operation universal polynomial.

## 1. Fixed source and semantic boundary

The immediate parent is the default, shared, coupled-product source saved
in `residue_affine_sparse_program_radix504.json`. Its parameters are
`program`, `radix_program`, `input`; write them \(E,C,x\). Its valid fixed
recipe requires \(C\) to be dyadic, \(C\ge64\), and \(C>E>0\).
The universal compiler supplies \(E=3^e\) and chooses one such \(C\) per
program, independently of the ordinary positive input \(x\).

The parent uses the literal U21 table and 36 edge selectors. The paid
initial loader performs exactly \(x\) doublings, followed by the simulated
register-machine computation. Its residue-affine body and prime-payload
representation are detailed in the pinned
[factored compiler](residue_affine_sparse_factored.md). The current
height/radix is \(h=x+\eta\), \(B=Ch\); the computed positive scale, weak
repunit sign recovery, native AND bootstrap, remainder conditions and
chronological transports are all inherited unchanged.

The new source does not reprove the original universality theorem, relax
its program recipe, or claim a new simulation of a different machine.
It proves an exact arithmetic improvement to the saved complete source.
In particular it does not rely on the much weaker statement that a finite
bounded history can be encoded. The predecessor already pays an unbounded
history representation at fixed arity, including its ordinary-input loader.

All predecessor files were read as inert bytes. No predecessor Python
module was imported or executed. The new [standalone checker](residue_affine_sparse_shared476.py)
uses only the Python standard library and authenticates the seven files
listed in Section 6 before reading the saved source array.

## 2. Reuse the existing disjoint selector partition: save 25A

Let \(E_e=\widehat E_e-1\) for edge IDs \(e=0,\ldots,35\), and let
\(J=\sum_e E_e\). These are formal polynomial definitions; the following
identity does not assume selector typing or nonnegativity.

The parent computes the 35-addition prefix chain for \(J\). It also pays
for seven prime-class sums and a state pair elsewhere. Together with the
already paid loader pair and one singleton, these form this disjoint
partition:

| Already paid register | Edge IDs |
|---|---|
| `prime_selector_93` | 2, 3, 13 |
| `prime_selector_95` | 32, 33, 34 |
| `prime_selector_97` | 26, 27, 35 |
| `prime_selector_101` | 16, 17, 28, 30, 31 |
| `prime_selector_109` | 6, 7, 10, 18, 19, 20, 21, 24, 25 |
| `prime_selector_113` | 5, 8, 9, 14, 15 |
| `prime_selector_115` | 4, 11, 12 |
| `selectors_36` | 0, 1 |
| `control_codes__duplicate_state_6` | 22, 23 |
| `edge_29` | 29 |

The first seven are precisely the prime \(p>2\) classes; the last three
partition the prime-2 edges. The checker expands every row to literal
edge variables and verifies that the 36 IDs occur exactly once.

Keep the loader pair `selectors_36`. Replace the subsequent 34 additions
in the old population chain by nine additions joining the ten terms above.
The last addition still produces `selectors_70`, so every downstream
population use is unchanged. This saves \(34-9=25\) additions.
The reused class/state producers depend only on raw edge selectors. Moving
them ahead of \(J\) introduces no cycle and no arithmetic gate. All their
original paid rows remain live, and all 36 hat-to-selector subtractions
remain paid. Nothing is supplied as a free class sum.

## 3. Two adjacent exact identities: save 1M + 2A

The parent has already constructed

\[
R_3(P)=1+P+P^2
\]

in `repeat_odd_318`. It separately builds the same quantity as
`three_range_repeat_408 = 1 + P*(P+1)`, using the private multiplication
`range_repeat_shift_407`. Replace its sole consuming operand in
`all_ranges_427` by `repeat_odd_318` and delete those two private rows.
This saves one multiplication and one addition. All powers and other
repunits remain paid exactly as before.

For the joint payload identity use the parent's notation:
\(W\) is the quotient word, \(U=W+J\), \(V\) is the prime-weighted word,
\(S\) is the complementary remainder word, and \(I,D,T\) are the
increment, positive-decrement and positive-test selector sums.
The actual source has \(T=E_{14}\). It computes

\[
Z=J-I-D-T,\qquad C_{\rm common}=U+V-S-Z.
\]

Substituting the actual producer \(U=W+J\) gives the polynomial identity

\[
C_{\rm common}=W+V-S+I+D+T.
\]

The old \(Z\) chain costs three additions/subtractions and the old common
payload costs three more. The replacement computes \(W+V\), subtracts
\(S\), computes \(I+D\), adds \(T\), and joins the two results: five
additions/subtractions. The three private \(Z\)-producer rows disappear;
two new nonzero-action sums are paid. This saves one addition overall.
The \(U\) producer itself remains paid and live in the prime selections
and \(V\). Both final payloads, \(C_{\rm common}-Y_I\) and
\(C_{\rm common}-Y_D\), are unchanged.

Two surviving intermediate register names (`common_quotient_152` and
`common_remainder_153`) now hold different values. Neither is an exported
comparison or native cut; their only downstream use passes through the
restored `common_payload_154`. No equality of those two intermediate
values is claimed.

## 4. Complete identity, positivity and degree

The checker proves the three local identities by exact sparse polynomial
expansion over the appropriate formal input registers. It then compares
the whole parent and child expression DAGs, using only those proved
identities as replacements. Every other retained definition is checked
by exact expression congruence, including the actual native inputs,
all 72 native-prefixed rows, the eight-factor product and all six ordinary
residuals. All 20 finalizer rows are literal retained parent rows.
The two changed intermediate values identified above are explicitly excluded
from the same-value register claim; 464 other retained registers match.

Thus over any commutative ring,

\[
F_{476}(E,C,x,\mathbf w)=F_{504}(E,C,x,\mathbf w).
\]

In particular the identity map in both directions preserves every supplied
positive integer coordinate and the complete zero set, including native
witnesses. There is no reconstruction of a history, hidden additional
inequality, signed slack, or new witness needed for this transfer.
The parent's full ordinary positive-input representation on its valid
fixed recipes follows immediately. Its uniform polynomial degree bound
5160 also transfers from equality of the complete polynomials; the new
source is not credited with an unproved lower exact degree.

The default product source is the sole newly emitted array. Other parent
variants (unshared packing, alternate finalizers or uncoupled norm forms)
are not claimed as emitted successors in this packet.

## 5. Complete paid ledger and checks

| Source stage | Operations | M | A |
|---|---:|---:|---:|
| Parent certificate | 484 | 170 | 314 |
| New certificate | 456 | 169 | 287 |
| Unchanged finalizer | 20 | 7 | 13 |
| Complete new polynomial | **476** | **176** | **300** |

The emitted array removes 38 old register names and adds ten new ones.
The retained population register and three other definitions change as
specified in Sections 2–3. A fresh traversal verifies the instruction
count, binary arithmetic grammar, unique definitions, topological order,
all 70 free ports, identical 67-witness interface, and full liveness.
The receipt includes the complete 476 rows rather than a delta schedule.

Exact proof checks cover the complete selector partition, both forms of
\(R_3\), the joint payload cancellation and every downstream output.
Separate corroborating tests interpret both full sources on 32 signed
assignments modulo two primes and four signed rational assignments.
These are off-zero algebra tests; no actual accepting outer history or
complete positive native Pell tuple is materialized in this packet.
Because full polynomial equality is established symbolically, those finite
tests are not the basis of the positive-zero theorem.

Fresh normal and optimized replay commands are:

```sh
python3 residue_affine_sparse_shared476.py --root . --expect residue_affine_sparse_shared476.json
python3 -O residue_affine_sparse_shared476.py --root . --expect residue_affine_sparse_shared476.json
```

The receipt binds the exact helper bytes. The rewrite creates a fresh edited
range row and checks that the parent source remains byte-identical in memory
before running the independent parent/child comparisons.

The new checker uses explicit runtime guards (not optimization-removable
assertions), rejects duplicate JSON keys, and compares receipts by
canonical JSON bytes, preserving exact number types. The author ran both
replays from `/` using absolute source/root/receipt paths; both passed.

## 6. Frozen provenance

Every dependency below is read as data or text only. The first JSON contains
the complete immediate parent array. The proof notes supply its inherited
semantic context; no independent recertification of their entire historical
compiler chain is claimed here.

| File | SHA-256 |
|---|---|
| `residue_affine_sparse_program_radix504.py` | `d85b7985fb54b23950070515514e4e88a3d942c17aa7531320c306e1fe46f073` |
| `residue_affine_sparse_program_radix504.json` | `d089b8477f28b154e04fa149231e19c333dacd35f995829ac09395fb3a70c0eb` |
| `residue_affine_sparse_program_radix504.md` | `4c3e0545b8f7f025096a30170a1785d33da35b625e3aa8dacb1362a461d0a549` |
| `residue_affine_sparse_factored.md` | `b169236c449623049759b7ac0877b2202b3aba389ace8e06d31370396abb9ea7` |
| `residue_affine_sparse_scale538.md` | `0c6e6bd9606a6c6b1c70f21575784ac24ed9ff2f64ab788cc6c64b0106979623` |
| `residue_affine_sparse_terminal537.md` | `9deba23f3b210d730fd32a2a10aa886edc9637c4f8d26010cc0f0f55a7c7f6d1` |
| `residue_affine_sparse_control_codes.md` | `be133b5d93c082c3f3022e4b9990140ff3de71cf7202a7ba281a48e8c77d34da` |

New helper SHA-256:
`52e09d2b3474e37c6116e16b7a1ee59395a337a5ff381b4881ae616ecbaafddf`.
New receipt SHA-256:
`90e6e265ae1eb9a1cd1239255c14da3d3c6e5841f330f7a6220536d182778ba8`.
