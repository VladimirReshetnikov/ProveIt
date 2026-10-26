# A global exclusion of the marker1004 offset19

This note proves the global alignment step for a prospective marker1004
layout. It does not claim a complete new fixed-tuple certificate or a
smaller equation. The accepted marker1005 construction and its frozen
[complete low-padding proof](../low-padding-independent/PROOF.md), SHA256
`ad952c6f1717a69e6b489e8c7af0bb52ce09414b78cc994b892b6e7f996d06f6`,
remain unchanged. ROOT proposed the global label recurrence; this note
independently checks its derivation and proves the needed finite-cycle
obstruction. The earlier compatible local pattern is preserved as a
correctly scoped local negative control.

## Prospective geometry and dependency order

Keep all942 selectors, all34 weighted labels, Boolean dummy977, shared
copy exponent18 and spatial exponent9. Move only the zero-weight marker
and bare marker monomial from1005 to1004, and the sole clause from1956
to1955. The physical support becomes

    Es={0..950} union {960..985} union {1004}.

The marker's other bare and spatial predecessors986 and995 are absent.
The reflected kernel begins at1955−985=970. For every output h<=1004,
each reflected coefficient index1955+f−h is at least951, beyond all odd
selector coefficients. Its contribution is therefore even and bounded
by the sum M−1024 of the label weights, without any decoding premise.
The same unconditional low reset

    M-1024+3+rho/2+29<rho

protects the marker and every copy test. In the forced Start cell the
marker's non-temporal parity is still one. Boolean physical digits then
exclude every nonzero fractional binary phase before using the clause.

At the clause1955 the bare marker's source951 is absent; all other bare
and spatial sources are absent too. Its temporal digit is Boolean after
phase recovery. The complete count lemma with k+tau_c<=30 therefore
recovers zero or one selector and all34 labels in every cell, without
assuming temporal cleanliness. The nine north-copy tests960..968 have
no reflected contributions because the first reflection is970.

The marker bounds the remaining integral field offset by
`r=1004-f`, with f physical. Thus r=0 or19<=r<=1004. The forced Start's
south tests reject r>961 by absent wrapped preimages. Offset20 is still
rejected by the exact tile941 south-bit0 contradiction; every offset
21..961 forces two selectors in the same already decoded cell. The only
additional case to exclude is r=19.

## Deriving the whole-cell recurrence at offset19

Let S_i be the decoded complemented south color of cell i, an integer
in0..511; an empty cell has S_i=0. Let delta_i be the Boolean indicator
of selector941 in that cell. The exact retained calibration gives

    delta_i=1 implies S_i=74,
    S_Start=510.

At offset19 the temporal preimages of all nine north-copy fields960..968
are941..949. They do not wrap a B-cell boundary, so the same temporal
cell permutation pi supplies every one of the nine source bits. Their
parity equalities therefore read

    S_i = (2*S_(pi(i)) mod512) + delta_(pi(i)).          (1)

The low bit comes from selector941; the next eight bits come from the
source south bits0..7. The displayed sum is an exact integer in0..511:
the doubled residue is even and at most510. This uses all nine copy
tests, including the Start's zero south bit0, and applies in every cell.
The permutation pi is a fixed rotation of the finite B-cell word. No
occupation or uniqueness-of-Start assumption is needed.

## The finite graph has only the zero cycle

Consider the directed graph on0..511 with every ordinary edge
`s -> 2s mod512` and the one additional edge74->149. Relation(1) follows
only edges of this graph when traversing each temporal permutation cycle
in the corresponding direction. The graph deliberately allows the
ordinary edge74->148 even if the decoded language restricts it; proving
the obstruction in this larger graph suffices.

A walk with no exceptional edge reaches0 after nine ordinary doubling
steps. If it uses the exceptional edge, its continuation is forced until
the next occurrence of74. But the entire ordinary orbit of149 is

    149 -> 298 -> 84 -> 168 -> 336 -> 160 -> 320
        -> 128 -> 256 -> 0 -> 0.

It never visits74. The other branch from74 is

    74 -> 148 -> 296 -> 80 -> 160 -> 320 -> 128 -> 256 -> 0.

Hence no directed closed walk can contain the exceptional edge, and a
closed walk consisting only of ordinary doubling edges can contain only
zero. The sole directed cycle is the loop at0. Every finite permutation
cycle obeying(1) therefore has S_i=0 throughout. This contradicts the
forced Start value510 and excludes r=19 globally.

The earlier local assignment using new tile3 with complemented south511
and east247 still reproduces the Start-copy tests at one cell. It cannot
extend around an entire finite temporal rotation. The local result never
claimed such an extension, so the global exclusion does not contradict
or modify its frozen certificate.

## Reproducible finite receipt

The independently authored [probe](probe.py) and its complete
[certificate](CERTIFICATE.json) authenticate the frozen source decoder,
all942 tiles, every513 calibrated bit transition and every943 decoded
state transition including the empty state. They record all512 graph
vertices with a strictly decreasing nonzero ranking; its maximum is11.
The local511-to510 edge is retained. A negative control shows why the
exact exceptional-tile calibration matters: allowing an uncalibrated
odd branch at511 would create a nonzero self-loop.

The proof author read the entire newly authored program before running
its normal and optimized read-only checks. Both reproduce the exact
certificate, with explicit exception gates active under optimization.
This finite receipt corroborates the ordinary graph argument above; it
does not assert the missing complete marker1004 controller or tuple.

| Artifact | SHA256 |
| --- | --- |
| Probe | `db5520034a989940df36055db26a6bbeaaceddb85292a6eedd78eb82262afb69` |
| Certificate | `0280bb9a03c796724227d1fc15f9fcfb51e22533872f4509807069886b91f190` |

## Scope of a possible successor

This closes the new alignment case for marker1004. The sole predecessor
would be exactly `Aadj+x_950` at1954, and the maximal product would be
2959. The existing low-padding block4*G_917 remains below every reflection
and copy test. These are ordinary support consequences, not a new complete
controller or whole-port receipt.

At L2963 this change need not reduce the minimal unsigned byte count,
and the printed exponents have the same digit lengths. The shorter odd
length2961 has repeated factors and fixed primes where B squared minus1
is not a unit; the currently certified controller theorem therefore does
not apply there. This is an obstruction to that theorem's hypotheses,
not a general impossibility result for a different controller. No new
equivalence, global minimum, consistency decision or formal-kernel replay
is asserted by this scoped note.
