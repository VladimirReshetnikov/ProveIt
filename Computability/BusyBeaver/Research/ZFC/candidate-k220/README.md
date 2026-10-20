# A 220-state binary Turing machine for Con(ZFC)

This machine improves the 221-state construction by re-encoding a decoder edge,
rotating its source twice, and merging two states using the preceding tape bit.
The resulting **220 working states and 440 transition rows** implement the same
proof-search program. Its ordinary mathematical argument gives blank-tape
nonhalting equivalent to Con(ZFC). **The exact 220-state Lean theorem and the
internal PA equivalence remain open.**

The public table is [k220.tm](k220.tm): binary alphabet, blank symbol 0, one
bidirectional infinite tape, moves L/R, initial state 0 and head at cell 0.
Working states are 0–219; 220 is the halt state and is not counted. Each row
has `state read write direction next`. Canonical SHA-256:
`f80c57e800d4f999d9b4902a8e96bd36d1b6180b3ad322ca8ed0ab67b47f2a5f`.
The [native table](k220.native.tm) keeps predecessor labels (halt 254), and
[canonical_map.json](canonical_map.json) records their correspondence.

## Construction and validation

Source 138, `K220_Construction_2026-10-20.zip` (arrival `7677a1f62f`), starts
from Source 132's K221 table. At prefix `11101001001101`, it changes the
association of four closed blocks from `((A,B),(C,D))` to `(A,((B,C),D))`.
Re-encoding the non-pure edge at native state 132 permits these rotations;
the primitive word and guarded control-flow graph remain identical. Native
state 202 then merges into 171, with helper 7 distinguishing predecessor
bits and restoring the exact tape/head configuration in three steps on read 0;
the common read-1 branch takes one step.
This fold is justified at valid source-decoder entries. The complete final
runtime check also covers the arithmetic uses of these states.

Fresh intake checks on 20 October 2026 pass:

| Check | Result |
| --- | --- |
| Reconstruction | Exact delivered source and native/canonical tables |
| Source | 208 distinct subtrees, 4,744 leaf occurrences, maximum depth 38 |
| Complete symbolic runtime | 6,167 cases; 1,516,421 symbolic rules; all 440 rows; positive duration |
| Blank initialization | 409,835 steps, exact entire tape and head checked |
| Independent audit | Source/CFG identity, fold blocks, symbolic coverage and startup |

The symbolic runtime quantifies over arbitrary natural register values,
header gap and finite spare-block lists; it is not a finite sampling of
register values. Exact blank initialization enters canonical dispatcher 22
(native 84) at head −5 with logical registers `[3,0,0,0,3,0,0,0,0]`.
The ordinary consistency calibration is inherited through the unchanged
source program. No recursive ancestor suite or proof-assistant build was
run for this intake.

## Three equivalent layouts

Source 139, `K220_Alternatives_2026-10-20.zip` (arrival `bf01dd349a`), supplies
three further 220-state tables. They have the same source, but distinct
canonical transition tables:

| Variant | Native change |
| --- | --- |
| [row103](variants/row103/k220.tm) | `103/1: 0L162 → 0L142` |
| [row157](variants/row157/k220.tm) | `157/1: 1L148 → 1L187` |
| [both](variants/both/k220.tm) | Both changes together |

Fresh positive-block equivalence and independent radius-five window checks
pass for all three, as do their exact 409,835-step startups and canonical
reconstruction. The equivalences hold from initial state 0 on every initial
tape; they are not equivalences from arbitrary control states. The changes
compose but do not reduce the state count. Separately delivered occurrence
and six-leaf no-op experiments remain uncertified research specimens.

## Evidence, reproduction and credit

The [intake reconciliation](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-185.md)
records the source changes, theory investigations, counterexamples, inherited
proof scope and all 13 fresh checks. Its
[recovery/replay guide](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-185-reproduction.md)
restores the complete packages from committed archives and runs the selected
checks on copies. Delivered code, data and notices are preserved as Sources
138–139 of that report; [provenance.json](provenance.json) binds this publication.

Credit remains with the submitted constructions and their predecessors:
Elliot Glazer's K calculus/development, Mira's 254-state construction,
Jeff's busy-beaver development, Andrew James Wade, BusyCoq, the Coq Library
of Undecidability, and ProveIt's accumulated compiler and machine reductions. See the delivered [attribution](ATTRIBUTION.md),
[alternative notice](NOTICE-alternatives.md), [license](LICENSE), and
[inherited notices](licenses/). No priority or minimality claim is made.
