# Physical reductions: complete arithmetic contexts and finite negative searches

This packet contains the physical-machine work associated with **PA194H5X**.
It does **not** contain a successful 193-state blank-start consistency machine.
The principal result is a stronger, reproducible finite search on the newly
constructed 194-state machine, together with independent whole-tape symbolic
coverage of its arithmetic routines. These results support the engineering
audit; the enclosing article gives the logical calibration of PA194H5X.

Repository comparison is pinned to
`8d31445d858761a8f6150c2e5012adae8895e932` of
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt).
The new machine itself is included as a frozen input. Native controls are
preserved: start 74, halt 254, 194 working controls, 388 transition rows.
The halt label is not included in the working-state count.

## What the universal context calculation proves

Each source command is executed with nine arbitrary natural-valued registers,
an arbitrary nonempty finite spare-register list, and an arbitrary nonnegative
gap parameter. Unary runs have affine symbolic lengths. Four one-block list
lemmas are rederived from the literal transition rows, and the complete source
execution uses them by induction on finite lists. There is no arithmetic-box
oracle in `collect_box_contexts.py`.

To collect a 13-cell window (radius 6), run lengths are capped only after every
possible boundary and interior window is represented. An arbitrary list traversal
is split into an already-consumed prefix, one arbitrary current block, and an
unconsumed suffix; either outer list may be empty. Both orientations and the
B/C block families are included. Correlations between separate affine atoms and
the two sides of the head are discarded, which enlarges the window set.
The collector also includes every interior position of an accelerated constant-
symbol scan. These are universal symbolic checks, not simulations on small
sampled register values.

For PA194H5X the fresh run checks **4,786 source outcomes**, uses **1,110,183
symbolic steps**, and expands **2,916 contextual list traversals**. It yields
18,539 arithmetic-box windows. Combined with the non-box source collector and
every exact blank-initialization window, the complete invariant contains
**50,873 windows across all 194 controls**. Blank initialization is checked by
exact complete finite-support tape equality after **57,922 literal steps**.

The finite-window set is an overapproximation used by the searches below. Its
construction and the resulting search transcripts are executable mathematical
evidence, not an end-to-end proof-assistant derivation of the iPRA consistency
equivalence. In particular, this packet makes no lower-bound claim about the
number of states required by an arbitrary consistency machine.

## Fresh searches on PA194H5X

All the following searches found **zero reductions to 193 states**.

| Search family | Explicit domain | Recorded result |
| --- | --- | --- |
| Contextual two-control quotient | All 18,721 unordered pairs; both retained rows synthesized; radius 6, at most 160 detour steps | 26,200,136 row-action trials; 176,844 joint row pairs; no hit |
| Incoming-edge elimination | All 193 non-initial deletion targets; each incoming edge may choose its own write, direction, and successor and rejoin a later unchanged working-state endpoint | 197 incoming-edge stages; 132,784 action trials; no hit |
| Shared history selector | Two old history-tagged pairs replaced by two representatives and one shared selector; arbitrary exterior tape remains untouched; 63-step two-cell limit | 14 eligible pairs; 672 configurations; 259,392 selector-row trials; no joint survivor |
| Physical register allocation plus tagged-reader folding | All 9! = 362,880 physical allocations, with every eligible non-arithmetic reader considered | Every allocation has maximum matching size 9; none supplies the tenth fold needed for 193 states |
| Coupled quotient and compensating row | Fixed native 301-to-88 quotient; every one of the other 384 transition rows may be synthesized jointly with the two retained rows | 70,582 joint triples; 1,768,875 local checks; no hit |
| One neutral row, then a quotient | All 343 single-row neutral nominations are generated; the 59 belonging to AX readers or arithmetic boxes are followed by the full quotient search | 1,104,539 control-pair searches; 1,546,613,992 row trials; 10,471,071 joint row pairs; no hit (heuristic nomination) |

Synthesized row actions choose a write bit, a move direction, and an existing
remaining working successor; an ensuing detour may use an unchanged halt edge.

The last row deliberately has a weaker status than a completed equivalence
certificate. A simultaneous mutation could introduce contexts absent from the
frozen original set. Any survivor would therefore have required a fresh complete
source proof or a combined local simulation certificate. There were no survivors.
A radius or step cutoff is only a search restriction; it is never interpreted as
proof of an infinite execution.

The allocation screen uses the precise three-step previous-bit folding rule:
one incoming history bit chooses which old control a merged reader represents.
A bipartite matching counts disjoint eligible pairs. The screen does not search
arbitrary tape encodings, longer folding relations, or a newly designed runtime.
The coupled-row screen was also run on the earlier PA194AX11GH family with its
newly refined arithmetic windows; its negative receipts are retained separately.

## Secondary PA194JH5X screen

The second new machine was screened separately using its freshly regenerated
32,142 non-box source windows, conservative blank-tape arithmetic windows,
and all 4,794 symbolic source outcomes. This secondary screen does not claim the
additional arithmetic-window refinement performed for PA194H5X.

* All 18,721 control pairs were tested: 25,551,656 row-action trials and 183,698
  joint row pairs, with no hit.
* Incoming-edge elimination and the shared-selector screen also found no hit.
  The latter has 15 eligible history pairs, 752 configurations, and 290,272
  selector-row trials.
* All 40,320 allocations fixing logical register 0 at physical position 6 have
  maximum tagged-reader matching size 9. Its raw parent has 203 controls, so
  this family supplies no tenth fold and no 193-state result.

The native/source inputs and compact receipts are included. The enclosing
package supplies this machine's independent literal verification and logical
proof.

## Focused shorter-header audit

The secondary source has maximum path length 34. Its full literal contracts
also hold with minimum header 36: 4,794 outcomes for both the 194-state table
and the fixed 193-state Runtime193 core. The accepted table still initializes
a 48-cell header after 57,922 steps, which is gap 12 in the new convention.
All 194 working controls occur in source contracts, so none is used solely
for initialization under the retained universal source specification.

For the transferred 193-state core, exact finite traces classify all 193 blank
start controls: 2 halt and 191 escape on self-loop rays, by at most 93 steps.
Across all starts, its 10 visits to boundary 84 each contain at most 4 ones.
Any canonical frame needs at least 12 ones (two markers and at least 10 unary
blocks), independently of header length or source site. Thus changing the
header convention cannot fix this core's initialization. This excludes only
the specified fixed core and start choices, not further bootstrap rewrites
or arbitrary 193-state constructions.

`header_feasibility/README.md` gives the small replay commands, 20-case source
control-usage witness, exact rejection traces, full smaller-header receipts,
and the explicitly uncertified 34/35-cell attempts. The independent trace
replay has no simulation time cutoff in its conclusion.

## Additional append-routine experiments

The spare-register append mechanism was explored as a different physical-design
route. On PA194AX11GH, 35,696 one-row arithmetic mutations were screened against
27 small literal register-operation cases, looking for a uniform appended value
from 2 through 8. Seven mutations passed the first increment case, and none passed
all cases. The run executed 728,755,426 literal transitions including its baseline
check. This is a **bounded discovery experiment**, not a universal rejection theorem.

A separate local two-row synthesis assigned both `(66,0)` and `(198,0)` in all
602,176 ways over the existing working successors. It looked for a larger unary
spare block while preserving the old surrounding tape, with a 160-step local
limit and positions -5 through 12. No candidate passed even the first local case.
It executed 10,495,179 literal transitions. A positive result would still have
required full arithmetic, source, startup, and logical checks.

## Reproduction

Python 3.10 or later, a C++17 compiler invoked as `g++`, and the standard libraries
are sufficient. No repository checkout, network access, Lean installation, or
third-party Python package is required.

From this directory:

```sh
python3 -B replay.py --work /tmp/pa194-runtime-replay
```

The default run checks all input hashes, compiles the programs, verifies positive
controls for the new synthesizers, and reproduces the main quotient,
incoming-elimination, and shared-selector counts. For the longer finite searches:

```sh
python3 -B replay.py --extended --work /tmp/pa194-runtime-extended
```

To regenerate the universal window sets and compare their exact bytes:

```sh
python3 -B replay.py --regenerate-contexts --work /tmp/pa194-runtime-contexts
```

The extended and context options can be combined. The command-line programs can
also be run separately; their argument shapes are visible in `replay.py`.
`results/` keeps compact receipts and frozen windows, rather than enormous search
traces. `positive_control/` contains a deliberately redundant machine for which
the two new local synthesizers find the expected reduction.

## Attribution and limits

`PROVENANCE.json` identifies the pinned repository inputs and inherited tools.
The source-context executor, literal affine/list interpreter, and original
quotient/neutral-row screen retain the upstream notices in `licenses/`.
The contextual list-window collector, incoming-edge eliminator, coupled-row
synthesizer, generalized shared-selector screen, allocation matcher, append
experiments, and portable replay orchestration are new work in this packet.

No successful run of these search programs establishes PA consistency. No empty
hit file proves 194 states optimal. The exact new 194-state machine, its source
program, and its logical interpretation are separate deliverables of the enclosing
research package.
