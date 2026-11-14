# Repairing the 193-control runtime core

These files record scoped finite searches. They do **not** provide a new
193-state blank-start consistency machine, nor a lower bound.

The inherited runtime table identifies native state 301 with 88 and changes
`88/0` to `0 L 51`, and `51/0` to `0 R 122`. Its complete source-contract
certificate is in the named incoming packet. On canonical unary register
frames the latter change has a two-step justification because the cell
after the delimiter is 1. During blank initialization that premise fails.
The unchanged native start 74 reaches an outward blank ray.

The named incoming packet is
`docs/incoming/pa_sub194_research_2026-11-13.zip` at ProveIt commit
`1c9524d8bf2e0a27b9a16ff622359927f536e663`.
It already screens individual row edits. This extension couples two, and
then three, candidate edits. It makes no priority claim relative to all
historical searches in every research packet.

## Candidate pool and limits

The input is the corrected radius-six pool of 346 candidate row rewrites:
327 outside the arithmetic boxes, and 19 speculative box-row changes.
The startup screen deliberately includes the latter as possible proposals;
it makes no claim that they preserve arithmetic. Nor is simultaneous
neutrality inferred from single-edit screening. Any positive hit would
require a new universal simulation proof and logical calibration.

Only edits to distinct `(state, read-bit)` rows may be combined. Every
run has an all-zero two-way tape. The frame detector checks native control
84, the entire finite tape support, a source site among 25 through 44,
padding at least 48, nine arbitrary register values, and at least one
arbitrary spare register. It accepts more stores than the mathematical
startup theorem: it does not require the three proof-store registers to
be zero. Thus an accepted frame would still be only a candidate.

Limits: 200,000 literal steps per run, absolute head displacement at most
20,000 before another step, and finite support size at most 20,000 before
another step. A ray is certified only when the head is outside the finite
support and the zero-read transition graph moves perpetually in one fixed
direction. Runs that hit a finite limit remain undecided.

The unchanged primary PA194 table is a positive control: the same frame
detector recovers its complete source-site-25 seed after exactly 58,154
steps. Two distinct no-op row edits exercise the pair-search path. The
complete detected tape and register file are recorded.

## Recorded pair searches

| Scope | Tables | Starts/table | Runs | Literal transitions | Halts | Rays | Bounded | Frames |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Two edits, start 74 | 58,485 | 1 | 58,485 | 87,558,362 | 0 | 58,072 | 413 | 0 |
| Two edits, every native control | 58,485 | 193 | 11,287,605 | 2,173,634,233 | 117,274 | 11,159,792 | 10,539 | 0 |

The all-start screen contains the start-74 screen, so their run totals
should not be added to count distinct trials.

The triple search fixes start 74. It skips a triple only when none of its
edited rows occurs anywhere on the unchanged blank trajectory. That
trajectory reaches the one-state outward ray `35/0`; its subsequent row
set is therefore exact. `search_triples.cpp` checks that ray premise.
There are 6,440,096 distinct-row triples. The exact unchanged-ray argument
eliminates 4,225,362 of them. The other 2,214,734 blank runs execute
16,183,877,637 transitions: 2,134,087 reach certified outward rays and
80,647 stop at a finite bound. None halts or reaches an accepted full frame.
The complete counts are in `recorded/log_triple.txt` and `summary.json`.
The frozen run took 386.523 seconds in its execution environment; elapsed
time is not a reproducibility requirement.

## Local merge synthesis

The inherited runtime reduction suggests modifying one helper row while
merging 301 into 88. The two-cell synthesis checks all two-cell inputs
with history bit 0 for state 301 and 1 for state 88. It tries 592,896
patches and finds 11 local identities. They use existing scan controls;
the known helper 51 is the one with the documented runtime justification.
The other ten alter arithmetic operations and are not accepted machines.

The radius-four synthesis allows excursions anywhere in a nine-cell
window, checks every assignment of its bits, allows at most 100 steps,
and searches a helper row encountered on the first failing unmodified
local trace. It tries 3,719,496 patches and finds 13 local identities.
The two additional non-box identities change row 31/0 or 70/0. Both fail
the complete source checker, at source outcomes `(16, None)` and
`(56, (2, True))` respectively. These are rejected experiments.

A separate source-context synthesis uses 8,339 recorded symbolic windows,
including interiors of accelerated constant-symbol scans. Arithmetic-box
rows are excluded from helper mutation. It tests 3,100,352 patches and
finds no local simulation. Its context envelope and bounds define its
scope; it is not an exhaustive proof against all compiler changes.

## Portable replay

Python 3.10+, a C++17 compiler, and the Python standard library suffice.
Run from this directory; use a fresh output directory outside the packet:

```sh
python3 replay.py --mode positive-control --output /tmp/pa-frame-control
python3 replay.py --mode pairs-all --output /tmp/pa-pairs-replay
python3 replay.py --mode pairs74 --output /tmp/pa-pairs74-replay
python3 replay.py --mode triples74 --output /tmp/pa-triples-replay
python3 replay.py --mode helper --output /tmp/pa-helper-replay
python3 replay.py --mode helper-window --output /tmp/pa-helper-window-replay
python3 replay.py --mode source-helper --output /tmp/pa-source-helper-replay
```

The driver verifies input hashes, compiles to a temporary directory,
keeps the frozen receipts unchanged, compares integer totals or exact
solution lists, and writes fresh observations to the chosen output.

The source-context collector and universal symbolic compiler are inherited
from the named packet. This smaller replay bundle includes their resulting
context envelope and rejection receipts, not a second complete copy of
that compiler. Replaying the three source-level receipts from first
principles requires that attributed source packet. The finite startup and
local-synthesis replays above are self-contained.

See `PROVENANCE.json` and `licenses/` for source attribution. None of these
programs constitutes a Lean/Rocq kernel theorem or closes the inherited
iPRA calibration and physical-simulation gaps.
