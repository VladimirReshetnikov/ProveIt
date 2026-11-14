# Bounded startup repair of the inherited 193-state runtime

**No accepted 193-state blank-start consistency machine was obtained.** This
directory records three new bounded searches, their inputs, and positive controls
for the frame detector. It is negative research evidence, not a lower bound.

The inherited runtime has 193 working states. In native numbering it merges 301
into 88 and changes `88/0` to `0 L 51` and `51/0` to `0 R 122`. The source packet
reports a 4,780-outcome universal source-step certificate on canonical frames, but
the unchanged blank startup fails. The appended-zero input additionally changes
`198/0` to `0 L 40`. These input tables are rejected blank-start constructions.

The source is the pinned ProveIt commit
`32d0d8b7d93a63ad4106c18cdb29b37927acdad2`, archive
`docs/incoming/pa194_ax11h_research_2026-11-14.zip`, member directory
`pa194_ax11h_research_2026-11-14/research/runtime193/`. Source hashes and the
original notices are included. `source_reference/` contains that packet's README
and result summary to distinguish inherited work from this extension.

## New results

All three searches use the same fixed pool of 327 possible transition-row edits
and all 3,673 source-site path templates. They permit four distinct changed rows.
The literal simulation limit is 200,000 transitions per run; the detector checks
configurations before that limit. They also stop at the finite tape-window and
one-count bounds described below.

| Experiment | Quadruple/start cases | Runs including preparation | Literal transitions | Frames |
|---|---:|---:|---:|---:|
| Native start 74, inherited detector | 106,694 | 119,534 | 10,827,753,922 | 0 |
| Start 74, append-zero input, inherited detector | 103,375 | 115,953 | 9,589,305,357 | 0 |
| Nine first-write starts, corrected detector | 226,546 | 248,457 | 25,275,985,412 | 0 |

The first two extend the incoming packet's 20,000-step experiments. Their
quadruple phases fix start 74; their baseline and single-edit preparatory phases
still include all 193 native working controls. The third experiment has 121,405
certified outward-ray exits, five finite halts, and **127,047 unresolved finite
limit exits**. The exact counts for all phases and experiments are in
`summary.json` and the original logs.

Quadruple counts refer to distinct edit-set/start pairs surviving trajectory
row-encounter filters, not all formal four-element subsets. Baseline and
single-edit simulations are shared preparations. The experiments overlap and
their totals should not be read as disjoint candidates.

## Why nine starts cover all blank starts in this edit family

Until the first one is written, every tape square remains zero. A blank run
either never writes a one, in which case it cannot reach one of the sought
frames, or reaches a control whose read-zero transition writes one. Starting
directly at that control produces the same remaining run up to translation and
with no greater elapsed time. The runtime's possible controls are
`0, 4, 16, 35, 66, 74, 97, 198`; the entire edit pool adds only `302`. The new
`quad_firstwrite.cpp` retains all controls for table initialization but uses
these nine possible first-write controls as starts. This reduction is specific
to the supplied table and pool. Finite window exits remain unresolved.

## Detector correction and controls

The inherited detector required at least thirteen ones before inspecting a
frame. A minimal frame for source site 0, path `000000`, can have exactly twelve
ones: the left marker, the header delimiter, and ten zero-valued unary blocks.
The new detector lowers the preliminary threshold to twelve. A synthetic
139-transition diagnostic writer produces exactly this frame. The corrected
detector accepts it and the inherited detector rejects it. The diagnostic
writer is only a test, not a consistency machine.

The production nomination criterion permits header distance at least 36. No
universal runtime theorem at that distance is claimed. A hit would still need
a sufficient semantic seed and full physical source verification, including
verification that the selected row changes remain correct together. The word
`safe` in the inherited `safe_edits.tsv` filename does not certify arbitrary
compositions of its entries.

For a stronger positive control, the corrected detector is set to the proved
header distance 48 and run on the accepted primary 194-state table. It recovers
the whole known seed at exactly 58,154 transitions: native state 84, head -2,
site 25, physical registers `(0,0,0,0,0,0,2,0,0)`, and 26 unit spare blocks.
At the permissive distance 36 the inherited detector instead first nominates
a shorter frame at 24,866 transitions; that earlier nomination is not asserted
to satisfy the accepted startup theorem. The JSON `gap` field is excess above
the detector's configured minimum, not the full header distance.

## Reproduction

Requirements: Python 3 and a C++17 compiler (`g++` by default). No external Python
packages, repository checkout, or binaries are needed. The wrapper creates
fresh outputs and never changes the frozen logs or inputs.

```sh
python replay.py --output /tmp/pa-startup-controls
python replay.py --full --output /tmp/pa-startup-full
```

The default verifies input hashes, checks the recorded integer totals against
`summary.json`, compiles both positive-control variants in the output directory,
and compares their output byte for byte with the recorded controls. `--full`
also compiles and reruns all three searches, comparing every integer count
while ignoring elapsed wall time. The full replay may take several minutes.

Equivalent individual search invocations, after compiling the sources with
`g++ -O3 -std=c++17`, are:

```sh
./quad_allframes runtime193.native.tm safe_edits.tsv all_source_templates.tsv 5 200000
./quad_allframes runtime193_append0.tm safe_edits.tsv all_source_templates.tsv 5 200000
./quad_firstwrite runtime193.native.tm safe_edits.tsv all_source_templates.tsv 6 200000
```

## Scope limits

The finite simulator has a 50,001-cell array with origin 25,000 and returns a
limit exit when its head leaves the inner safety margin, when the one count
exceeds 20,000, or when the step bound is reached. All such exits are unresolved.
A certified ray is a same-control outward transition into an infinite blank
region and is a direct nontermination witness for that edited startup.

The search does not exhaust arbitrary transition edits, different encodings,
other compilers, or all 193-state Turing machines. It does not establish a new
iPRA calibration theorem and does not repair the remaining calibration gap of
the parent design. No accepted sub-194 machine or state-minimality result is
claimed.
