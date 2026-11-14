# Additional PA196 engine and reader searches

No machine with fewer than 196 working states was found by these experiments.
This packet records bounded executable certificate searches. Its negative
results are not a lower bound for Turing machines and do not prove that a
195-state consistency machine is impossible.

## Reproduction

The input files needed by the scripts are included under `inputs/`. No network,
Lean installation, or external Python package is needed. Use Python 3.10 or
later; the full search also needs a C++17 compiler named `g++`.

Run the following from this directory:

```sh
python run_searches.py
python run_searches.py --all
```

The first command checks the baseline and rotated source contracts and the
rejected append-zero initializer. The second also regenerates the main
source-context files and repeats the principal searches. It writes new
`*.rerun.log` files, while preserving the recorded search logs. Search timing
depends on the host; iteration counts are the relevant comparison.

`symbolic_core.py` is an independent executable reconstruction of the runtime
checker. Its source is included for inspection. It is not a Lean theorem and
does not itself prove the PA consistency equivalence. The four register box
operations are used through their algebraic contracts; they are not expanded
one tape step at a time by this checker. `variant_core.py` reconstructs the
rotated source graph with two independent CFG resolvers from the included
`source_language.py`.

## Inputs and state conventions

The baseline table comes from James Chang's cited BusyBeaver design at
commit `407cdc356f6b586635e71ac92be394255f4bfea4`. Its SHA-256 is
`e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8`.
`inputs/BusyBeaver/PA196/Conjugacy.lean` supplies the dense-to-native control
labels, and `Program.lean` supplies the exact source tree.

Dense tables have working controls 0 through 195 and halt control 196.
Native tables use the historical sparse labels, with initial control 74,
dispatch control 84, and halt control 254. The rotated table retains the
same native-to-dense bijection. Both tables have 3,812 source sites and 4,959
primitive branch contracts. The rotated table is a different physical layout
of the same ordinal source CFG; its derivation and startup certificate are
documented in the enclosing report.

## Search models and results

### Instruction endpoints

The `macro_quotients.py` search redirects all incoming edges of one eligible
control to another without changing other rows. It checks each affected
instruction contract from the first differing control until the original
whole-instruction endpoint, allowing at most 1,024 symbolic updates. The
intermediate head positions and controls need not match the baseline. There
are 172 eligible controls outside the register-box set and dispatch control.

The baseline search rejects all 33,540 directed identifications after 35,753
contract trials. The corresponding rotated search rejects all 33,540 after
35,561 trials. These figures count early-rejected candidates, not a Cartesian
product of all candidates and all contracts.

`macro_row_blends.py` keeps the read-0 row of one control and the read-1 row
of the other, in both mixed orientations, while identifying the pair. The
baseline rejects 29,412 candidates after 79,124 contract trials; the rotated
layout rejects the same 29,412 candidates after 74,960 trials.

`edge_contracts.py` also tries deleting each of the 172 eligible controls by
independently replacing incoming rows with single actions matching a short
baseline walk. No deletion meets that restricted template.

These are bounded endpoint tests. Exhaustion of the candidate list does not
exclude a different row design, a longer simulation, changed data encoding,
or a different source invariant. Any successful candidate would still need
the register-box agreement check, the complete blank initializer, a total
source-runtime simulation, and the arithmetic proof transport.

### Two arbitrary replacement rows

`all_nonloop_contexts.py` extracts 25-cell windows, with radius 12, from the
symbolic primitive contracts and the finite blank initializer. Known bits
are recorded separately from opaque register data. It produces 152,196
windows at 167 eligible nonloop controls for the baseline and 152,352 for
the rotated layout. No inferred trace may read an unknown bit.

`full_two_row.cpp` identifies two eligible controls, replaces both rows of
the retained control with arbitrary binary write/left-or-right/target
actions, and allows the retained control to be revisited internally. Each
old step must be matched within 64 new steps inside the radius-12 window,
with the same tape and head position and the projected old target control.
This is a particular local simulation certificate template.

The baseline screen examines 27,722 directed control pairs, 21,734,048 first
row trials, and 60,990,496 paired row trials after the first-stage filter.
Six candidates pass a representative-context filter; all six fail a later
context. The rotated screen has the same number of directed pairs and
first row trials and tests 61,912,480 paired rows, again with six initial
survivors and none after all contexts. The final six baseline candidates
also fail the less restrictive whole-instruction symbolic test; the
counterexample sites appear in `full_two_row_macro_rejections.json`.

The helper searches permit either two disjoint folds sharing one new
dispatch control or three controls folded into a retained control plus
one helper. Both have a possible net saving of one control. No compatible
certificate was found. The triple-helper screen tests 82 eligible triples
on each layout; 27 pass its first helper-branch filter, and none pass both.

The complete context sets are packaged to make the screens reproducible.
The source extraction uses the register-box contracts and a conservative
unknown-data mask; it is an executable analysis, not a separately checked
proof of an inductive invariant.

### Physical register permutation

The physical order of the nine logical registers is
`[6,2,0,4,3,7,8,5,1]`. Eleven non-skip read-1 rows choose the logical
register through the nine-state skip chain. Their mapping is recorded in
`register_entry_analysis.json` and the dense-format `register_selectors.txt`.

`all_register_twofold.cpp` combines arbitrary two-row identification with
injective physical-register assignment. Assignments are introduced lazily
as selector rows are visited, so all bijections can be represented within
the search template. It tests 13,861 unordered eligible pairs, 10,867,024
first rows, and 30,514,848 paired rows. Three candidates pass the small
representative filter; none pass all stored windows.

This search reuses the baseline's local context obligations. It therefore
does not prove that every register reordering fails: a new physical order
can alter entry contexts or the initializer. In particular, merely swapping
the physical slots of logical D and H preserves all 4,959 symbolic source
contracts but does not reach the required clean initial frame within the
tested one-million-step prefix. That finite observation is a rejection of
the proposed initializer certificate, not a nonhalting proof.

## Rejected engine-tail experiment

Changing native row `198/0` from `1 L 40` to `0 L 40` changes the spare
register appended by increment. The existing blank initializer then reaches
native state 35 after exactly 76 steps, with head at cell 4 and ones only
at cells -3 and 1. Its row `35/0 = 1 R 35` gives an elementary induction:
the machine forever moves right into a fresh blank cell, writes 1, and
remains in state 35. Thus this particular altered blank-start machine has
PA-provable nonhalting. It is rejected as a consistency-machine candidate.
The exact 77 configurations are recorded in
`rejected_experiments/append_zero_initializer.json`.

This illustrates why a source-runtime contract alone is insufficient:
the same finite table must also establish the required blank startup.

## Provenance

The upstream BusyBeaver files are preserved with their license. The
source-language resolver carries its upstream attribution in its header.
The new Python/C++ scripts, negative receipts, and local context datasets
were produced during this investigation. All assertions about search scope
are intentionally narrower than the user's requested existence theorem.
