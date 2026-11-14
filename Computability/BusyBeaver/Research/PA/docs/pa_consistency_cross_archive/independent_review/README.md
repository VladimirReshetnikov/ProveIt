# Independent review of four new 196-state cross-grafts

All supplied checkers pass. The four tables are new rooted transition
graphs relative to every supplied literal 196-state table and relative to
one another. Each has 196 graph-reachable working controls and 196 ordinary
action-bisimulation classes. These are same-size results, not a sub-196
construction.

## Run

Use Python 3.10 or later; only the standard library is required.

    python3 verify_grafts.py
    python3 check_command_words.py
    python3 verify_zerojump_grafts.py

The first checker imports neither the root builder nor an inherited symbolic
runtime. It independently parses the literal Lean macro definitions, expands
the candidate grammars, resolves source control flow using leaf intervals,
and checks all component bindings. It also checks the complete free-algebra
AX output, native/dense conjugacy, whole-tape startup, and graph novelty.
The zerojump checker uses the first checker's input/CFG/graph functions and
independently recomputes both original and modified abstract closures.

The recorded outputs are `graft_review.json`, `command_review.json`, and
`zerojump_review.json`. `input_manifest.json` binds all copied inputs to exact
SHA-256 hashes and their original working locations. No checker modifies the
root construction or source archives.

The broader novelty check, which requires the original checkout, is:

    python3 check_all_prior_graphs.py /path/to/ProveIt/docs/incoming /path/to/current_inventory.json

Its `all_prior_graph_review.json` receipt covers all 268 literal 196-state
table occurrences, deduplicated to 127 parsed transition tables. It first
uses each state's pair of write/move actions as a necessary isomorphism
invariant, then tries every possible initial working label of each remaining
table. All 23,324 resulting rooted canonicalizations differ from the four
new graphs. Thus novelty does not depend on guessing a native table's
initial label or excluding previous experimental tables.

## What was checked

| Candidate | Source sites | AX sites | Exterior sites | Startup |
|---|---:|---:|---:|---:|
| Diagonal + Combined | 3,676 | 3,531 | 145 | 57,922 |
| Separate + Combined | 3,649 | 3,504 | 145 | 57,922 |
| Diagonal + Combined + zerojump | 3,676 | 3,531 | 145 | 58,168 |
| Separate + Combined + zerojump | 3,649 | 3,504 | 145 | 58,168 |

Every pre/post-AX exterior opcode and resolved edge agrees with Combined196
under the exact source-address map. Every AX primitive instruction and edge
agrees with the diagonal/separate source after changing its surrounding
prefix and binding its single command-return exit. The Combined return at
ordinal 3776 is correctly mapped to 3664 or 3637, respectively. The only
changed fixed-control row in each primary native table is the required AX
entry redirect at 101/read1; the other 267 fixed-control rows are identical
to Combined196.

The AX word contains 191 or 190 macro items. The independent free-algebra
check confirms the six old heads, restricted propositional head, generated
universal formula, saved top, and final diagonal/separate gate. In the
separate case the extra unconditional Gamma head is at the top of the
stack. The final numerical guard and cleanup macros are unchanged.

The zerojump variants have exactly one additional native row change:
27/read1 changes from `(0,L,40)` to `(1,R,21)`. Their only source change is
site 26 from `jump34` to `dec6(34,27)`. The parent and modified abstract
closures are identical, not merely equal in size: 265,964 pairs for the
diagonal source and 263,244 for the separate source. Every admitted pattern
at source26 has register6 zero. The common invariant therefore makes the
source replacement a value-preserving step on every reachable source run.

## Command compiler

`command_compiler_note.tex` gives a proof for a general AX with `m` generated
formulas, where `m=8` for the diagonal source and `m=9` for the separate
source. The saved top is an additional stack entry, so the total pushed
counts are nine and ten. The note adjusts all pop, push, selector and
generalization words and proves the MP proof compiler by induction.

| Word component | Diagonal m=8 | Separate m=9 |
|---|---:|---:|
| Shifts after AX in Push | 8 | 9 |
| Shifts after AX in Pop | 10 | 11 |
| Shifts after final AX in generalization | 9 | 10 |
| Pops selecting the final gate | 9 | 10 |

Pop halts when the saved top is one. The proof explicitly permits this
early halt instead of assuming Pop is total. The MP suffix keeps its dummy
zero so that it preserves the opaque underlying stack. The separate head
has residue zero and is safe even when the final gate guard fails.

The symbolic command checker validates 64 and 67 identities, respectively.
Its head and gate values are abstract residue-zero values, so it does not
assume that a guarded gate is nonzero. It covers the numerical truth alias
`I(0,0)=0` and never inspects the arbitrary opaque stack tail.

## Limits

The source/graph checkers do not independently reimplement the inherited
unbounded tape-engine proofs. The parent construction has separate complete
symbolic physical instruction certificates. This review proves the missing
finite composition bindings and supplies the changed command compiler.
The ordinary calculus-to-PA calibration is inherited from the diagonal and
separate-head manuscripts. No new closed Lean PA biconditional is claimed,
and no finite startup trace is used to infer nonhalting.

James Chang's original macro/table sources and the ProveIt contributions
retain their supplied licenses, copied alongside this review.
