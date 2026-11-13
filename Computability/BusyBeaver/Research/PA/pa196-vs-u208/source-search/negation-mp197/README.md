# Combining the negation and MP-success source rewrites

This experiment combines two separately proposed source changes. It produces
an **experimental 197-state machine**, not a machine below 196 states and not
an established PA consistency equivalence. The source has 3,573 primitive
sites, compared with 3,596 in the negation candidate and 3,812 in the
published PA196 program. The shorter program still has 159 distinct internal
source nodes, and all 197 of its working states are graph reachable.

The first input is `experiments/negation197` in the incoming
`pa_consistency_research_2026-11-13.zip`. Its source replaces a repeated
negation macro by a shorter arithmetic sequence; the incoming report gives
the intended source-level identity. The second input is
`mp_move_h_candidate.json` from `conpa_tm_comparison_and_reduction_search.zip`.
It changes the successful MP branch so that the consequent is put in `H`,
with `T` and `D` cleared and the stack unchanged. This is a deliberate change
to the command interpreter, not a claim that every old command has identical
state effects. The incoming `command_reduction.tex` gives an adapted
proof-word compiler and proof-carrying soundness argument as mathematical
research; neither is an implemented PA proof for this combined table.

**Scratch-register condition:** the negation rewrite is not equivalent for
arbitrary scratch registers. An independent check found that, at the first changed
region, input `r1=r2=r6=0, r7=1` produces `r1=16` in the old block and
`r1=12` in the new block. The replay computes a closed joint zero/positive
invariant from the clean seed for both the MP-only and combined source programs; it forces `r7=0` at
all eight identified rewrite entries. This establishes the scratch-zero
entry condition at the abstract source level. The separate [local audit](local-audit/README.md) proves the
individual block identity under that condition and checks the eight source
control-flow replacements. The full PA-internal transport remains open.
Passing primitive contracts alone would not establish the entry invariant.

The negation source retains exactly one occurrence of original source
`node163`, at path `10101011`. Replace it by `(node6,node147)`, exactly the
MP rewrite in the second archive. On the native table the matching one-row
change is `(164,1): 1 R 98 -> 1 R 130`; start is 74, frame-root state is 84,
and halt is 254. The incoming archive checker verifies all 3,573 source
sites, including both branches of every decrement, for 4,641 symbolic cases,
and checks that the blank tape reaches the original clean frame in exactly
58,154 steps. It checks agreement with its inherited engine at 42 protected
rows. The source graph is separately resolved using two independent path and
ancestor-interval algorithms. The exact inputs, outputs, and results are
pinned in [receipt.json](receipt.json).

The symbolic checks are executable evidence for local primitive contracts;
they are not a kernel-checked proof or, by themselves, an internal PA theorem.
In particular, the proposed MP compiler and the negation source transformation
must be connected to this exact table, the arbitrary-internal-time halting
trace must be bound to the source, and both directions of the desired PA
consistency equivalence require the appropriate arithmetized proofs. No claim
is made that 197 states is a lower bound, or that source-site count equals
physical state count.

## Reproduction

From the repository root, Python 3.10 or later:

```sh
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/source-search/negation-mp197/replay.py --output /tmp/negation-mp197-receipt.json --out-dir /tmp/negation-mp197
```

Do not use Python `-O`: the imported archive's symbolic and startup checker
uses assertions. The replay pins both archive SHA-256 hashes, reads the source
and native table directly from them, and extracts only the temporary checker
files needed for the run. It also checks that applying the MP rewrite to the
original PA196 tree produces the exact tree shipped in the second archive.
The retained [native table](machine.native.tm) and [source tree](source.tree.json)
are checked byte-for-byte against the reconstruction. The optional output
directory also contains a flat site list and a table with an explicit start
directive.

The upstream negation checker and source snapshots retain their archive
licenses and attribution; their author did not review this combination.

A separate run of the existing U208-derived symbolic runtime engine rederived
all 4,641 contracts over arbitrary nine-register values and nonempty finite
spare lists, at the actual startup header gap 48, covering all 394 table
rows. Its deterministic summary is [runtime48-receipt.json](runtime48-receipt.json).
This engine also provides executable induction, not a PA or kernel proof. It
has different code and provenance from the incoming archive checker. Reproduce
after creating the output files above:

```sh
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/source-search/startup-preserving/check_runtime48.py --machine /tmp/negation-mp197/machine-with-start.native.tm --sites /tmp/negation-mp197/sites.json --mapping Computability/BusyBeaver/Research/PA/pa196-vs-u208/source-search/allocator-screen/legacy_mapping.json --output /tmp/negation-mp197-runtime48 --expected-states 197
```

The recorded run took about two minutes. The generated runtime report contains
non-deterministic elapsed time and additional details; the committed summary
omits that time and the longer block and label maps.
