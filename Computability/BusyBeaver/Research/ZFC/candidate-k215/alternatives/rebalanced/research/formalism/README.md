# Late matrix inflation: a source experiment

**The native-calculus-to-ZFC lower consistency reduction remains open.** This
is not an accepted 214-state or 215-state machine. It has no allocated binary
table and no certified blank-tape execution.

The source edit inserts `C := C+A+B+1` just before the existing final bundle
emitter, removes its two now-unnecessary equality comparisons, and preserves
all earlier logical rows. The source in `large-matrix/` has 206 distinct
subtrees, 4,738 primitive occurrences, 6,155 guarded cases, depth 46 and
zero-run 6. That saves 13 primitive occurrences but adds four distinct
subtrees relative to the accepted K215 source. No binary-state count follows.

`formalism_supplement.tex` gives a first-order matrix-padding lemma, a new
universal RESET block and the precise restricted numerical calculus searched
by this source. The unresolved point is atomic quantifier vacuity: the same
bundle now emits it only for binder indices `C>A+B`. Matrix padding in
ordinary first-order logic does not recover this missing native interface.

## Reproduce

From the packet root, with Python 3 and its standard library:

```sh
python3 research/formalism/large_matrix_splice.py \
  --output /tmp/large-matrix-reproduction
```

The script locates `baseline/sites215.json` relative to itself. It pins that
file and its unchanged vendored source utility by SHA-256. No external
checkout, network access or current working directory convention is needed
when the script is invoked by an absolute path. A `--baseline` override is
available, but its content must match the pinned source.

The source SHA-256 is
`aa20e3cdeb5bc7c4814f079843b4f45caab6a37e72fc333cb047e8fa41c172e3`.
`large-matrix/large_matrix_audit.json` records two complete control-flow
resolvers, preservation of every unchanged exterior instruction and edge,
literal retention of the first bundle factor, and 1,728 finite macro tests.
The all-natural macro and compiler claims in the supplement are ordinary
mathematical proofs, not newly compiled Lean/Rocq theorems.

## Provenance

`vendor/source_splice.py` is copied byte for byte from the pinned ProveIt
checkout, `candidate-k215/research/composition-allocation/source_splice.py`.
The calculus, source macros and compiler conventions retain the upstream
attribution and licenses included in the packet's `licenses/` directory.
The late-inflation edit, padding lemma, reset proof and finite audit were
produced in this session. The supplement is separate from the accepted
215-state physical rebalancing and is not used in its correctness proof.
