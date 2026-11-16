# PA194 site-25 zero branch, expressed as the actual site-27 path

`PA194Path27Header.path27` kernel-checks that the repository's actual
`PA194SourceProgram.path 27` is `[true,false,false,false,true,false,false]`.
`modelWord` interprets any fixed standard list of path bits as a little-endian
model-valued tape prefix. `PA194Site27PathStep.zeroBranchPath27` composes this
path identity with the physical run: starting at the specified state-24
site-25 header, it reaches state 24 with left half 1 and exact right half
`modelWord (path 27) (zeros(k+1, 1+2·sourceFileCode(args)))`.

The only source-register hypothesis is `args 8 = 0`. All other logical
registers, the spare, and the complete suffix remain arbitrary model elements,
and the same complete source file is retained. The exact model-valued clock
is the named sum in the theorem. This is an all-model semantic physical run;
the theorem does not itself construct an object-theory iPRA proof of a
universally quantified source simulation.

The model-word identity uses the formal source-program path. A separate [standard-zipper frame correspondence](PATH27-FRAME-REPLAY.md)
has been checked. It applies to standard data with a blank suffix; this module
does not assert a nonstandard zipper correspondence or prove all source
instructions.

`check-site27-path.sh` recompiles this module, the path identity, and the
entire preceding incremental suffix. It expects the five checked overlays
documented in `TWO-HEADER-PASSES.md`, and `PA194_TWO_PASSES_SOURCE_DIR` can
specify external sources. It verifies the printed axioms and selected direct
object hashes. Input overlays still require an independently audited coherent
transitive import closure; direct hash checks do not establish that audit.
