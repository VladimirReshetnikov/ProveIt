Shared macro words and the exact Perm/Dom AX effect equality
========================================================

Base: VladimirReshetnikov/ProveIt commit
6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95.

These three proposed modules were checked using Lean 4.32.0 against the
actual repository definitions. Thirty repository dependency modules and
three new modules compiled successfully in an isolated directory. No
K215 or K217 endpoint was rebuilt and no production file was modified.

Files:
* GenericMacroWord.lean: checked word soundness, invariant preservation,
  label erasure, and adjacent commuting effects under any prefix/suffix.
* AXReadCons.lean: actual L2Perm.AXAtom readp1/cons effects commute.
* AXWordsEqual.lean: L2Perm.f236 st = L2Dom.f236 st for every L2K.AS;
  the Dom closed-form AX effect theorem follows from the Perm theorem.

The first concrete-word comparison needed maxRecDepth 4096, matching the
production AX modules. The accepted final result is in receipt.json;
there are no sorry/admit declarations in these new sources.

Reproduce in a fresh output directory:

python3 build_prototype.py --repo /path/to/ProveIt \
  --lean /path/to/lean-4.32.0/bin/lean --out /path/to/new-build

The script checks the repository commit, resolves the 30 dependency
sources from the checkout, copies them into the new build directory,
and compiles serially. Source and log hashes are written to receipt.json.

This is an additive proof prototype. It establishes a precise route to
one shared AX proof, but it does not claim a production source reduction.
Keep the two concrete word-to-DAG checks separate. Equality of AX effects
is not equality of the complete programs or their command decoders.

Attribution: the checked-word soundness induction generalizes the existing
L2AxiomsPerm/L2AxiomsDom development in the pinned ProveIt repository.
RMDag semantics and the macro contracts are imported from that repository,
whose headers preserve their TMBuilder/K230/m254 provenance. The local
readp1/cons commutation, whole-word effect comparison and generic label/swap
lemmas are the additional work in this packet. Retain upstream terms when
integrating the proposed abstraction into the existing development.
