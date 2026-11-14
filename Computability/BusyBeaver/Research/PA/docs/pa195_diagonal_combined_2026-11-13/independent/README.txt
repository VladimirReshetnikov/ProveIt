Independent symbolic verification of PA195DC
===========================================

Run from the package root, with Python 3.10+ and assertions enabled:

  python3 independent/verify_physical.py
  python3 independent/check_commands.py

Alternatively, invoke either script by its full path from any working directory.
Both scripts locate and read the actual sibling machine/ files.
They write detailed fresh certificates into independent/results/. No optional
Python packages are required. Python -O and PYTHONOPTIMIZE are rejected.

The physical route parses the new native and dense tables directly and checks
the exact dense relabeling, graph reachability of all 195 working states, and
the native table SHA-256. It reads machine/source.json, reconstructs its source
control-flow graph with two independent algorithms, and compares every source
instruction. It does not import machine/build_verify.py or its compiler.

The symbolic engine represents the complete tape using affine unary runs,
infinite blank exteriors, nine arbitrary natural register values, an arbitrary
nonnegative extra header gap, and a nonempty finite spare-register list with
arbitrary natural entries. Four traversal lemmas are rederived from the actual
literal rows and lifted to arbitrary spare lists. Every primitive source site
is checked, including both branches of each decrement. No arithmetic register
box is assumed as an oracle. Unbounded homogeneous scans and spare-list walks
are justified by the explicit symbolic induction rules in the imported engine.

The exact 57,922-step blank startup is then replayed literally. Its state,
head position, and entire finite support must equal the clean source-25 frame,
with candidate 2, all other logical registers zero, gap 48 and 26 spare blocks
of value one. A finite simulation alone is not a nonhalting proof.

The command supplement checks the nine-entry AX interface and the changed
Shift/MP compiler algebra in 164 symbolic cases. It includes arbitrary opaque
stack tails, the all-zero Cantor alias, early halts at saved top one, all
selectors, generalization, and the dummy-zero MP suffix. Unknown symbolic
equalities are rejected rather than guessed. Formula gates are treated by
their already proved macro interface and residue; the free-algebra emitter
binding and the gate's logical calibration are separate package obligations.

The driver programs were adapted for this exact table. The five checker and
mapping files in reference/ were imported without alteration from the supplied
research archive. PROVENANCE.json records their origin and exact hashes;
LICENSE.JamesChang and LICENSE.ProveIt preserve the accompanying notices.

These are executable mathematical certificates. They are not Lean or Rocq
kernel proofs and do not by themselves establish the PA consistency
biconditional. The report supplies the logical and arithmetic composition.

Once the recorded/ directory and MANIFEST.json are present, replay.py first
checks their identities, reruns both routes, and compares the five generated
certificate files byte for byte against the recorded results.
