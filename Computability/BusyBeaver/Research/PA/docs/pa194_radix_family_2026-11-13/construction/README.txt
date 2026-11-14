PA194 radix-family reproducible construction
==========================================

Python 3.10+; standard library only; do not run with -O.

  python3 -B build.py --output generated

This regenerates the dense and native 194-state tables for:
  4R: new reassociation of the original radix-4 formula constructor;
  5: formula implication I(a,b)=5*Cantor(a,b);
  6: formula implication I(a,b)=6*Cantor(a,b).

To rebuild one family, add --family 4R, --family 5, or --family 6.
The three known dense-table SHA-256 values are hard-coded assertions.
The initial dense state is 0; working states are 0..193; halt is194.
Each table line is: state read write direction target.
The alphabet is binary, the tape is initially all zero, and direction
is always L or R. The count 194 excludes the halt target.

The builder verifies:
- the exact principal PA194 input table reconstructed from the pinned inputs;
- the 61 modified multiplier bodies and their exact complete Cons prefixes;
- all 3,429 outside source instructions and every relocated successor edge;
- the entire AX output in a free formula-constructor algebra;
- all 32 local contexts for the eight simultaneously applied reader folds;
- the unchanged arithmetic-box rows;
- every primitive source contract for arbitrary symbolic register values;
- the exact entire blank-start tape at step 58,320;
- the exact table count, reachability, totality, and expected hashes.

The separate independent literal checker should also be run: it imports
neither compiler.py nor support.py, recomputes the source graph by two
different methods, derives the four list-arithmetic block contracts from
the transition rows, and checks every arbitrary-register primitive case.

generic_cons_proof.tex gives the arithmetic macro theorem and its exact
concrete binding. Logical PA calibration is supplied by the main research
report. The executable certificates are not a new end-to-end Lean theorem.

Provenance
----------
Pinned ProveIt commit: 17f92105e2bc4317feae6c219cb2143437b482ff
Input Program.lean, Conjugacy.lean and pa196.tm are copied exactly from
Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/.
The primary PA194 grammar, folds, compiler, and symbolic runtime come from
Computability/BusyBeaver/Research/PA/docs/pa194_conpa_2026-11-13/.
support.py is adapted from the baseline finite helper functions carried
in docs/incoming/pa194_new_designs_2026-11-13.zip.
build.py, the source multiplier changes, extra reader fold, source-binding
audit, and free-algebra emitter audit are additions for this investigation.
Inherited licenses are included in LICENSE.JamesChang and LICENSE.ProveIt.

Files in reference/ are fixed inputs, not generated output.
The reconstruction has no network, repository checkout, or proof-assistant
dependency.
