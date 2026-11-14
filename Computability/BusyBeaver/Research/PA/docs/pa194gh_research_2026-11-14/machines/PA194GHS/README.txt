PA194GHS — symmetric physical realization of the PA194GH commands
===============================================================

Binary, two-way, single-tape, all-zero blank start; 194 working states.
Start 0, halt 194, initial head coordinate 0; 388 transition rows.
SHA-256: 68442e304616894c14f0e256624208c89fc9e84897d678b1c809f0c27a4ca471

This table implements exactly the new command interface proved in
../PA194GH/proof.tex. Its saved generalization is U(c,h), MP pushes no
extra zero, and Shift tests only the cached head. It additionally uses
PA194HS's symmetric destructive comparison, which removes three source
sites. This is a second physical implementation, not a second logical
calculus. The inherited absolute iPRA calibration remains incomplete.

Reproduce from this directory (Python 3.10+, assertions enabled):

    python3 -B build.py
    python3 -B check_commands.py
    python3 -B ../PA194GH/independent/check.py . --output ../PA194GH/independent/results

The sibling PA194GH directory must be retained. It holds the shared
compiler/runtime, frozen ancestry inputs, proof, licenses and independent
checker. build.py reconstructs this companion from the exact GH raw table,
rechecks its additional source changes and eighth contextual fold, verifies
all 4,750 source outcomes, and compares the whole blank startup tape at
step 57,768. The raw count is 135 fixed + 67 readers; eight folds give 194.

Full source sites, instructions, grammar, nodes, native/dense tables,
numbering map, fold cases and receipts are included here. The independent
checker rederives the register-list lemmas from this table. These are
executable symbolic certificates, not a proof-assistant kernel.
