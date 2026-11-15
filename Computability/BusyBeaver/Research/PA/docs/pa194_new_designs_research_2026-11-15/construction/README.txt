PA194-LCSF3 / PA194LCAX11HSF3
===========================

This is a new 194-working-state, binary single-tape blank-input construction.
Its parent is the exact PA194LC_AX11H_SF table in the four incoming archives
at ProveIt revision 793c68737d94bffa4e32a75bce6cc8058d6d22f0.

The only native edit is 190/1: 1 L 73 -> 0 L 42. Native start=74, halt=254.
The dense table preserves the parent's numbering: start=0, halt=194.
Native state 194 remains a working state; the halt is not part of the 194.

candidate/machine.tm          Complete dense table, 388 numeric rows.
candidate/machine.native.tm   Complete native table.
candidate/labels.json         Dense-to-native map, including halt.
candidate/construction.json   Identities, edit and machine convention.
candidate/verification.json   Fresh independent verification receipt.
build.py                     Reconstructs the exact new table.
verify.py                    Checks the written proof's finite premises.
reproduce.py                 Runs builder plus independent checker.
proof.tex                    Standalone relative proof and dependencies.

Reproduce with Python 3, standard library only, assertions enabled:

  python3 -B construction/reproduce.py --output lcsf3_replay

The independent checker establishes the unique predecessor's forced bit,
eight exhaustive local contexts, full dense/native conjugacy, exact 57918-
step startup and complete seed tape, 61 fixed-address decoder-use proofs,
the first affected source event at step 32686, and the exact 66-to-64-step
canonical instruction endpoint. The decoder certificates use only literal
address cells, so they apply to arbitrary admissible registers, header gap,
and spare list. The transfer of source reachability to the enormous physical
blank prefix uses the inherited source-frame theorem, not a scalar replay.

Quantifier-free induction proves the unbounded relative theorem in iPRA.
The parent-to-child halting witness bound is t; child-to-parent is 3*t.
These positive maps give both halting and nonhalting equivalence without
assuming Con(PA), classical reasoning, or unbounded minimization.

The absolute Con(PA) theorem imports the exact written revised AX11H
calibration, then the LC_AX11H and SF transfers. Their source/proof files
are in reference/, including the exact nested calibration ZIP:

  reference/references/ax11h_calibration.zip

Its SHA-256 is
93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075.
The source and prior physical transformations remain attributed prior work.
No end-to-end Lean kernel theorem is claimed by this packet.

The third return shortcut was already used on GH/GHS parents. The new
contribution is its compatible composition with the LC_AX11H history
selector, with exact all-time simulation and structural novelty checked.

Existing inherited SF finite premises can be replayed in a disposable copy:

  python3 -B reference/composites/verify_composites.py

That upstream script writes its verification receipts. The supplied original
proofs and provenance are preserved; the top-level package also records a
fresh isolated replay of these inherited finite premises.
