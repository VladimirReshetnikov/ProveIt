FM215: exact-table, all-tape Lean proof
====================================

The three formal sources were kernel-checked successfully with official
Lean 4.32.0. See fm215-kernel-receipt.json and the three .compile.log files.
PositiveSimulation.halts_iff, FM215.all_tapes_halts_iff, and its blank
instance depend on exactly propext and Quot.sound.

Reproduce from this directory with a complete Lean 4.32.0 installation:

  python3 check_fm215.py --lean /absolute/path/to/lean

The script compiles PositiveSimulation.lean, FM215Data.lean, and FM215.lean
sequentially, prints the endpoint dependencies, and binds both complete
literal tables to k215.native.tm and fm215.native.tm. It records source,
object, and compiler-output hashes. No ProveIt build is required.
The independent data audit can also be run alone:

  python3 check_lean_bindings.py --output lean-bindings.json

Scope
-----
The main theorem covers all binary tapes (Int -> Bool), every initial
head position, and designated initial control 0. It is a genuine whole-
tape halting equivalence, not a conclusion drawn from a finite run.
The machine has 215 working controls, two symbols, and terminal label 254.
Fin 512 is only the ambient type for the nonconsecutive native labels.

The new native table changes exactly four primary K215 rows. State 127's
old role is merged into 124; label 127 is reused as a predecessor-marker
selector. Old transitions take one or three new transitions. An invariant
at the old machine's two exceptional states remembers only the symbol
immediately left of the head and holds after every old transition.

This standalone endpoint uses functional tapes and native state labels.
The repository's existing KEndpoint215 uses its own dense/zipper semantics.
The straightforward semantics-and-renaming bridge has not been compiled
as an imported end-to-end consistency endpoint in this packet. Ordinary
mathematical composition with the established primary calibration gives
FM215's nonhalting equivalence to Con(ZFC). No claim of a new 214-state
machine or a freshly rebuilt full ProveIt endpoint follows from this check.

Attribution
-----------
k215.native.tm and the old literal table are copied from ProveIt revision
b6c7087477e51c017003bd729e712c8969733223; see K215-NOTICE.txt and
ProveIt-LICENSE.txt. FM215 is the four-row construction developed for this
report. PositiveSimulation.lean extracts and generalizes the final
positive-step argument in ProveIt's KSim.halts_iff. The rest of the proof
and the independent binding checker were developed for this report.

Optional comparison artifacts
-----------------------------
check_cm215.py, cm215*.tm, cm215-canonicalization.json, and
cm215-certificate.json independently audit the previously existing
conditional-marker CM215 candidate. That checker certifies finite local
obligations used in an ordinary all-tape proof; it is not a second Lean
endpoint. CM215-NOTICE.txt identifies its repository provenance.
