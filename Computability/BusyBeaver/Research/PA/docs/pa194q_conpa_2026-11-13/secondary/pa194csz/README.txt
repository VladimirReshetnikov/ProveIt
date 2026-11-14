PA194CSZ: symmetric Shift plus a zero-register jump
=================================================

This optional construction has 194 working states and 388 transitions. It
combines the supplied symmetric Shift with a supplied guarded zero-register
jump and freshly proves their compatibility. It is not a reduction below
194, and neither ingredient is claimed as a new idea.

Authoritative dense table: machine_csz/pa194CSZ.tm
SHA-256: 62e93098caf7c09ff2938d07064f0dbbb47c71ec369892968258fff708592269

Working labels are 0 through 193, start is 0, and the separate halt label is
194. The head begins at cell 0 on a two-way infinite all-zero binary tape.
Each row is: current_state read_bit write_bit L_or_R next_state.
Every move is L or R. The native table uses start 74 and halt 254; its checked
dense/native bijection is included.

Reproduce
---------
Python 3.10 or later and only its standard library are required:

    python3 -B verify.py

Run with assertions enabled, without -O or PYTHONOPTIMIZE. No network,
external checkout, solver, compiler or proof assistant is needed. The
independent physical replay can take several minutes. Receipts are
regenerated, including observed timings.

Components may also be run separately:

    python3 -B build_csz.py
    python3 -B check_invariant.py
    python3 -B verification/check_csz.py

Completed verification
----------------------
- 3,646 source sites and 4,746 universal primitive outcomes.
- Fully unfolded table: 202 controls, consisting of 135 fixed controls and
  67 readers. Eight simultaneous folds yield 194. All 32 local two-cell
  cases pass, with maximum duration 5.
- Common invariant: 263,180 (site, positivity-mask) pairs. At site 26, all
  32 admitted masks have r6=0. Both sources agree at every concrete step
  from the clean seed.
- Original symbolic runtime: 1,513,882 transitions, at most 508 per outcome.
- Independent literal runtime: 1,100,566 transitions, at most 403 per
  outcome; four generic list lemmas rederived from literal rows; no
  arithmetic-block oracle; minimum positive-duration constant 3. Two CFG
  resolvers agree, and the finite invariant is independently checked.
- Exact whole-tape blank seed after 58,014 transitions: native state 84,
  head -2, source site 25, registers (2,0,0,0,0,0,0,0,0), and 26 spare
  blocks of value one. The independent bytearray check finds no earlier halt.
- The action graph differs from all eight previous 194-state classes and
  all 620 recognized literal forms at repository commit
  17f92105e2bc4317feae6c219cb2143437b482ff, allowing control renaming,
  start choice, reflection and symbol complementation. The finite graph
  receipt is machine_csz/novelty.json.

Only source site 26 changes: jump34 becomes dec r6[zero34,positive27].
Only native row (27,1) changes: 0L40 becomes 1R21. The invariant excludes
that decrement's positive branch from the blank-start source execution;
physical verification nevertheless checks both branches universally.

Proof scope
-----------
proof_csz.tex gives the complete new invariant and simulation argument as a
report fragment. The new transfer is PA-provable halting equivalence with
supplied PA194CS. Its ordinary mathematical calibration to Con(PA) is an
inherited dependency, not a conclusion of the Python certificate alone.
No newly compiled end-to-end Lean/Rocq theorem or completed iPRA endpoint
is claimed.

The contracts cover nine arbitrary natural registers, address-plus-gap
length 48+n for any n>=0, and an arbitrary nonempty finite spare list. The mask invariant
represents unbounded registers, rather than bounded numerical samples.
Initialization is an exact finite check, not long-run nonhalting evidence.
This composition does not improve PA194CS's startup runtime.

Files
-----
build_csz.py                  Complete deterministic builder
check_invariant.py            Small independent finite invariant checker
compiler.py, symbolic_runtime.py, baseline_tools.py
                              Attributed construction support
inputs/, reference/, referenceCS/
                              Frozen source and pinned parent data
machine_csz/                  Literal tables, source, folds and invariant
verification/check_csz.py     Independent literal execution checker
verification/reference/       Its attributed support modules and licenses
verification/results_csz/     Contracts, list lemmas, seed and receipt
proof_csz.tex                 Mathematical proof fragment
PROVENANCE.json, NOTICE_CSZ.txt
                              Exact source identities and credit
LICENSE.*                    Preserved supplied licenses

Preserve all notices and licenses. Check SHA256SUMS before regenerating
outputs; reproduction intentionally rewrites receipts and timings.
