# Exact 222-state runtime and source certificates

Run from any directory with standard-library Python 3 (assertions enabled for
`verify222.py`, whose retained symbolic proof engine uses assertions):

    python -B verify222.py
    python -B audit222.py
    python -B generate_invariants222.py
    python -B -O check_invariants222.py

Default input is `inputs/`, default output is `results/`, both relative to this
script directory. The full verifier also accepts positional `INPUTDIR OUTPUTDIR`;
the other three scripts accept positional `OUTPUTDIR`. INPUTDIR must contain
`candidate.tm` (the native, noncontiguous labels, initial 0 and halt 254) and
`sites.json`. The exact supplied table/source hashes and 222-state census are
checked before any theorem replay. Canonical labels are related separately by
an explicit bijection.

The full verifier proves all 6,167 guarded source-instruction cases with nine
independent arbitrary natural register values, arbitrary extra gap and an
arbitrary nonempty finite list of spare words. It also executes blank startup
with two independent tape representations and compares the entire resulting
tape support. The initial seed is [3,0,0,0,3,0,0,0,0].

`audit222.py` independently checks stored receipt integrity, complete case
coverage, source CFG, positive duration forms, literal relabeling and full blank
startup. It does not replace the fresh induction replay. The source fixed point
is regenerated from the exact source, and checked independently using a
trie-interval/ancestor CFG implementation. Both auditing programs retain their
checks under Python optimization.

`reference_results/` retains the separately run discovery-time proof output.
The portable replay's own output is in `results/`; these are independently
executed instances, not copied success flags. The mathematical calibration of
the proof calculus and emitted formula grammar is a separate obligation.
No newly compiled Rocq or Lean endpoint is asserted here.
