BOUNDED SYNTHESIS OF A SHORTER RETURN SCANNER

No shorter scanner was found. This is a fresh, restricted synthesis experiment,
not a lower bound for all 195-state machines.

The PA196 return scanner has seven counter controls, with native names
2,3,5,9,15,23,34. It additionally uses the unchanged native 1 left scan and
native 75 right scan. A successful six-counter replacement would save one
working state without changing the arithmetic source or its decoder.

CONTRACT
The initial control is abstract 0, with head coordinate 0 and a known 1 at
coordinate 1. For each m=0,...,6, a prefix consists of m zeros immediately
leftward from the head, followed by a 1 at coordinate -m. The desired output
has control 0 and head -m-1, with every tape cell restored. For a seven-zero
prefix, the desired output is the right-scan helper at coordinate -7, again
with unchanged tape. The candidate may move in both directions and may write,
but it must not read beyond the supplied prefix before its endpoint.
These eight cases give exact compositional contracts; they are not sampled
values of unbounded registers. Reads outside the supplied region are rejected,
so every uninspected tape suffix is arbitrary.

The two helper controls retain their complete rows. The reported principal
searches also fix row 0/1 to write 1/moveL/control 0 and fix the first fresh
target of row 0/0 to 1. A separate recorded query relaxes row 0/1. Every run
has an explicit step bound. These are real restrictions on the template.

RESULTS
A seven-counter-state positive control was rediscovered by the solver and
then independently replayed by check_positive.py. Its longest contract is
8 steps. The six-counter read-only model with bound 18 is UNSAT; the writable
model with bound 12 is UNSAT. A pure-bitvector multiplexor encoding additionally
establishes UNSAT for the writable model with bound 14. Longer writable
queries at bounds 16 and 24, and the relaxed-on1 query at bound 18, returned
UNKNOWN at their stated timeouts. UNKNOWN is not an infeasibility result.
Detailed model restrictions, solver version, commands, and statuses are
recorded in search_receipt.json and the source files.

REPLAY
    python3 check_positive.py
    python3 synthesize.py --states 7 --steps 10 --seconds 30 --readonly --symmetry
    python3 synthesize.py --states 6 --steps 12 --seconds 60 --symmetry
    python3 synthesize_mux.py --states 6 --steps 14 --seconds 90 --symmetry

Synthesis requires the z3 Python package; this run used z3 5.4.1 and Python
3.12.14. Solver times and returned models may vary. The positive replay needs
only Python's standard library. No solver UNSAT proof was exported, and no
new Lean kernel theorem or PA-internal consistency equivalence is claimed.
