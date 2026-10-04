# Exact-degree independent audit

Verdict: PASS on the mathematical claims, with one nonblocking scope clarification: the odd-K symmetry degree bound in candidate Section 2 should explicitly say K≥3. The separate K=1 result is correct.

Read `AUDIT.md` for the full proof audit and scope. `independent_check.py` is the standalone, fresh exact-integer checker; `independent_results.json` records its passing evidence. The checker uses no candidate or upstream code.

The evidence covers K=1…101 for coefficient and sign checks; full interpolation at K=1…10 (385 nodes); 565 SOS expansions at K=1…8, including every subset at K=1,2,3; and all fifteen literal POWER residual degrees.

`inventory.py`, `sources_before.json`, `sources_after.json` and `preservation_stdout.txt` establish preservation of both original source trees, including bytes, permission modes and nanosecond mtimes. `verify_sources.py` checks the candidate manifest and provenance hashes.

Run `python3 independent_check.py --output reproduced.json` and compare its output to `independent_results.json`. No external package or source packet is needed for this algebra run. Source-integrity reproduction needs the original paths identified in the audit.

The all-K result rests on the proof audit, not extrapolation from finite checks. No source script, Lean, counter-machine interpreter, or physical simulator was run.
