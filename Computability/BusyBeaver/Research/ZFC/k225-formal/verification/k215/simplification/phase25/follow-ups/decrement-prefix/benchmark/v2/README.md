# Paired decrement benchmark v2 — source-only successor

This unexecuted successor uses the exact v1 benchmark driver with only its fixed plan hash changed. The plan updates owned snapshot paths and the two-line repaired prefix candidate, and adds immutable v1 failure/repair/provenance file pins. All policy fields and the three literal block statements/proofs remain exact. The original draft, failed run and raw records are unchanged.

V1 stopped at prefix KSim elaboration: its soundness applications retained closed `if true = true` / `if false = true` around the target, blocking two original `conc_target` rewrites. V2 adds only explicit conditional rewrites before those original steps. The paired checker, neutral/specialized execution logic, targets and every other proof line remain unchanged. New source growth is 36 lines/1,580 bytes against P24, including the two-line/87-byte repair. No new candidate elaboration or profile result is claimed.

Both arms retain separate new workspaces/objects, 17 exact unaffected accepted P24 dependencies and fresh KSim+KFastSites215 before either identical blocks0/5/10 probe. Failed-run objects are not imported or reused. The one inherited FramedWindow raw-record absence remains explicit, with its accepted aggregate/source/object/log bindings; no fresh record exemption or reconstructed record is introduced.

Pinned existing supervisor/compiler, global lock, SIGTERM→KeyboardInterrupt process-group cleanup, -j1/-M12288, one thread, 120-second ordinary /900-second probe compiler budgets, zero-warning/standard-axiom rules, exact ordered report-name/profile equality and full source/object/log/dependency/input pre/postchecks are unchanged. Compiler seconds exclude global lock wait. All attempts preserve source/log/raw records; failures preserve FAIL diagnostics. Outputs must be new and cannot resume old objects.

Root and inline must independently review the repair and new frozen controls before root-only launch: `python3 -B /tmp/k215-phase25-decrement-benchmark-draft-v2/benchmark.py --out NEW_ABSOLUTE_DIRECTORY`. No command was executed here. A third control reviewer was waived by root; this does not waive either required review.

This is still one ordered sample per arm for three existing blocks (9/52/67 literal leaves), not full coverage, general speed, Boolean acceptance equivalence, adoption, machine count or PA endpoint evidence. Separate phase25 proof cuts remain excluded.
