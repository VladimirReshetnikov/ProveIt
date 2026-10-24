# Architecture proofs and comparison artifacts

Main results: replace the duplicated upper row circuit by 23 fixed squarings, and orient all four Pell congruences using canonical simultaneous witnesses. The main direct packet integrates these results and supersedes this folder's earlier numerical comparisons.

Read PROOF.md for full arguments and section.tex for a report-ready section. The exact Mathlib source is inert, never executed, and pinned in PELL_SOURCE_PIN.json with its Apache license. HEIGHT_CERTIFICATE.json records both arithmetic-DAG exponent certificates.

Run `python check_architecture.py` from this folder (or invoke it by full path). It performs arithmetic fixtures, independent sparse sum-of-squares expansion, and clean byte-for-byte replay of the three selected final variants. Python standard library only. The `--no-rebuild` option skips clean regeneration. CHECKS.json records the results.

The standalone builders are self-authored round 13 code. The delivered build_architecture_final.py rounds the fixed exponent upward to a power of two and adds the optional factorial carrier. No upstream program is imported or executed. The initial coarse/exact comparison outputs and earlier reference files are omitted. The release checker is a narrowed copy selecting only rounded positive, rounded negative, and factorial-carrier outputs; the mathematical proofs and final builder are unchanged.

BENCHMARKS.json contains exact comparison counts. Rounded positive CRT uses2672 natural variables; rounded negative CRT uses2678; factorial carrier uses2872. These are matched architecture comparisons, not the final round13 minimum. The recommended main polynomial is elsewhere in the direct packet.

No new kernel-checked end-to-end formalization or proof of Con(ZFC) is claimed. Existing numerical-calculus calibration and exact Pell graphs remain explicit dependencies.
