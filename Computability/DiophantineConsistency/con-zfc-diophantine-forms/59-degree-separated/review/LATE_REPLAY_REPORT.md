# Late original-root replay and short-frontier comparison

Both late archives were replayed from fresh copies. Original extracted trees and frozen wave8 families were unchanged. The root drivers were read before execution; all 29 Python files were parsed and inspected for imports, process calls, filesystem writes and dynamic execution. The only process calls were the local listed verifier/build steps; all generated writes occurred in disposable copies. These are finite reproduction checks, not new proof-assistant kernel claims.

## Exact root outcomes

- Separated Degrees: `python reproduce.py` passed all 13 listed steps, exit 0, in 14.496 seconds. Every pre-existing copied file remained byte-identical. `python -O reproduce.py` exited1 with the documented message `Run without -O/-OO: some independent checks use assertions.` This is classified as EXPECTED_REJECTION, not a passed optimized audit.
- Free Coordinate: `python verify_all.py` and `python -O verify_all.py` both passed, exit 0, in 2.890 and 2.947 seconds. Every pre-existing copied file remained byte-identical. Their JSON output differs only in the explicit `outer_python_optimized` flag; the substantive component receipts match.

The complete receipts, stdout/stderr, copied reproduction certificate and every initial input SHA256 are in the neighboring LATE_REPLAY files. The observed Python is 3.12.14. No original research archive was edited.

## Comparison affecting the frozen short frontier

For fifteen strictly positive unknowns, the late archive supplies:

- Q54: 73 operations, exact degree 54, dominating frozen 73/60.
- Q46: 74 operations, exact degree 46, dominating frozen 74/50 and 75/46.
- Inherited gap_minima75: 75 operations, exact degree 44, dominating frozen 76/44 and 75/46. Its degree certificate is explicitly displayed in the preserved GAP_MINIMA.tex: the diagonal leading coefficient is 16 beta^28 + 256 beta^24 + 16 beta^22 > 0.

The resulting inspected fifteen-variable frontier, as operations/degree, is:
66/157,67/125,68/101,69/91,70/84,71/80,72/74,73/54,74/46,75/44.
The frozen fourteen-variable 79/52 point remains incomparable. This changes comparative claims, not the correctness of the frozen dominated polynomials. Frozen family artifacts were deliberately not rewritten.

An independent read-only comparison checked the literal gate totals, topology, complete liveness and four byte-identical coefficient payloads. Q54 has 39 multiplications, 19 additions and 15 subtractions; Q46 has 39, 20, 15. The supplied proof's minimum-norm argument is sound on the positive domain. Q54's top contribution has degree 54 and nonzero coefficient 64 beta^32; Q46's top contribution has degree 46 and coefficient 4 beta^22. Squared-modulus completeness reconstructs canonical normalized witnesses rather than incorrectly assuming f^2=1 modulo c for arbitrary ordinary-strong witnesses.

These statements retain the named inherited native-compiler and K215 calibration dependencies. They establish no global minimality, no consistency result, and no new kernel-checked derivation.
