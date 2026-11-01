# Explanatory gate aliases for the 29- and 30-variable displays

The corrected 29-variable presentation calls the printed square gate `m`, matching line 65, while `m` is a positive input and `f2` is the square gate in the 30-variable presentation. The old 29-variable explanation incorrectly called the printed gate `f2`; prior audit receipts are historical and did not detect that mismatch.

`check_aliases.py` checks the named circuit inputs, explanatory gate expressions and corresponding graph rows, printed gate names, displayed definitions, and extracted PDF text for both presentations. In particular, the display uses `E=λ` and `I=θ`, while the circuit computes `E=XY` and `I=ng`; the respective residuals enforce those equalities at a zero. The check does not replay Lean or audit proof provenance.
