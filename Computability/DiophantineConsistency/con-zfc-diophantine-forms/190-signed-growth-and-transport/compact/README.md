# Free-chart polynomial centers: ten positive variables, degree 190

The new result is defined by `equation.json` and proved in `PROOF.md`.
It has 10 strictly positive integer variables, exact total degree 190,
and 119 live binary operations. Its lack of positive-integer zeros is
equivalent in ZFC to Con(ZFC), composed with the named inherited
native/refutation calibration. No global optimum or newly compiled
end-to-end Lean/Rocq certificate is claimed.

The new transport `L=U*E*b^2` makes the free-quotient chart compatible
with the whole-product center. It handles the previously troublesome
auxiliary index-three branch and lowers the carrier degree from 54 to 41,
leaving the norm-defect term to determine degree 190.

Run with Python 3.10+ and no extra packages:

    python3 -B verify.py
    python3 -B -O verify.py
    python3 -B build.py

The verifier independently checks the entire center, the source-row
transformation, the exact highest form, all actual fixed coefficients by
finite reconstruction, and genuine occurrence of every input. It does
not import the circuit producer and does not search for zeros.

The fixed numerals are not represented only by hashes: their full bytes
are in `source/coefficients/`, and `source/rebuild_coefficients.py`
reconstructs them from the finite 943-tile recipe. The coherent tuple is
unchanged from the authenticated source-172 parent. The full ordinary
proof texts needed by that parent's arithmetic interface are retained
under `source/upstream172/`; the selected-file ledger explains the scope.
Historical verification claims inside these unmodified sources refer to
their original packages, not a newly replayed formal development here.

The main endpoint is positive-domain. Section 9 gives a 30-unrestricted-
integer, degree-380 conversion, which is not presented as a variable-count
record. The current improvement is the degree reduction in the ten-positive
family against inspected 214-, 208-, and 206-degree constructions.

New material follows the ProveIt MIT No Attribution license. Original
notices and licenses accompany the inherited data and proof texts.
