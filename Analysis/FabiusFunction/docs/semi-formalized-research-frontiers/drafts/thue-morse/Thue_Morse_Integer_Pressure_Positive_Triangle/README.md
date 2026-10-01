# The Full Positive Triangle in Integer Thue Morse Pressure

For every integer m>=2 and 1<=r<m, this note proves both
H_(m,r)=[a^(2r)]h_a(1/2)>0 and
E_(m,r)=[t^(2m+2r)]p_m(t/pi)>0.

Thus every even pressure coefficient strictly between degrees 2m and 4m is
positive. A new dyadic tangent-product comparison closes the full triangular
range left by the earlier sufficient region m>=3r. This is a separate report;
previously delivered papers are unchanged.

## Contents

- `article.pdf`: seven-page standalone mathematical report
- `article.tex`: editable LaTeX source
- `code/run_all.py`: complete exact verification entry point
- `code/check_triangle.py`: 91 rational response/pressure pairs, plus 28 independent direct pressure checks
- `code/check_basis_signs.py`: 36 exploratory exact eigenbasis-sign checks, explicitly separate from the proof
- `code/check_m2_cubic.py`: exact certificate for the negative later degree-twelve coefficient
- `data/`: exact reference values and verification results
- `PROOF_STATUS.md`: proved scope and remaining questions
- `SOURCES.md`: versioned source provenance
- `VISUAL_QA.md`: rendered-page verification record
- `SHA256SUMS.txt`: file-integrity manifest

## Verification

Run `python3 code/run_all.py` with Python 3 and SymPy installed. All coefficient
and matrix calculations use exact rational arithmetic. The universal proof
uses no numerical sign test; the finite values are regression checks.

Build with two runs of `pdflatex article.tex` on a normal TeX installation,
or use `build_local.sh` for the restricted environment used for this package.
The latter builds the format locally rather than modifying a system TeX tree.

This is ordinary mathematical research, independently reviewed but unrefereed
and not formally verified in Lean. Positivity of individual eigenbasis
coefficients remains conjectural. Positivity of all subsequent pressure
coefficients is false, as shown by the included m=2 degree-twelve certificate.
