Seven terms are necessary at discriminant -152
Compile report.tex with pdflatex (twice).
python3 verify.py runs the exact finite certificate (standard library only).
python3 regenerate.py independently audits class-polynomial coefficients,
using mpmath interval arithmetic with the analytic tails in the report.
Both scripts consume polynomials.json, ordered by ascending degree.
After extracting, sha256sum -c SHA256SUMS checks the archive contents.
