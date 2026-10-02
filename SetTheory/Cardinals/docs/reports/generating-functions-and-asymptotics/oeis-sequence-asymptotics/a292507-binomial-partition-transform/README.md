A292507 all-orders asymptotics and asymptotic inversion
Research note, 1 October 2026

FILES
- a292507_asymptotics.pdf: complete ten-page mathematical report
- a292507_asymptotics.tex: editable, standalone LaTeX source
- reproduce.py: arbitrary fixed-order coefficient algorithm, exact-integer
  sequence computations, numerical forward and model-inverse diagnostics
- verification.json: recorded order-six results through n=10000
- validate_inverse.py: symbolic check of the two displayed inverse polynomials
- inverse_verification.json: recorded result of that check

REPRODUCE
Requires Python 3 with sympy and mpmath, plus LaTeX for the report.
Tested with Python 3.12.14, SymPy 1.14.0, and mpmath 1.3.0.
From this directory:
  python3 reproduce.py --order 6 --max-n 10000 --output verification.json
  python3 validate_inverse.py
  pdflatex a292507_asymptotics.tex
  pdflatex a292507_asymptotics.tex
The coefficient order may be any nonnegative finite integer. Symbolic cost
increases with order. The routine inverse_polynomials(M,J) in reproduce.py
computes any fixed finite inverse order J for the M-term model.

SCOPE
The all-orders forward expansion, real-model inversion, and shrinking
integer-threshold brackets are proved in the report. Numerical checks
support but do not replace those proofs. Big-O constants for the integer
brackets are existence constants rather than certified numerical thresholds.
Floating-point diagnostics are not interval certificates.

The leading binomial-smoothing method is established prior art. Literature
searches did not locate these particular higher corrections or inverse,
but the report does not claim publication priority. It does not prove
convergence of the correction series or a complete exponential transseries.

The TeX source has explicit font maps so it also compiles in minimal TeX Live
installations where a default font map has not been configured.
