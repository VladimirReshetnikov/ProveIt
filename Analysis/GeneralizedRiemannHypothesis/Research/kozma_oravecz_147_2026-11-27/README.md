# Zero-free gaps for the spectrum ±{N,4N,7N}

The note gives the exact supremum, a family approaching it, and uniqueness
of both the limiting nonnegative polynomial and the six-point positive
annihilating probability measure on a fixed critical interval.

- kozma_oravecz_147.pdf: proof and source references.
- kozma_oravecz_147.tex: standalone LaTeX source. Run pdflatex twice.
- certify.js: original exact outward-rounded interval certificate. Run with Node.js.
- verify.py: independent exact rational checks, including the uniqueness determinant.
  Run with Python 3 without optimization, so assertions are enabled.

No third-party Node.js or Python dependencies are needed. The calculations
are unconditional; they do not assume the Riemann hypothesis or GRH.
