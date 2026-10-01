THE FIRST POSITIVE COEFFICIENT IN INTEGER THUE MORSE PRESSURE
1 October 2026

Main result
For every integer m >= 2, the coefficient [t^(2m+2)] p_m(t/pi) is strictly positive. The note gives an explicit finite Bernoulli formula and proves positivity of the quadratic Perron response at every noninteger point. It also proves an absolutely convergent inverse-branch formula, an explicit positive lower bound, and a large-m expansion with an exponentially smaller error.

Scope
This answers the precisely identified question in the ProveIt integer-pressure manuscript. It does not assert an elementary closed form in m, an exhaustive priority search, a noninteger-order theorem, or a pressure expansion uniform in m and phase. The proof is ordinary mathematics, not externally refereed or Lean formalized.

Files
- positive_thue_morse_coefficient.pdf: eight-page research note
- positive_thue_morse_coefficient.tex: complete editable proof source
- SOURCES.txt: precise repository and primary literature references
- checks/: independent exact Fourier and finite-tree checks, plus asymptotic diagnostics
- data/: regenerated check outputs and logs
- validation.json: verification and PDF quality-control record
- SHA256SUMS: file integrity hashes

Build the PDF
Run bash build.sh using a standard TeX Live installation with pdfLaTeX, Latin Modern, AMS packages, geometry, microtype, booktabs, hyperref and xurl. Three passes resolve references.

Run checks
Install the dependencies in requirements.txt, then run python checks/run_all.py.
The rational Fourier check covers m=2,...,10 and exactly reproduces all three coefficients printed in the source. Two finite-basis checkers compare the Bernoulli formula with those Fourier values, verify the stated coefficient bounds, and check positivity through m=30. Twenty finite inverse-tree identities are compared at 70-digit precision with exact rational matrix powers. Large-order diagnostics use 80-digit arithmetic. These finite checks guard against transcription mistakes; the universal proof is in the note.
