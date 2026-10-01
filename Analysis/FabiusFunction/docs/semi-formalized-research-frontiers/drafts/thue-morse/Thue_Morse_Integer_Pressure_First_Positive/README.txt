THE FIRST POSITIVE COEFFICIENT IN INTEGER THUE MORSE PRESSURE
1 October 2026

Main result
For every integer m >= 2, the coefficient [t^(2m+2)] p_m(t/pi) is strictly positive. The note gives an explicit finite Bernoulli formula and proves positivity of the quadratic Perron response at every noninteger point. It also proves an absolutely convergent inverse-branch formula, an explicit positive lower bound, and a large-m expansion with an exponentially smaller error.

Scope
This answers the precisely identified question in the ProveIt integer-pressure manuscript. It does not assert an elementary closed form in m, an exhaustive priority search, a noninteger-order theorem, or a pressure expansion uniform in m and phase. The proof is ordinary mathematics, not externally refereed or Lean formalized.

Files
- positive_thue_morse_coefficient.pdf: nine-page research note (eight pages as delivered; see the editorial amendments below)
- positive_thue_morse_coefficient.tex: complete editable proof source
- SOURCES.txt: precise repository and primary literature references
- checks/: independent exact Fourier and finite-tree checks, plus asymptotic diagnostics
- data/: regenerated check outputs and logs
- validation.json: verification and PDF quality-control record
- SHA256SUMS: file integrity hashes (retired on filing; not in the repository)

Build the PDF
Run bash build.sh using a standard TeX Live installation with pdfLaTeX, Latin Modern, AMS packages, geometry, microtype, booktabs, hyperref and xurl. Three passes resolve references.

Run checks
Install the dependencies in requirements.txt, then run python checks/run_all.py.
The rational Fourier check covers m=2,...,10 and exactly reproduces all three coefficients printed in the source. Two finite-basis checkers compare the Bernoulli formula with those Fourier values, verify the stated coefficient bounds, and check positivity through m=30. Twenty finite inverse-tree identities are compared at 70-digit precision with exact rational matrix powers. Large-order diagnostics use 80-digit arithmetic. These finite checks guard against transcription mistakes; the universal proof is in the note.


Editorial amendments (ProveIt, 2026-10-01)
------------------------------------------

Made in the editorial pass after batch 72 of docs/incoming/ (see
docs/incoming/README.md). Every change to the source is marked
% ed. (2026-10-01), every change to a program ed. (2026-10-01). The
mathematical text is unchanged; the byline and pdfauthor entry ("Research
note prepared for Vladimir Reshetnikov with OpenAI") are kept as delivered.
This is the first of thirteen packages of one series, filed beside the
manuscript they continue, ../Thue_Morse_Integer_Pressure/, in logical order:
the positivity series ../Thue_Morse_Integer_Pressure_First_Positive/,
../Thue_Morse_Integer_Pressure_Higher_Positive/,
../Thue_Morse_Integer_Pressure_Positive_Triangle/,
../Thue_Morse_Integer_Pressure_Feedback_Boundary/,
../Thue_Morse_Integer_Pressure_Beyond_Boundary/,
../Thue_Morse_Integer_Pressure_Linear_Region/,
../Thue_Morse_Integer_Pressure_Full_Range/, and the sign series, which
imports the full-range theorem,
../Thue_Morse_Integer_Pressure_Sign_Changes/,
../Thue_Morse_Integer_Pressure_Sign_Densities/,
../Thue_Morse_Integer_Pressure_Negative_Bound/,
../Thue_Morse_Integer_Pressure_First_Negative/,
../Thue_Morse_Integer_Pressure_Cluster_Asymptotics/, with the dataset
../Thue_Morse_Integer_Pressure_First_Negative_Data/. An earlier version of
../Thue_Morse_Integer_Pressure_Full_Range/, The Full Pressure Positivity
Range for Large Integer Orders (m >= 4096), was superseded by it and not
filed; neither was a duplicate archive.

- positive_thue_morse_coefficient.tex: an unnumbered environment ednote
  ("Editorial note (ProveIt, 2026-10-01)") is defined after the theorem
  environments (no counter changes). Three notes:
  - after Theorem 1.1 and the sign pattern (7): C_m = E_{m,1} and
    B_m = H_{m,1} in the later packages' notation; Theorem 1.1 and B_m > 0
    are the case r = 1 of Theorem 1.1 of
    ../Thue_Morse_Integer_Pressure_Positive_Triangle/, and C_m > 0 that of
    ../Thue_Morse_Integer_Pressure_Full_Range/; the finite Bernoulli
    formula, pointwise positivity off the integers, the lower bound (6) and
    Corollary 6.1 are proved only here;
  - after the second question: answered by the series (positive at every even
    degree strictly between 2m and 6m, sharp at m = 2; both signs
    infinitely often beyond, with positive lower densities; N_m >= 6m,
    N_m = gamma m - log log(2m)/Lambda + O(1), gamma in
    (6.662966, 6.662968); N_m certified for m <= 128); the first and
    third questions are not treated;
  - before the bibliography, a series map: the thirteen packages in logical
    order, the superseded earlier version of the full-range article, and the
    filed directory of every source cited; [1] is
    ../Thue_Morse_Integer_Pressure/, whose question now carries a note of
    2026-10-01; and a Lean crosswalk: no declaration concerns p_m, while
    Fabius.evenZeta_eq_bernoulli (EvenZetaValues.lean) is the Bernoulli
    evaluation that makes c_j and R_m rational.
- positive_thue_morse_coefficient.pdf: rebuilt from the amended source with
  three pdflatex passes (MiKTeX 26.2, pdfTeX 1.40.29), on a copy: 9 A4 pages
  (8 as delivered), 367,993 bytes; all 18 fonts embedded, none Type 3; the
  final log has no error, overfull or underfull box, undefined or multiply
  defined reference, duplicate destination, or rerun request. The pages
  carrying the notes were rendered and inspected.
- checks/run_all.py and its five checkers: new option --output-dir
  (default data/rerun/; the console logs go there too), with LF line
  endings. As delivered, every checker overwrote its recorded file or log in
  data/, with CRLF line endings on Windows. Pass --output-dir data, on a
  copy, to regenerate the recorded files. A checker that reads another
  checker's record reads the recorded file, as delivered. On the ProveIt
  machine use py rather than python3/python. A rerun of the amended
  run_all.py on a copy (2026-10-01, Python 3.14.4, SymPy 1.14.0, mpmath
  1.3.0) passed and wrote all five JSON records and five logs equal to the
  recorded ones byte for byte.
- build.sh: kept as delivered; it writes build/ here and copies the PDF
  over the filed one: build on a copy.
- validation.json: pdf_pages set to 9; its other entries are as delivered.
- README.txt: the page count and the retired ledger under "Files", and this
  section.
