# The optimal torsion window and one-sided prime tests

Start with **torsion-window.pdf**. It answers the optimal-order question raised in the earlier ProveIt exact-torsion report, proves the matching obstruction, and extends the result to elliptic formal groups. **prime-tests.pdf** gives independently proved analytic criteria and an excursion bound. The results in these notes are mathematical proofs, with finite computational checks. No new Lean proof files are claimed.

## What is established

| Question | Result |
| --- | --- |
| How many cyclotomic shells always suffice at a fixed positive Gauss radius? | The least upper exponent is h0 + floor(p^(h0−1) B). A whole torsion coset works. One polynomial simultaneously attains the minimum budget and degree to block a window. |
| Does the result survive beyond roots of unity? | A one-dimensional height-d formal group over an unramified p-adic base has the same formula with p^(d(h0−1)) in the floor. Over a ramified base a valuation cutoff has an exact formula in terms of torsion valuations. |
| Can a single prime sum detect one nonreal class-group Hecke factor? | Yes. The exact coefficient field of an isolating weight is the maximal real cyclotomic field of its order. Discriminant −95 gives an explicit three-form test. The resulting square-root estimate is an open analytic input. |
| How large are negative excursions of the modulus-one twisted detector? | Assuming the upstream Dirichlet theorem, its normalized lower limit lies in a conductor-independent width 0.09238284… around an explicit conductor-dependent center. A parity condition on relations of zero ordinates characterizes attainment of the lower endpoint. |

## Reproduction

Use a standard TeX Live installation that includes Latin Modern, amsmath, mathtools, hyperref, fancyhdr and enumitem. From this directory run

    latexmk -pdf torsion-window.tex
    latexmk -pdf prime-tests.tex

Each main source includes layout.tex and its files in sections/. The PDFs were compiled with pdfLaTeX. Run the Python programs below from this directory. All except the final one use the Python standard library. Their recorded outputs are in checks/.

    python3 checks/verify_torsion.py
    python3 checks/verify_formal_height.py
    python3 checks/verify_d95.py
    python3 checks/verify_gaussian.py
    python3 checks/oscillation_constants.py

The last script uses mpmath. It cross-checks the evaluations at conductors 7 and 23 via separate expansions at zero and one. Its decimal outputs are numerical illustrations. The formal-height checker tests the group metric and computes examples of actual Lubin–Tate Newton polygons. The Gaussian and −95 prime enumerations check the arithmetic interpretation of the prime weights; they do not certify asymptotic estimates.

## Source scope

sources/ contains an inventory of the preceding archives and notes on the pinned GitHub source. The directory contained 31 ZIP files; 28 were retrieved and their TeX compared. Three entries were identified from metadata. The two reports compare their results with the closest predecessors. No claim of exhaustive bibliographic priority is made. The source Lean development was inspected, and its publicly reported checks were distinguished from the work performed here.
