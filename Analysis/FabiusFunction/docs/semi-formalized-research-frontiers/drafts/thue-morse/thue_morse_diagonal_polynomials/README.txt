Diagonal Polynomials and Dyadic Block Geometry in Repeated Thue--Morse Summation
================================================================================

This archive accompanies the article of the same title.  It contains exact
formulas, Wolfram Language implementations, independent Python verification,
and the generated profile figure.

Main result
-----------

Let epsilon(q)=(-1)^(binary digit sum of q), and put r=k-n-1.  For k>=n+1,

    s[n,k] = D_r(n),

where

    D_r(x) = Sum_{q=0}^{Floor[r/2]}
             epsilon(q) Binomial[2 x+r-2 q-1, r-2 q].

Equivalently,

    Sum_{r>=0} D_r(x) z^r = E(z^2)/(1-z)^(2 x),
    E(z) = Product_{j>=0} (1-z^(2^j)).

The article proves the diagonal degree and coefficient structure, Sheffer and
ruler-function recurrences, exact half-integer roots, and the full finite-block
geometry of every row.

Files
-----

  thue_morse_diagonal_polynomials.tex
      Complete 1,763-line, 56,530-byte LaTeX source; SHA-256
      eee5751653bb19ec04042f51ded34d74bf8862f5b06b49d47e68ea78bb689c45.

  thue_morse_diagonal_polynomials.pdf
      Synchronized 24-page, 778,595-byte A4 article; SHA-256
      8db0c4e0a4fcf682bd3e1311f7d8197ea04dcca56e102236b52494267d99cbbe.

  thue_morse_table.wl
      Standalone Wolfram Language implementation.  It provides:
        diagonalPolynomial[r]  symbolic D_r(x);
        diagonalRuler[r]       consecutive-polynomial recurrence;
        sDiagonalValue[n,k]    direct finite-sum evaluation;
        sFast[n,k]             hybrid arbitrary-entry evaluator;
        rowBlock[n]            complete first block for moderate n;
        sByBlock[n,k]          signed block lookup.

  experiments.py
      Fully commented Python/SymPy verification code.  It derives values by
      independent routes, checks all main identities with exact arithmetic,
      writes verification_report.txt, and regenerates the profile figures.

  verification_report.txt
      Output from a successful exact verification run.

  row_profiles.pdf
  row_profiles.png
      Vector and raster forms of the article's normalized-row figure.

  The former package checksum ledger is retired; its historical bytes remain
      recoverable from Git.

Wolfram Language use
--------------------

From a Wolfram Language session whose current directory is this folder:

    Get["thue_morse_table.wl"];

    sFast[20, 123456789]              (* one arbitrary exact entry *)
    Factor[diagonalPolynomial[12]]    (* a symbolic diagonal law *)
    Table[diagonalRuler[r], {r,0,20}] (* consecutive diagonal laws *)

For a moderate fixed n and many queries, evaluate rowBlock[n] once and then use
sByBlock[n,k].  For k close to n, sDiagonalValue[n,k] is normally preferable.
The hybrid sFast[n,k] first reduces k to one signed dyadic block, then uses the
zero, plateau, reflection, and complement identities before applying the exact
diagonal sum.

The build container did not include a Wolfram kernel, so the .wl file was not
executed directly here.  Its branch logic is mirrored by table_value_fast
in experiments.py and was checked against every residue of exact row blocks
for n=0,...,5, followed by three signed blocks for each n.

Python verification
-------------------

Requirements:

    Python 3.10 or later
    SymPy
    Matplotlib

Run:

    python experiments.py

The final line should be:

    All exact checks passed.

The program overwrites verification_report.txt, row_profiles.pdf, and
row_profiles.png in this directory.

Building the PDF
----------------

A recent TeX Live installation with latexmk is recommended.  From this folder:

    latexmk -pdf -interaction=nonstopmode -halt-on-error \
      thue_morse_diagonal_polynomials.tex

The current publication was rebuilt on 4 September 2026 from absent
auxiliaries using exactly three serial halt-on-error pdflatex passes. They
produced 23 pages/768,048 bytes, 24 pages/778,598 bytes, and finally 24
pages/778,595 bytes. The final log has no TeX error, unresolved reference or
citation, or rerun request; title, author, subject, and keywords metadata are
present. Every page is A4 at rotation zero, rendered, and contains extractable
text. All 22 font rows are embedded and subset, seven are Libertinus, and none
is Type 3. Representative title, body, formula, figure, and final pages passed
visual inspection. Generated sidecars were removed, and no checksum ledger is
a live publication gate.

Clean auxiliary files with:

    latexmk -c thue_morse_diagonal_polynomials.tex

Reproducibility notes
---------------------

* All mathematical identity checks use Python integers or exact SymPy
  rationals.  Floating-point arithmetic is used only for plotting.
* The PDF is A4, unencrypted, text-searchable, and uses embedded/subset fonts.
* The current article was built and verified on 4 September 2026.
