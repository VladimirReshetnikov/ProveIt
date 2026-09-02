EXACT QUARTER-BASE EXTRAPOLATION FOR DYADIC SAMPLES
OF RVACHEV'S UP-FUNCTION SPLINE PREFIXES

Package contents
----------------

1. rvachev_up_dyadic_extrapolation.tex
   Complete LaTeX source of the article.

2. rvachev_up_dyadic_extrapolation.pdf
   Compiled 15-page article.

3. verify_extrapolation.py
   Standard-library-only Python program using fractions.Fraction for exact
   arithmetic.  It evaluates the finite Thue--Morse spline, constructs the
   q-binomial extraction row, performs the triangular Richardson extraction,
   solves the full rational Vandermonde system, computes reciprocal centered
   moments, and verifies the worked examples and optional exhaustive tests.

4. SHA256SUMS.txt
   SHA-256 checksums of the three principal files.

Main result
-----------

For a fixed dyadic x in [-1,1], reduce

    a = 1 - |x| = m/2^s

and put d=floor(s/2), rho=1/4, q_n=up_n(x).  Then, for every n>=s,

    q_n = up(x) + sum_{r=1}^d A_r(x) 4^(-r n),

and all d coefficients are nonzero when s>=2.  From any d+1 consecutive
values q_N,...,q_{N+d}, N>=s, the exact limit is

    up(x) = 1/(rho;rho)_d * sum_{j=0}^d
            (-1)^j rho^(j(j+1)/2) [d choose j]_rho q_{N+d-j}.

The article proves this by exact matched-cell moment deconvolution.  The
omitted centered random tail has the half-width of one polynomial spline
cell, so the Taylor expansion is finite.  At a reduced dyadic point, all even
derivatives beyond order 2 floor(s/2) vanish, leaving precisely the finite
quarter-base geometric tail above.

Running the verifier
--------------------

No third-party Python packages are required.

    python3 verify_extrapolation.py
    python3 verify_extrapolation.py --x=-11/16
    python3 verify_extrapolation.py --self-test-max-depth 7

The delivered version was checked with the last command.  It verified all 129
reduced dyadic cases through depth 7, using exact rational arithmetic.

Compiling the article
---------------------

A standard TeX installation containing amsmath, amsthm, hyperref, listings,
fancyhdr, lmodern, microtype, booktabs, and related common packages is enough.
Run:

    pdflatex -interaction=nonstopmode -halt-on-error \
      rvachev_up_dyadic_extrapolation.tex
    pdflatex -interaction=nonstopmode -halt-on-error \
      rvachev_up_dyadic_extrapolation.tex
    pdflatex -interaction=nonstopmode -halt-on-error \
      rvachev_up_dyadic_extrapolation.tex

Repository used for conventions and comparison
----------------------------------------------

https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/FabiusFunction/docs

Prepared 2 September 2026.
