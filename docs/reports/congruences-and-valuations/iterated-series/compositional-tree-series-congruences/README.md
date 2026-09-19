# Prime-power congruences for compositional tree series

Research report prepared for Vladimir Reshetnikov, September 19, 2026.

## Main result

For the formal series A_l(x) = x exp(A_l composed with itself l times),
write A_l(x) = sum_{n>=1} a_l(n) x^n/n!.

The OEIS A396805 claim a_5(n) = n (mod 5) is false. Its first failure is
n=23, and its complete exception set is {20j+3,20j+4 : j>=1}.
At every exceptional index the residue is 2. The report proves eleven
other conjectural assertions in OEIS A396803, A396804, A396805, and A396806.

The general theorem reduces coefficients modulo p^alpha to a finite sum
over typed rooted trees on fewer than p^alpha labels. It implies:

- eventual period dividing p^alpha(p-1), starting no later than n=p^alpha;
- rational ordinary generating functions for coefficient residues;
- a_l(n) periodic in l modulo M with parameter period dividing M^2;
- exact classification of a_l(n)=n (mod p) for every n:
  no restriction for p=2; 3 divides l for p=3; p^2 divides l for p>=5.

All infinite statements have mathematical proofs in article.tex/article.pdf.
Finite computation is corroboration, not a substitute for those proofs.
The report is not independently peer reviewed or formally verified.
The numerical counterexample is already present in the published OEIS
b-file; no claim is made to having computed that integer for the first time.

## Files

- article.tex: standalone LaTeX source, bibliography included.
- article.pdf: compiled article.
- code/iterative_series.py: standard-library-only exact and modular
  coefficient routines, independent Fraction implementation, and two
  independent small-core enumerators.
- code/verify.py: regenerates the checks and data.
- data/a396805_first40.csv: exact early coefficients and residues.
- data/residues_ell0_to12_n1_to260.csv: direct-computation residue grid.
- data/core_certificates.json: exact small-core type frequencies.
- data/prime_witnesses.json: instances of the proved infinite witness formula.
- data/verification_summary.json: test outcome and scope.
- OEIS_corrections.txt: concise proposed mathematical updates, not submitted.
- SOURCE_STATUS.md: source URLs, inspection date, and priority limitations.
- build.sh: two-pass PDF build using a temporary local directory.

## Reproduce

Python 3.10 or later; no third-party Python packages required:

    python3 code/verify.py
    python3 code/iterative_series.py 5 40
    python3 code/iterative_series.py 5 260 --modulus 5

The recorded run passed 29,122 assertions. The first 23 coefficients for
l=5 agree between the Bell recurrence and the independent exact ordinary
power-series fixed-point algorithm. The large residue grid and parameter
period tests use the original recurrence without assuming the periods.
Timing depends on the machine; the mathematical output does not.

To rebuild the PDF with a normal TeX Live or MiKTeX installation:

    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex

On a POSIX system, ./build.sh keeps auxiliary files in .build instead.
Packages include newtxtext/newtxmath, amsmath/amsthm/mathtools, microtype,
geometry, booktabs, enumitem, fancyhdr, tcolorbox, listings, and hyperref.
Font packages are obtained through the user's TeX distribution; no font
files are included in the archive.

## Conventions

Iteration zero is the identity series x. Superscripts referring to iteration
must not be read as ordinary powers. Coefficients are EGF coefficients,
so a_l(n) is n! times the ordinary coefficient. Arrays include a_l(0)=0.
The modular recurrences contain no division by a nonunit. In the finite-core
power sums, use 0^0=1; this controls the initial nonperiodic terms.

The integer-valued parameter-polynomial argument does not assume that all
polynomials in l have integral ordinary coefficients.
