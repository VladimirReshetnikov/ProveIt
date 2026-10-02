# A279619: an exact gamma constant and two asymptotic scales

Research report prepared for Vladimir Reshetnikov, October 1, 2026.

## Main result

For a(0)=1, a(1)=2 and

    (n+1)^2 a(n+1) = (26n^2+13n+2) a(n)
                    + 3(3n-1)(3n-2) a(n-1),  n >= 1,

put G = Gamma(1/7) Gamma(2/7) Gamma(4/7). The report proves

    a(n) ~ sqrt(3*pi)/G * 27^n / n^(3/2),
    sum(a(n)/27^n, n>=0) = 3G/(8*pi^2),

and an expansion to every fixed algebraic order with a remainder of the
next order. It also proves a continued-fraction companion and the exact
amplitude of its alternating recessive solution. Convolution powers,
Lambert-W inverse expansions, and discrete rounding bounds are included.

## Files

- `article.pdf`: compiled research article.
- `article.tex`: complete source; numerical tables are included directly.
- `code/verify.py`: exact symbolic/rational checks and numerical diagnostics.
- `data/verification.json`: exact coefficients through order 12, eight zero
  rational certificates, rational bounds for C and L, and decimal enclosures.
- `data/dominant_errors.csv`: signed relative errors for the dominant expansion.
- `data/minimal_errors.csv`: signed normalized errors for the recessive expansion.
- `data/inverse_errors.csv`: continuous inverse errors evaluated at exact a(n).
- `data/run_log.txt`: output of the successful verification run.
- `SOURCE_AUDIT.md`: proof dependencies, source comparison, and novelty limits.
- `requirements.txt`: pinned versions used for verification.
- `SHA256SUMS.txt`: integrity hashes of the supplied files, excluding itself.

## Run the verification

Python 3.10 or newer is recommended; the supplied run used Python 3.13.5,
SymPy 1.14.0, and mpmath 1.3.0.

    python -m pip install -r requirements.txt
    python code/verify.py

The script can run from any working directory. It writes its output beside
this README in `data/`. No network connection is used by the verification
itself. Do not run Python with `-O`: the tests intentionally use assertions.
Installing dependencies may require internet access.

The successful run checked eight rational differential-equation identities,
formal expansions through order 12 for both roots, recurrence values through
n=1000, 100 exact Wronskians, and 41 convolution identities. It certified
rational enclosures for C and L, then outward-rounded them to intervals of
width 10^(-100). Floating-point tables use 190 decimal working digits; they
are diagnostics, not certified bounds on all asymptotic remainders.

## Build the PDF

Use a TeX Live installation containing amsmath, amsthm, newtx, microtype,
tcolorbox, hyperref, bookmark, and the other packages listed in article.tex.
Run from this folder:

    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex

A third pass may be needed after changes that move the table of contents.
Python is not required to build the PDF. All external special values used
in the proof are cited in the article; no third-party papers or font files
are redistributed in this bundle.

## Interpretation and limitations

The OEIS entry inspected still labeled the leading asymptotic conjectural.
The first three corrections were already calculated formally in O'Brien's
thesis, and the hypergeometric generating function was already recorded in
OEIS. The report credits both and does not claim global priority.

The proof uses two established classical special-value identities: a
Ramanujan 1/pi series and the level-seven elliptic period. They are stated
with explicit normalizations and sources. The Python program is not a Lean
proof of those identities or of the analytic transfer theorem.

The two-scale statement concerns a specified exact recurrence basis. It is
not a canonical exponentially improved summation of the dominant formal
series. Effective numerical constants for the general asymptotic remainder,
the Lucas-congruence conjecture, a closed form for the continued-fraction
limit, and irrationality claims are not established here. Twelve further
research directions are included.

No changes were made to OEIS or to the ProveIt repository.
