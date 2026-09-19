# A counterexample to winner stability in ordinal Chomp

Research report prepared for Vladimir Reshetnikov, 19 September 2026.

## Result

Let S = <4,6,9> be the numerical semigroup with gaps {1,2,3,5,7,11},
ordered by x <=_S y exactly when y-x belongs to S. Its ordinal square is
S^2 = {omega*a+b : a,b in S}, with the order induced by ordinary ordinal
subtraction, not coefficientwise subtraction under the natural sum.

Chomp on S is a second-player win. Chomp on S^2 is a first-player win:
the first move **omega*4+4** leaves a position of Grundy value zero.
The same move wins at every ordinal exponent at least 2. Thus
**ch(4,6,9) = 2**.

The multiplication order matters: `omega*4+4` is NOT `4*omega+4`.

This is a computer-assisted counterexample to Conjecture 4.1 in the first
version of Fabián Rivero Herrera's arXiv:2504.07317, and a negative answer
to Question 4.6 in its third version, already for natural-number generators.
The source check located no later resolution. That search is not an
exhaustive priority determination. The result has not been externally
refereed or formalized in a proof assistant.

## Start here

- `ordinal_chomp_counterexample.pdf`: the 17-page article, including detailed
  proofs, a block-order diagram, the complete finite certificate, and references.
- `ordinal_chomp_counterexample.tex`: editable LaTeX source.
- `certificate_tables.tex`: complete certificate table included by the article.
- `code/verify_certificate.py`: standalone independent finite-game verifier.
- `code/make_certificate.py`: deterministic certificate generator.
- `code/test_certificate.py`: six regression tests, including corruption tests.
- `code/export_tables.py`: regenerates the LaTeX table from the JSON certificate.
- `data/certificate.json`: machine-readable proof certificate and transitions.
- `data/verification.json` and `data/verification.txt`: successful verification.
- `data/exact_boundary_values.csv`: all 4,301 exact, untruncated boundary values.
- `data/apery_values.csv`: exact poisoned and normal Apéry values for the 258
  positive semigroup elements through 264.
- `data/tests.txt`: recorded regression-test output.
- `build.sh`, `build.ps1`: verification followed by PDF compilation.
- `SHA256SUMS.txt`: integrity hashes of the distributed files, excluding itself.

## Mathematical verification

Python 3.9 or later and its standard library suffice; no installation of
third-party packages or network access is required. The supplied scripts
were run successfully with Python 3.13.5.

To check the existing certificate without regenerating it:

```sh
python code/verify_certificate.py
python code/test_certificate.py
```

To regenerate and then check it:

```sh
python code/make_certificate.py
python code/verify_certificate.py
python code/test_certificate.py
python code/export_tables.py
```

The verifier prints:

```text
VERIFIED
Exact finite positions: 4301
Memoized finite states: 4346
Local residual identities: 233
Repeated boundary state: 237 = 265 (187 entries); period 28
All full-ideal labels are 2, meaning Grundy value at least 2.
SHA-256: f408697a728c12efd4cca15b73d055b3c747a17e5b06a5897969973ceb1697dc
```

The generator and verifier use different finite-game representations.
The verifier does not import the generator. It reconstructs semigroup
membership from 4, 6, and 9 and recomputes EVERY displayed boundary value
by the literal finite-poset mex recursion, using full integer Grundy values.
The six tests also check the general boundary recurrence on eight numerical
semigroups at three cutoffs, and verify rejection of deliberately corrupted
certificate data.

## Why a finite certificate proves an infinite assertion

The article reduces the winning-move claim to

    g(Ap(S,t) minus {0}) >= 2, for every positive t in S.

For each of 17 gap ideals C, the certificate records a row for the finite
boundary board with first missing element x and tail x+C. Labels have the
following meanings:

    0 = Grundy value exactly 0
    1 = Grundy value exactly 1
    2 = Grundy value at least 2

In particular, a label 2 does NOT assert an exact value of 2.

The article proves a finite-memory recurrence. The stored rows run from
12 through 264. Its eleven-row state before computing row 237 is exactly
the same as its state before computing row 265: rows 226..236 equal rows
254..264. All 187 entries agree, and every full-tail coordinate in the
initial segment and cycle has label 2. Determinism proves the same
assertion for all subsequent rows. The exceptional positive first moves
below 12 are checked separately.

The repeated state, together with the proved recurrence, is the crucial
infinite step. No assertion about an infinite board is inferred merely
from a large finite truncation. The exact, unbounded Grundy sequence is
not claimed to be eventually periodic; only each fixed bounded profile is.

The mathematical trust boundary consists of the written reduction and
recurrence proof, plus ordinary exact Python computation of a small finite
certificate. Separate implementations reduce coding risk but are not a
substitute for a proof-assistant kernel or independent human review.

## Building the PDF

Use a normal TeX Live or MiKTeX installation with pdfLaTeX and the packages
listed in the source preamble, including newtx, TikZ, tcolorbox, cleveref,
xurl, and microtype. The bibliography is embedded in the main source;
BibTeX is not required. No external image files or custom font files are
needed.

On a POSIX shell:

```sh
sh build.sh
```

On Windows PowerShell, with `python` and `pdflatex` on PATH:

```powershell
.\build.ps1
```

The POSIX build was executed end to end. The PowerShell wrapper is supplied
for convenience; it was not executed in the Linux verification environment.

Alternatively, run the verification commands above and then run the
following command two or three times, to resolve references and pagination:

```sh
pdflatex -interaction=nonstopmode -halt-on-error ordinal_chomp_counterexample.tex
```

Recompilation may change the PDF's byte hash because of timestamps or TeX
versions. The canonical JSON certificate is deterministic.

## Primary references

1. Fabián Rivero Herrera, *A poset game in submonoids of additively
   indecomposable ordinals*, arXiv:2504.07317v1 (9 April 2025),
   Conjecture 4.1. https://arxiv.org/abs/2504.07317v1
2. Fabián Rivero Herrera, *Hanf numbers for poset games*,
   arXiv:2504.07317v3 (5 January 2026), Example 3.2 and Question 4.6.
   https://arxiv.org/abs/2504.07317v3
3. Ignacio García-Marco and Kolja Knauer, *Chomp on numerical semigroups*,
   Algebraic Combinatorics 1 (2018), no. 3, 371–394.
   https://doi.org/10.5802/alco.16
4. Mišo Gavrilović and Alexander Thumm, *The ordered join of impartial
   games*, arXiv:2104.13131v2 (18 May 2021), especially Theorem 2.6.
   https://arxiv.org/abs/2104.13131v2
