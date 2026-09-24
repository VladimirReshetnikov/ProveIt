# Cycles refute infinite log-concavity for chromatic coefficients

Research report and exact computational certificates, September 19, 2026.

## Result

For the simple cycle C_n (n >= 3), let a be the absolute chromatic
coefficient sequence, indexed by increasing degree:

    a = (0, n-1, binomial(n,2), ..., binomial(n,n)).

Use zero padding and L(a)[k] = a[k]^2 - a[k-1]*a[k+1]. No additional
absolute values are taken during iteration. The first negative iterate is:

| Cycle size | First failure depth |
| --- | --- |
| 3 <= n <= 11 | Never: infinitely log-concave |
| n = 12 | 5 |
| 13 <= n <= 16 | 4 |
| n >= 17 | 3 |

Every cycle passes its first two iterations. In each finite case, index 2
is negative at the first failure. C_12 is the smallest **cycle**
counterexample; no minimum over all simple graphs is claimed.

The exact third-iterate witness, valid for all n >= 3, is

    -n^3*(n-1)^8*(n+4)*(2*n^4-12*n^3-327*n^2-412*n+36)/103680.

For n=17 it equals -28272276537344. The sign for all n >= 17 is proved by
shifting the quartic to n=m+17, where every coefficient is positive.
The positive cases are certified by the invariant 3-factor log-concavity
cone, not inferred from a long but finite list of positive iterates.

## Scope and priority

The target is Conjecture 21 in Amdeberhan and Moll, *Infinite
log-convexity*, as formulated on page 9 of the publisher's PDF. A targeted
search did not locate an earlier cycle counterexample, but no exhaustive
priority or current-open-status claim is made. The paper contains the
exact disproof independently of that bibliographic question. Standard
invariant-cone machinery is credited to McNamara and Sagan.

This is an AI-assisted, unrefereed research report. The exact calculations
and symbolic audits listed below were run; no Lean formalization or
independent human referee verification is claimed.

## Contents

- `article.tex`, `article.pdf`: the comprehensive article and its source.
- `verify.py`: typed, dependency-free exact checker and data generator.
- `minimal_verifier.py`: compact standard-library checker reproduced in
  the article's appendix.
- `derive_symbolic.py`: optional independent SymPy audit of the identities.
- `verification.txt`, `minimal_verification.txt`,
  `symbolic_verification.txt`: actual execution output.
- `data/certificates.json`: complete iterates for n=3,...,17 through the
  certifying cone or first failure, with exact ratios and negative values.
- `data/cycle_coefficients.csv`: the coefficient triangle for n=3,...,100.
- `data/third_iteration_witness.csv`: the signed degree-2 third-iterate
  witness for n=3,...,100.
- `data/witness_generating_function.json`: integer forward differences
  and the numerator of the generating function for
  w_m = -L^3(a^(17+m))[2], whose denominator is (1-t)^17.
- `source_notes.md`: precise primary-source provenance and search limits.
- `build.sh`: verification and LaTeX build commands.
- `requirements-optional.txt`: only the optional symbolic-audit dependency.

## Run and reproduce

Python 3.10 or later is required for the principal checker. The recorded
run used Python 3.13.5. No network connection is needed.

```sh
python verify.py
python minimal_verifier.py
```

The default verifies full rows C_3 through C_200, plus local prefix
identities up to n=10^12. The symbolic proof, not that finite range,
establishes the universal mathematical statement.

```sh
python verify.py --max-n 300 --write-data
```

The data files always have the fixed coverage described above. `--max-n`
changes only the verification range; it must be at least 17.

For the optional symbolic audit, use an environment with SymPy installed:

```sh
python -m pip install -r requirements-optional.txt
python derive_symbolic.py
```

SymPy 1.14.0 was used for the recorded run. This audit is not required to
check the finite integer certificates.

## Build the PDF

The source uses standard TeX Live packages, including newpxtext/newpxmath,
microtype, tocloft, tcolorbox, listings, and hyperref. Run from this folder:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Keep `minimal_verifier.py` beside `article.tex`, since the article includes
that source in its appendix. `./build.sh` runs the main checks and compiles
the article. The optional symbolic audit is a separate command.

## Data interpretation

All sequence entries in the JSON certificates are **decimal strings** to
avoid precision loss in JSON readers that use binary floating-point
numbers. Parse them as arbitrary-precision integers. Ratios such as
`32433025/8287488` are exact rational numbers. The CSV files similarly
contain exact decimal integers; spreadsheet applications may round large
values unless those columns are imported as text.

The full-row operator uses zero padding. The prefix operator computes
only entries whose neighbors are actually known; it does not silently
replace an unknown right-hand tail by zeros.

## Main additional results

The article proves that the coefficient sequence of exp(x)-1 has a
negative third iterate at index 2, namely -1/51840, and transfers that
strict obstruction to locally converging rescaled families. It also
shows that the witness sequence w_m is a positive degree-16 polynomial,
has a rational generating function with denominator (1-t)^17, and obeys
its seventeenth forward-difference recurrence.

No external research-paper PDFs, font files, checksum files, or temporary
LaTeX compilation files are included.
