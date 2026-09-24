# A counterexample to a decimal-length bound for tetration stabilization

Research report prepared for Vladimir Reshetnikov, 19 September 2026.

## Main result

Let c = 2547, q = 5^c, m = 2^(c+1), and let u be the least nonnegative residue
of -2 q^(-1) modulo m. Define A = 1 + q u.

The exact certificate verifies:

- A has 2544 decimal digits and ends in 1.
- v_2(A-1) = 1, v_2(A+1) = 2548, and v_5(A-1) = 2547.
- With T_0 = 1 and T_(n+1) = A^(T_n),
  nu_10(T_(n+1)-T_n) = min(1+2548 n, 2547(n+1)) for every n >= 0.
- The published congruence speed at height len(A)+2 = 2546 is 2548,
  whereas its permanent value is 2547. The exact sustained onset is 2547.

The all-height statement follows from the elementary proof in the article,
not from a finite experiment. Neither checker constructs an enormous tower.

## Research status and scope

The target is Conjecture 1 in Marco Ripà, *The congruence speed formula*,
NNTDM 27(4) (2021), p. 46 (Conjecture 2.1 on arXiv, p. 3).
A later paper by Ripà and Onnis claims to confirm this conjecture after giving
a valuation-based bound. The report explicitly audits that claim: the weaker
valuation bound is compatible with this counterexample; the decimal-length
bound is not.

Thus the outcome is an explicit counterexample/correction, not a claim that
all later sources regard the conjecture as open. Historical priority and
global minimality have not been established. This is a conventional
mathematical proof with exact-arithmetic certification, not a Lean or other
proof-assistant formalization. No third-party review is claimed.

## Files

- `article.pdf`: the complete research article.
- `article.tex`: self-contained LaTeX source with embedded bibliography.
- `counterexample.txt`: all 2544 decimal digits of A on a single line.
- `certificate.json`: exact verification data and crossover table.
- `verify.py`: construction and certificate verification; uses two CRT implementations.
- `verify_stream.py`: independent decimal-streaming residue checker, sharing no helpers.
- `tetration_tools.py`: exact valuation, onset, CRT, and small modular-tower routines.
- `test_tetration.py`: seven regression test methods, including independent modular towers.
- `search.py`: reproducible targeted CRT search.
- `search_results.json`: stored result for 4 <= c <= 2547.
- `verification_output.txt`, `test_output.txt`: outputs of checks actually run.
- `source_audit.md`: source locations and the status distinction.
- `build.sh`: rebuilds the PDF using pdfLaTeX.
- `validation_summary.json`: compilation, PDF inspection, and executed-check summary.

## Verify

Python 3.9+ is sufficient. No Python packages need to be installed.
Run from the extracted directory:

```sh
python verify.py
python verify_stream.py
python -m unittest -v test_tetration
python search.py --max-c 2547 --output search_results.json
```

The search is a filtered CRT-family search, not an exhaustive search over all
positive integer bases. Its validity is not needed to certify the final A.

`verify.py` uses explicit checks that remain active under `python -O`.
The independent checker reads the decimal file one digit at a time and verifies
its residues modulo 2^2549 and 5^2548 without reconstructing a modular inverse.

## Build the PDF

Run `sh build.sh` in a TeX Live installation with the packages used by
`article.tex` (including newtx, amsmath, amsthm, microtype, tcolorbox, listings,
fancyvrb, and hyperref). There is no separate BibTeX step and no font download.
The final PDF supplied in this archive was compiled and visually inspected.

## Indexing warning

The raw modular gain is g_b = s_b - s_(b-1). Here s_0 is the genuine
nu_10(A-1), not a reset-to-zero convention. Some published examples use a
special displayed-digit convention at heights 1 and 2. The report proves
agreement of the relevant conventions for b >= 3 in the class used, and its
counterexample occurs at b = 2546. Do not shift the gain to s_(b+1)-s_b.
