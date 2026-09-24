# Term counts in the derivatives of power towers

**What this package is.** One article covering three OEIS sequences that ask the
same question about three different functions:

| Sequence | Function | The question |
|---|---|---|
| [A293239](https://oeis.org/A293239) | `x^x` | how many distinct monomials are in the fully collected `n`-th derivative? |
| [A290268](https://oeis.org/A290268) | `x^(x^2)` | the same |
| [A281434](https://oeis.org/A281434) | `x^(x^x)` | the same |

The three were written as separate reports and are merged here because they
share a setup, not because they share a result. **They reach three different
answers by three different recurrences**, and the article keeps all three
intact. What is proved once instead of three times is the common machinery:
the canonical differential-polynomial form, the uniqueness of that form, the
transition recurrence it obeys, and the reduction of "count the terms" to
"count the nonvanishing coefficients". That is Part I.

## Status of each headline question — read this first

**None of the three headline questions is fully settled here, and this package
does not pretend otherwise.** Two of the three OEIS entries print a conjectured
closed form, and neither is proved. The third prints no closed form; there the
growth *order* is settled and the constant is not — and the obstruction is a
different kind of statement, because further zeros provably exist and the open
question is only how many.

- **A293239 (`x^x`): the principal all-order closed formula is NOT proved.**
  Its precise missing nonvanishing statement is isolated. What *is* proved
  unconditionally: the term count reduces exactly to zeros of the first-kind
  Lehmer–Comtet triangle [A008296](https://oeis.org/A008296), giving
  `a(n) = 1 + n(n+1)/2 - Z(n)`; and `n + 1 + floor(n^2/4) <= a(n) <= q(n)`, so
  `a(n) = Theta(n^2)`. Separately, **the recurrence printed in the OEIS entry
  with the range `n > 6` is disproved at `n = 8`** (the recurrence gives 36,
  the true value is 35). For the proposed sequence `q` the recurrence holds for
  every `n >= 14` and fails at `n = 13`; asserting the corrected range for the
  actual derivative count remains conditional on the principal conjecture.

- **A290268 (`x^(x^2)`): the OEIS conjecture is NOT proved.** What is proved:
  the conjectured expression `U(n)` is an *upper* bound; every predicted
  cancellation is explained; positivity holds on a large coefficient region;
  there are no further zeros on the first two logarithmic-deficit diagonals;
  and `Lambda(n) <= a(n) <= U(n)` with `Lambda(n) = (3n^2+10n+8)/8` for even `n`
  and `(3n^2+12n+1)/8` for odd `n`, so `a(n) = Theta(n^2)`. The proposed
  leading constant `1/2` is not established.

- **A281434 (`x^(x^x)`): the growth order is settled; the constant is not.**
  For `n >= 1`, with `eps = 1` for odd `n` and `0` otherwise,

      (7n^3 + 39n^2 + 26n + 3*eps*(n-1))/24  <=  a(n)  <=  (2n^3 + 3n^2 + 4n)/3

  hence `a(n) = Theta(n^3)`. The sharper equivalent `a(n) ~ (2/3)n^3` is **not**
  proved; it would need the deficit from the upper polynomial to be `o(n^3)`.

Every finite computation in this package certifies a range. None of them is an
all-`n` proof, and each verifier says so in its own output.

## A warning about notation

The three parts keep the notation of their sources, which is *not* consistent
between them, because silently rewriting 2,600 lines of dense manipulation is a
worse risk than declaring the clash. Two collisions matter more than the rest:

- **`j` changes role.** In Parts II and III it is the exponent of `log x`. In
  Part IV it is the exponent of `x^-1`, and `l` is the logarithm exponent. Every
  envelope and every bound in Part IV is indexed the second way.
- **`z` has three meanings.** It is `x^2` in Part III and `log x` in Part IV — a
  direct contradiction — and in Part II it is neither, but the formal variable
  in which the Lehmer–Comtet numbers are defined.

§1.5 of the article gives the three canonical monomials side by side, which is
the form in which this is actually usable, and is explicit that many other
letters (`u`, `v`, `t`, `q`, `U`, `Z`, `E`, `Δ`) are reused across parts with
unrelated meanings. `a(n)` denotes a different sequence in each part.

## Building

    sh build.sh            # three pdflatex passes
    make pdf               # the same, via latexmk

## Verifying

Run from the package root. Each script is independent of the others.

    python code/verify.py --max-n 1500              # A293239, exact
    python code/verify_diagonals.py                 # A293239, offsets 1..16
    python code/verify_exact.py --max-n 200 --formula-n 16   # A290268, exact
    python code/test_a281434.py                     # A281434, 10 regression groups
    python code/run_experiments.py                  # A281434, data + benchmarks

Optional compiled verifiers, both exact rather than probabilistic:

    g++ -O3 -std=c++17 code/verify_gmp.cpp -lgmp -o verify_gmp      # A293239
    g++ -O3 -std=c++17 code/verify_modular.cpp -o verify_modular    # A290268

`make verify` runs the A290268 exact and modular passes and the certificate
combiner. **Note that several of these rewrite files in `data/`**: `make verify`
tees its run logs there, and `code/verify.py` rewrites `data/python_report.json`.
The shipped `data/` is the output of a full run, so re-running is reproduction,
not corruption — but the files will change.

## What the modular verifiers do and do not do

Both compiled verifiers are exact. A nonzero residue certifies a nonzero
coefficient outright. Every *zero* residue inside the proved support envelope is
checked again with an exact integer formula rather than being accepted. Neither
is a probabilistic zero test.

## Layout

- `article.pdf`, `article.tex` — the merged article and its source.
- `MERGE_EDITS.md` — every edit made to the three source texts during the
  merge, with a diff and a reason for each. Two of the eleven were not
  cosmetic.
- `code/` — verifiers, one group per sequence; see "Verifying" above.
- `data/` — retained outputs: term counts, zero classifications, modular witness
  lists, diagonal certificates, run logs, benchmarks, machine-readable summaries.
- `A293239_oeis_notes.txt` — a compact statement of the recurrence range
  correction for `x^x` and of which assertions are proved and which are not.
  Not an OEIS submission.
- `A290268_result_status.json` — machine-readable status for the `x^(x^2)`
  conjecture: what is proved, the certified finite range, and the exact
  remaining obligation.
- `CODE_LICENSE.txt` — license for the code (the A281434 group shipped it; it
  now covers the merged `code/` directory).
- `requirements-optional.txt` — optional NumPy acceleration for the A281434
  modular path; every exact path needs only the standard library.

## Provenance

Merged from three separately delivered archives:

| Part | Archive | Original article |
|---|---|---|
| II  | `A293239_research_report.zip` | 16 pages |
| III | `A290268_partial_results.zip` | 15 pages |
| IV  | `A281434_exact_algorithm_and_cubic_growth.zip` | 17 pages |

No theorem, lemma, proposition, corollary, definition, conjecture or remark
from any of the three was dropped in the merge — all fifty of them are present
with their statements unchanged, and `MERGE_EDITS.md` lists every edit that was
made to the surrounding text. Where a part's setup section is now subsumed by
Part I, the original statement is retained and cross-referenced rather than
deleted, so each part is still readable on its own.

These are AI-assisted drafts. None is refereed or machine-checked.
