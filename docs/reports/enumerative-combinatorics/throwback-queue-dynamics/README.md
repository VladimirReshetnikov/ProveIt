# Throwback Dynamics with Repeated Entries

**Recurrence classification, exact cycles, perfect mixing, and extremal periods**  
Research manuscript dated 19 September 2026.

## Main files

`throwback_research.pdf` is the 21-page article, including complete proofs,
source/status notes, exact examples, and computational verification tables.
`throwback_research.tex` is its self-contained LaTeX source.

This is a proposed mathematical resolution, not a claim of independently
established publication priority. The proofs have not been independently
refereed or checked in Lean. See `notes/source_status.md` for the literature
scope and `notes/proof_audit.md` for proof-critical distinctions.

## What is proved

An infinite queue has positive integer weights. At each move, remove its head
and reinsert it at the zero-based position equal to its weight. Tokens retain
their original labels even when weights repeat.

Every token recurs if and only if at most m input tokens have weight at most m,
for every positive integer m. If that condition fails, let J be the first
initial prefix endpoint that fails, and m the least overloaded threshold in
that prefix. The recurrent tokens are exactly the labels i <= J with x_i <= m.
Only labels 0 through J ever lead. No information after that prefix is needed.

The article also proves exact cycle periods and frequencies, a necessary and
sufficient coprimality test for perfect mixing, Catalan and prime-parking
counts for recurrent cores, and the largest labeled period of a core of size r:

    M_r = max(k ** (r-k+1) for k in range(2, r+1)).

This is OEIS A003320 evaluated at r+1. The sequence is known; the throwback
interpretation is what is established in the article. A Lambert-W asymptotic
and an exact example where individual limiting frequencies sum to less than
one are also included.

## Run an example

Python 3.10 or later is sufficient. There are no third-party Python dependencies.
From this directory:

```sh
python3 code/analyze.py 2 100 2 1 1 --simulate
```

The certificate has first bad index 3, threshold 2, and recurrent original labels
0, 2, 3, of weights 2, 2, 1. The labeled period is 4; the numerical period is 2.
Any positive continuation after the first four entries has exactly the same
leader word. Label 4, although also of weight 1, never leads.

An admissible finite prefix is reported accurately:

```sh
python3 code/analyze.py 2 2 3 4 5
```

It is **not** a certificate about an unspecified infinite tail. A streaming
search on an infinite admissible input does not terminate.

## Reproduce the checks

```sh
python3 code/verify.py
python3 code/extra_results.py
```

The default checks were actually run and passed:

* All 296,675 closed labeled input words in {1,...,n-1}^n for 2 <= n <= 7.
* All 303,245 bounded configurations for 571 admissible sorted profiles with
  at most five tokens and weights at most seven; 10,308 complete cycles.
* 5,470 waiting-or-barrier cases, 1,500 seeded sparse/static comparisons, and
  200 exact finite-horizon comparisons.
* All 290,511 critical profiles of sizes 2 through 13 for the extremal-period
  check, plus exact worked examples and a rational product bound.

`verify.py` also accepts `--max-n`, `--max-value`, `--max-r`, and `--output`.
Increasing the exhaustive bounds can greatly increase the runtime. The reported
wall-clock runtime is environment-dependent; all mathematical output is
deterministic. The stored JSON/CSV files are the outputs of the executed runs.

## API overview

In `code/throwback.py`:

- `first_obstruction(iterable)` returns an `Obstruction`, or `None` when a finite
  inspected input is admissible. It uses sparse backward parking and an interval
  disjoint-set structure; it does not allocate up to the largest weight.
- `Obstruction.verify()` independently checks the certificate by sorted-prefix
  inequalities, rather than replaying parking.
- `sorted_statistics(weights, closed=False)` computes exact rational per-token
  frequencies, the least labeled period, configuration and cycle counts, and
  the perfect-mixing test. Open mode requires an admissible selected multiset;
  closed mode requires a critical recurrent core.
- `finite_orbit(weights)` simulates an actually closed finite queue. Every weight
  must be less than its length. Labels, not equal weight values, form states.
- `certified_orbit(certificate, max_steps=...)` simulates the complete infinite
  input leader word using only the certificate's prefix-token positions. A
  resource cap can stop enumeration without affecting certificate validity.
- `finite_horizon(weights, steps, window)` computes an exact bounded horizon
  from at least `steps+window` known input values. Out-of-range throws are not
  incorrectly appended.
- `maximum_core_period(r)` evaluates the exact extremal formula with integers.

Repeated weights have equal individual frequencies, but merging labels can
shorten a period. Numerical periods can depend on which labeled cycle is used.
Do not reinterpret a labeled period as automatically the least numerical one.

## Build the article

A normal TeX Live or MiKTeX installation with the standard packages used in the
preamble is sufficient. No custom font files are distributed or required.

```sh
pdflatex -interaction=nonstopmode -halt-on-error throwback_research.tex
pdflatex -interaction=nonstopmode -halt-on-error throwback_research.tex
```

Or use `latexmk -pdf throwback_research.tex`. The delivered PDF was compiled,
rendered with Poppler, and visually checked. The final compilation had no
undefined references or overfull-box warnings.

## Artifact scope

The archive contains original source, code, data, and notes only; third-party
papers and font files are not bundled. It contains no checksum files. No OEIS
submission, publication, repository modification, or email to the source-paper
authors has been made.
