# Two Apéry-transform supercongruences in OEIS A267220

Research note prepared for Vladimir Reshetnikov, September 20, 2026.

## Result

Both Peter Bala conjectures dated October 17, 2024 in OEIS A267220 are
proved for all integer parameters, including negative and zero values.
The proof is in `article.pdf`; its editable source is `article.tex`.

Let a_n be the classical Apéry numbers, and set

    A(x) = exp(sum_{n>=1} a_n x^n/n),
    F(x) = x / Rev(x A(x)),
    u_m(n) = [x^n] A(x)^(m n),
    v_m(n) = [x^n] F(x)^(m n).

For every odd prime p, nonzero integer m, and positive N divisible by p,
put R = valuation_p(N). Then both differences at N and N/p are divisible by

    p^(2 R + valuation_p(m)).

The unsigned v_m congruence modulo p^(2 R) holds for EVERY prime,
including 2. The u_m congruence at 2 needs a sign correction when m is odd
and R = 1. The article gives the exact all-prime signed refinements.
For m=0 the positive-index terms vanish; at n=0, u_m(0)=v_m(0)=1.

The underlying framing-integrality principle is established work of
Albert Schwarz, Vadim Vologodsky, and Johannes Walcher (2013 and 2017).
This note supplies a self-contained coefficient proof adapted to these
OEIS formulas, not a claim of priority for the general principle.
The OEIS assertions were checked as still labeled conjectural on the
stated research date. No OEIS edit has been submitted.

## Files

- `article.pdf`: complete 16-page mathematical article.
- `article.tex`: standalone LaTeX source; bibliography is embedded.
- `verify.py`: exact-integer verification program, Python 3.9+, no dependencies.
- `verification/verification.json`: machine-readable results and every tested pair.
- `verification/verification.log`: human-readable verification record.
- `verification/sample_values.csv`: initial values for the input and transforms.
- `sources.md`: primary sources, scope, and attribution notes.
- `suggested_OEIS_update.txt`: a proposed update and proof outline, not submitted.

## Reproduce the checks

From this directory, run:

```text
python verify.py --max-index 250 --output-dir verification
```

The included run passed 8,142 exact checks. It used original parameters
-6 through 6; normalized parameters -7 through 6; primes 2, 3, 5, 7, 11,
and 13; and indices N=h*p^r <= 250 with 1 <= h <= 6 and r >= 1.
Duplicates were removed, giving 71 prime/index pairs.
The input Apéry congruences were tested at every prime divisor of every
positive N <= 250, not only at the six selected transformed-test primes.
Low-degree direct power and reversion tests use degrees through 12.
The transformed tests are a specified finite sample, not an exhaustive
search over all indices and parameters in a box.

Every purported exact division is checked for zero remainder.
No floating-point arithmetic is used. The script's proof-independent
input computation is the defining binomial sum; the classical Apéry
three-term recurrence is an additional cross-check.
Finite computations supplement the proof; they do not replace it.

For a larger run (not included in the archived results), use this single
line, which is also suitable for PowerShell:

```text
python verify.py --max-index 500 --parameter-radius 8 --multipliers 8 --primes 2 3 5 7 11 13 17 --output-dir verification-500
```

The JSON `elapsed_seconds` and `python` fields may differ across machines.
All integer values, check counts, and tested pairs are deterministic for
the same command arguments.

## Build the PDF

With a LaTeX distribution providing the standard packages used by the
source:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, run the following command twice:

```text
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The bibliography is in the source; no BibTeX invocation, network access,
external illustration, or special font installation is required.
The delivered PDF was compiled with pdfLaTeX and visually checked after
rendering. It is not a proof-assistant certificate.

## Two useful boundaries

1. u_1(2)-u_1(1)=118 is not divisible by 4. The first unsigned family
   cannot unconditionally be extended to the prime 2.
2. u_1(7)-u_1(1)=49*103720679, where 103720679 is 6 modulo 7. Its valuation
   at 7 is exactly 2, so a universal third-order replacement is false.
   Since v_2(n)=2*u_1(n) for n>=1, the same obstruction applies to the
   second family.

In addition, v_2(2)-v_2(1)=236 is divisible by 4 but not 8, showing why
its unsigned parameter refinement has a first-dyadic-descent exception.
