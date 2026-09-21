# Two Apéry-transform supercongruences in OEIS A267220

Research note prepared for Vladimir Reshetnikov, September 20, 2026.

## Provenance

This package is the merge of two independently produced archives that
targeted the same pair of OEIS A267220 conjectures:

- **`a267220-apery-transform-supercongruences`** — the base. Constant-term
  (integration-by-parts) proof of the framing step, the signed all-prime
  Gauss-congruence theorem, the sharper 2-adic bounds, the framing group
  law, the signed framed dilogarithm expansion, the verification run to
  index 250.
- **`a267220-exponentiation-and-reversion`** — folded in and then removed.
  The explicit Frobenius-defect identity with its logarithmic-error lemma,
  the binomial-moment seed family, the dependency-and-boundary audit, extra
  exact data, the Liu citation, and a second verification program.

The two shared the seed lemma, the dilogarithm/Euler-product criterion, the
Lagrange inversion appendix, the parameter-shift proposition, the framed
potential and the counterexamples. Those are proved once here, in the base's
form. Where the two archives disagreed on a 2-adic exponent, the sharper
proved bound from the constant-term route is the asserted one, and the
weaker bound that the defect route alone yields is recorded as exactly that
(Remark 8.4), not suppressed.

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

The framing step is proved **twice, independently**:

1. Sections 5–7: a constant-term (Laurent-residue) computation in the
   original coordinate, index by index. Its engine is constant-term
   integration by parts, which recovers the second power of the index in
   the linear term. This is the route that reaches the delicate dyadic sign
   analysis, hence the signed all-prime theorem and the sharper 2-adic
   bounds.
2. Section 8.3: one exact Frobenius-defect identity in the framed
   coordinate, which yields integrality of the normalized family and the
   congruence together by induction on the valuation, is symbolically
   checkable as a formal identity, and transfers transparently to other
   seeds.

Section 9 exhibits an infinite family of such seeds: every even binomial
moment sum_k (C(n,k) C(n+k,k))^(2h), h >= 1, is order-two admissible, so
the whole theorem holds with that seed in place of the Apéry numbers.
Appendix B is a dependency-and-boundary audit naming the specific traps
(compositional versus multiplicative inverse, the sign of the quadratic
correction, x^p versus x_p, never dividing by m or m-1 modulo p, and the
modulus keyed to the full valuation of N).

The underlying framing-integrality principle is established work of
Albert Schwarz, Vadim Vologodsky, and Johannes Walcher (2013 and 2017).
This note supplies self-contained coefficient proofs adapted to these
OEIS formulas, not a claim of priority for the general principle.
The OEIS assertions were checked as still labeled conjectural on the
stated research date. No OEIS edit has been submitted. This is an
unrefereed research exposition; no proof-assistant verification or OEIS
submission is claimed. Nor does an entry's conjectural label establish
that no proof exists elsewhere.

The older exponential-integrality comment in the same entry, with its 2020
attribution to Beukers, is NOT one of the two targeted conjectures and is
not presented here as an open problem.

## Files

- `article.pdf`: complete 22-page mathematical article.
- `article.tex`: standalone LaTeX source; bibliography is embedded.
- `verify_constant_term_route.py`: exact-integer verification program for the
  constant-term proof, Python 3.9+, no dependencies.
- `verify_defect_route.py`: exact integer/rational verification program for
  the defect-identity proof, Python 3.10+, no dependencies.
- `verification/verification.json`: machine-readable results of the first run.
- `verification/verification.log`: human-readable record of the first run.
- `verification/sample_values.csv`: initial values for the input and transforms.
- `verification-defect-route/verification_summary.json`: counts and exact
  counterexamples from the second run.
- `verification-defect-route/validation_log.txt`: saved output of the second run.
- `verification-defect-route/odd_prime_checks.csv`: 798 normalized checks with
  actual valuations and scaled differences.
- `verification-defect-route/sample_coefficients.csv`: Apéry numbers and related
  coefficients at indices 1 through 20.
- `sources.md`: primary sources, scope, attribution, and merge provenance.
- `suggested_OEIS_update.txt`: a proposed update and proof outline, not submitted.

The two verification programs are **not** merged into one. They compute the
same quantities by different routes on different grids, and that independence
is the point of keeping both.

## Reproduce the checks

From this directory:

```text
python verify_constant_term_route.py --max-index 250 --output-dir verification
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

For a larger run (not included in the archived results), use this single
line, which is also suitable for PowerShell:

```text
python verify_constant_term_route.py --max-index 500 --parameter-radius 8 --multipliers 8 --primes 2 3 5 7 11 13 17 --output-dir verification-500
```

Then, for the second, independent program:

```text
python verify_defect_route.py --out verification-defect-route --limit 150
```

Run it normally, not with Python's `-O` option; it refuses to run with its
verification assertions disabled. That run passed 7,767 exact checks: 151
binomial-sum-versus-recurrence comparisons, 269 seed congruences, 798
normalized odd-prime congruences, 1,575 normalized two-adic bounds, 840
parameter-sensitive odd-prime bounds for the exponential family, 1,575
parameter-sensitive two-adic bounds for that family, 2,415 bounds for the
reverted family including the prime 2, 126 independent
reversion-and-power identities, and 18 full Frobenius-defect identities
through degree 14. The exact grids are documented in section 11 of the
article and in the code; this does not mean every possible integer
parameter or prime below every bound was tested.

The 2-adic bounds exercised by `verify_defect_route.py` are the ones its own
proof yields, namely 2*valuation_2(N)-1 for odd framing parameters. The
sharper bounds asserted by the article are exercised by
`verify_constant_term_route.py`.

The two counts, 8,142 and 7,767, are different finite samples and are not
comparable totals. The first reaches higher indices; the second reaches
wider parameters and is the only one that checks the central identity
symbolically.

Every purported exact division is checked for zero remainder.
No floating-point arithmetic is used. Both programs compute the input
sequence twice, once from the defining binomial sum and once from the
classical Apéry three-term recurrence, and compare.
Finite computations supplement the proofs; they do not replace them.

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

## Three useful boundaries

1. u_1(2)-u_1(1)=118 is not divisible by 4. The first unsigned family
   cannot unconditionally be extended to the prime 2. The signed sum
   u_1(2)+u_1(1)=128 is divisible by 4, exactly as the first-descent proof
   predicts.
2. u_1(7)=5082313276, so u_1(7)-u_1(1)=49*103720679, where 103720679 is 6
   modulo 7; the difference is 294 modulo 343. Its valuation at 7 is
   exactly 2, so a universal third-order replacement is false.
   Since v_2(n)=2*u_1(n) for n>=1, v_2(7)-v_2(1)=10164626542 is 245 modulo
   343, and the same obstruction applies to the second family.
3. v_2(2)-v_2(1)=236 is divisible by 4 but not 8, showing why the unsigned
   parameter refinement has a first-dyadic-descent exception.

These are counterexamples to stronger variants, not to either formula
actually listed in OEIS.
