# Small-prime congruences for OEIS A348410

**Article:** `article.pdf` (33 pages), with editable source `article.tex`.
**Date:** 19 September 2026.

This report is a merge of two independently produced research reports on
A348410: `a348410-small-prime-congruences` (the binary completion, the
denominator theorem, the Mobius and asymptotic material, the source audit)
and `a348410-cubic-supercongruence` (the odd-prime prime-power tower, its
consequences for related families, an audit of a broader printed framing
claim). The shared odd-prime theorem was proved by the same argument in both
and is proved once here. Where the two proved the same statement by
genuinely different routes, both routes are kept and labelled.

## Main results

For integer parameters,

    A_{alpha,beta}(n) = [x^n] (1-x)^(-alpha*n) (1+x)^(-beta*n),
    a(n) = A_{2,1}(n) = [x^n] ((1-x)(1-x^2))^(-n)   (OEIS A348410).

1. **Odd-prime cubic tower** (Theorem 1.2). For every odd prime p and every
   N > 0 divisible by p,

       v_p(A_{alpha,beta}(N) - A_{alpha,beta}(N/p)) >= 3*v_p(N) - eps_p,
       eps_3 = 1,  eps_p = 0 for p >= 5.

   Equivalently, with no coprimality restriction on the multiplier,
   `A(m*p^k) == A(m*p^(k-1)) mod p^(3*(k+v_p(m)) - eps_p)` (Corollary 1.3).
   Specializing to (alpha,beta)=(2,1) and p>=5 gives Bala's 2022 OEIS
   conjecture; at p=3 it gives modulus 3^(3r-1).

2. **First binary defect** (Theorem 1.4). For odd m and r >= 2,

       A(m*2^r) - A(m*2^(r-1))
         == 2^(3*r-3) * alpha*beta * binomial((alpha+beta+1)*m-1, m-1)
            modulo 2^(3*r-2).

   Generalized binomial coefficients are used for negative upper arguments.
   This gives a sharp universal binary modulus 2^(3r-3), improved by one bit
   when alpha*beta is even. If both parameters are odd and m=1, the valuation
   is exactly 3r-3 at every r >= 2.

3. **All primes for the basket sequence** (Theorem 1.5):
   `v_p(a(m*p^r) - a(m*p^(r-1))) >= 3*r - v_p(12)`, each uniform loss
   necessary.

4. **Sharp common denominators** (Theorem 1.6). `24*B_{alpha,beta}(n)` is an
   integer always, and `12*B_{alpha,beta}(n)` when alpha*beta is even, where
   `B(n) = n^(-3) * sum_{d|n} mu(d) A(n/d)`. In particular

       (12/n^3) * sum_{d|n} mu(d) * a(n/d)

   is a nonnegative integer for every n >= 1, and 12 is minimal: the unscaled
   transform is 2/3 at n=3, 5/4 at n=4, and 126385/12 at n=12.

5. **Primitive-orbit divisibility** (Corollary 1.7):
   `n^2/gcd(n^2,12)` divides the primitive cyclic-word count `P_n = n^2 B(n)`.

6. **Limits along a tower, change of step, and related families**
   (Sections 3.5-3.6): a p-adic limit with an explicit error estimate, the
   same bound for `[x^n](1-x^d)^(-alpha n)(1+x^d)^(-beta n)` at odd p not
   dividing d, and the reparametrized basket family
   `A_{sigma+tau,tau}(n) = [x^n](1-x)^(-sigma n)(1-x^2)^(-tau n)`.

7. **The exact hypothesis, and its failure** (Remark 3.7, Section 7). The
   logarithmic method needs `c_{pj}=c_j` PLUS a quadratic coefficient
   estimate; the second is not implied by the first. An infinite period-three
   family `b_t(n) = [x^n](1-x)^(-tn)(1-x^3)^(-tn)` satisfies the first and
   fails the conclusion at p=5, with exact valuation 2 for every t not
   divisible by 5.

8. **Framing audit** (Section 7.3 and Appendix C). Two independent inputs
   refute the explicit printed conclusions of arXiv:2104.10754v1,
   Theorems 1.1 and 1.2/6.2, at p=5. See below for the scope.

## Where two proofs are kept

- **Lemma 3.3 (reduced reciprocal squares), case p=3.** Proof: lifting
  induction `U_t == 3*U_{t-1} mod 3^(t-1)`. Remark 3.4 gives a second,
  uniform proof by the doubling automorphism `a -> 2a`, from which
  `3*U_t == 0 mod p^t` and the loss `v_p(3) = eps_p` at p=3 is visible as the
  valuation of a single constant, with no case split at all.
- **The period-three obstruction (Section 7.2).** First witness: the
  first-level residue formula (7.1), giving weighted sum 361/144 == 4 mod 5.
  Second witness: the quadratic coefficient itself, `11/6` not 0 mod 5,
  which is the precise quantity the proof consumes and needs no appeal to the
  residue formula.
- **The framing audit (Section 7.3 and Appendix C).** First input:
  `V_1(x) = x/(1-x) + 3x^3/(1-x^3)` over `Q(sqrt(-3))`, harmonic sum 361/144.
  Second input: `V_3(x) = 3x/(1-x) + 9x^3/(1-x^3)` over `Q`, harmonic sum
  361/16, whose rational 2-function condition is proved at EVERY prime
  including 3, with no ramified exception and no field extension.
  361/144 and 361/16 are for DIFFERENT inputs; neither is a typo for the
  other, and their residues mod 5 differ (4 against 1).
- **Generating-function certificates.** `verify.py` checks them to degree 60
  in integer arithmetic with the standard library only; `symbolic_checks.py`
  checks them independently with SymPy.
- **Four evaluation mechanisms for a(n).** The coefficient recurrence, the
  positive binomial sum, the signed binomial sum, and repeated basket
  convolution.

## Source and priority boundary

The initial target was Bala's 2022 OEIS-listed odd-prime conjecture. A
source audit found a prior public proof candidate for it and for its full
integer-parameter odd-prime extension. This archive does NOT claim a new
resolution or priority for that result; it is presented as a first-class
theorem of the article with a complete proof, because the binary completion
depends on it and should not rest on an external unreviewed argument. The
prior source is explicitly credited and pinned in the bibliography and in
`source_audit.md`.

The prior note expressly did not assert a binary result. The binary defect
formula and denominator-12 completion were not found in the checked sources.
The literature search is not exhaustive and does not establish global
priority. That a problem exists in the general printed framing statement is
also not claimed as new: a period-four counterexample is already documented
in the same repository, and the period-three witnesses here are compact
independent evidence. The criticism is limited to the explicit printed
conclusions of the inspected version 1; a single exceptional prime does not
refute a weaker statement allowing an unspecified finite exceptional set or
a compensating scalar.

The written proofs are intended to be complete but have not undergone
external peer review or Lean formalization. No OEIS edit, no database
submission, and no communication with an author has been performed.

The stronger experimental identity
`v_2(a(2^r)-a(2^(r-1))) = 3r+1` for r>=4 is a CONJECTURE here, not a theorem.
It is checked only through r=15 and is not used in any proof.

## Reproduce the exact tests

Python 3.10 or later is recommended. The two exact scripts need only the
standard library and perform no network operations. No floating-point
arithmetic occurs in any congruence check.

```sh
python verify.py
python binary_checks.py
```

The first script allows coverage options:

```sh
python verify.py --max-n 5000 --prime-limit 97 --multipliers 12
python verify.py --max-n 20000
python verify.py --help
```

In PowerShell the path may also be written `python .\verify.py`.

The recorded run used Python 3.13.5 with the default `--max-n 5000`. It
performed 26 initial-value checks against the inspected OEIS listing; 208
positive-binomial and 13 basket-convolution cross-checks; 1,519 signed
parameter cross-checks; 489 original-sequence and 3,675 two-parameter
prime-power congruence tests in the STRONG form (multipliers divisible by p
are not skipped); 918 quadratic-tail tests; 3,415 logarithmic-derivative
coefficient bounds; 119,760 factorial inequalities for the exponential tail;
61 generating-function coefficients in integer arithmetic; 300 Mobius/orbit
checks and 100 cubic-transform denominator checks; 7 exact boundary
witnesses and 3 period-three family members; and 10,000 rational 2-function
input checks backing Appendix C. The largest original-sequence index reached
was 5,000.

The binary script includes 5,808 checks of the complete leading-defect
formula; 1,936 first-lift checks; 400 exact harmonic-unit checks; 1,000
target denominator/orbit checks; 4,900 general denominator checks; and
290 sharpness/minimal-denominator checks. Its final 78-row exploratory
table is explicitly not a proof of the finer conjecture.

## Optional symbolic and asymptotic checks

```sh
python -m pip install -r requirements-optional.txt
python symbolic_checks.py
```

These check the generating-function elimination (both that the resultant
equals the displayed quartic and that the quotient of the resultant by it is
a nonzero constant, recorded as 1), the grouped form of the quartic, the
three parity-weight identities used in Lemma 3.5, the formal series, the
saddle constants, the Gaussian/Bell formulas for two correction coefficients,
and 90-digit asymptotic comparisons. The symbolic identities are exact; the
comparison table alone uses approximate decimal arithmetic.

## Build the article

Use a normal TeX Live or MiKTeX installation with the packages named in the
preamble. The PDF was built with pdfLaTeX and latexmk. The bibliography is
inline, so BibTeX is NOT required; `bibliography.bib` is supplied only for
reuse and citation managers.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, `make pdf` builds it, `make exact` reruns the exact checks,
and `make symbolic` runs the optional symbolic checks.

## Files

- `article.tex`, `article.pdf`: complete article, proofs and bibliography.
- `bibliography.bib`: the same reference metadata in BibTeX form, for reuse.
  Not needed to build the PDF.
- `verify.py`: exact evaluator; four independent evaluation mechanisms;
  odd-prime tests in strong form; direct tests of the logarithmic-derivative,
  exponential-truncation and quadratic-tail lemmas; integer-arithmetic
  generating-function certificates; Mobius denominators; both period-three
  boundary witnesses and the rational 2-function input checks for Appendix C.
- `binary_checks.py`: binary formula and universal denominator tests.
- `symbolic_checks.py`: optional SymPy/mpmath checks.
- `verification_report.json/.txt`, `binary_report.json/.txt`,
  `symbolic_report.txt`: results of the recorded runs.
- `Makefile`: `pdf`, `exact`, `symbolic`, `check`, `clean` targets.
- `requirements-optional.txt`: pinned versions for the optional checks only.
- `data/terms.csv`: a(n) through n=1000.
- `data/supercongruence_checks.csv`: odd-prime valuation checks, strong form.
- `data/binary_defect_checks.csv`: the full exact binary parameter grid.
- `data/denominator12.csv`: **not distributed** (1.0 MB); `python binary_checks.py`
  rebuilds it. Primitive orbits, B(n), 12B(n), and the proved
  orbit divisibility factor through n=1000.
- `data/mobius_invariants.csv`: earlier odd-prime-only orbit checks;
  the stronger completed bound is in `denominator12.csv`.
- `data/binary_valuations.csv`: proved lower bounds beside exploratory
  actual binary valuations, including powers of two through 32768.
- `data/period_three_counterexamples.csv`: the family b_t(1), b_t(5), their
  difference and its residue mod 125, for t = 1, 3, 9.
- `data/asymptotic_checks.csv`: numerical comparisons at 90-digit precision.
- `source_audit.md`: source URLs, provenance, and priority limitations.
- `oeis_comment_draft.txt`: possible mathematical comments, NOT posted.

All assertion failures raise exceptions. Exact computations use integers
and reduced rational numbers, not floating-point approximations.

## Research status

Complete proofs are presented, but nothing here has been refereed or checked
by a proof assistant. The computations are checks, not a substitute for the
universal statements, which are established by the lemmas and theorems. No
OEIS edit, no submission, and no author contact was performed. The claim
about open status is specifically that the OEIS entry still displayed Bala's
supercongruence as a conjecture on the inspection date; exhaustive historical
priority is not established.
