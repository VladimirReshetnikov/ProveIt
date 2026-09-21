# Sources and provenance

Research date: September 20, 2026.

## The actual target

**OEIS A267220** — https://oeis.org/A267220

The Formula section contains two assertions by Peter Bala dated
October 17, 2024. They define u_m(n)=[x^n]A(x)^(m*n) and
v_m(n)=[x^n]F(x)^(m*n), with F(x)=x/Rev(x*A(x)), and assert the respective
congruences between indices n*p^r and n*p^(r-1) modulo p^(2*r), for
all integer m, all primes p>=5, and positive integers n,r.
Both assertions were explicitly labeled conjectural when checked.

These are NOT the older exponential-integrality comment in the same
entry, which already has a 2020 attribution to Beukers. The article does
not present that older comment as a newly unresolved question.
A current conjectural label is evidence of the entry's wording, not a
proof of global historical priority. No edit or submission to OEIS was
performed.

**OEIS A005259** — https://oeis.org/A005259

This is the classical Apéry sequence used as input. The defining
binomial sum and the three-term recurrence used as a numerical
cross-check are recorded there. The article derives its required
second-order congruence directly from the binomial definition rather
than importing an external Apéry supercongruence theorem.

## The established framing principle

**Albert Schwarz, Vadim Vologodsky, Johannes Walcher (2013)**,
*Framing the Di-Logarithm (over Z)*, arXiv:1306.4298.
https://arxiv.org/abs/1306.4298

General framing integrality for rational-coefficient 2-functions is prior
work. Its relation to integral dilogarithm expansions explains the
preservation mechanism used here.

**Albert Schwarz, Vadim Vologodsky, Johannes Walcher (2017)**,
*Integrality of Framing and Geometric Origin of 2-functions (with
algebraic coefficients)*, arXiv:1702.07135v2.
https://arxiv.org/abs/1702.07135

Theorem 8 and Section 3 develop the general preservation theorem and a
local coefficient proof. This article gives the coefficient argument
explicitly in the normalization b_m(n)=u_m(n)/m for m!=0, with an
integral definition valid at m=0 and at primes dividing m. The connection
to the second OEIS family is v_m(n)=m*b_(m-1)(n). The known general
mechanism must not be represented as a newly invented theorem.

**L. Felipe Müller (2021)**,
*Wolstenholme Type Congruences and Framing of Rational 2-Functions*,
arXiv:2104.10754.
https://arxiv.org/abs/2104.10754

Background on more specialized higher-order congruences under framing.
No higher-order theorem from this work is used to infer a third-order
Apéry-transform congruence. The note explicitly exhibits a counterexample
to a uniform third-order strengthening.

## Apéry arithmetic background

**Ji-Cai Liu (2024)**,
*An extension of Gauss congruences for Apéry numbers*, arXiv:2404.16636v1,
25 April 2024.
https://arxiv.org/abs/2404.16636

The introduction records the standard recurrence, the binomial-sum
definition, the connection with Apéry's irrationality proof, and the
historical order-three results of Gessel and Coster. Those stronger
congruences provide context, not an unproved dependency of the present
argument: the required order-two seed statement is proved directly in
section 3 of the article.

## What was independently checked

The mathematical proof in article.tex is written out in full, including
its formal Lagrange inversion lemma, the Apéry input congruence, the
constant-term calculation, and all three dyadic cases.
The included Python code performs exact integer checks, including direct
low-degree polynomial powers and both compositional inverse identities.
Its scope and actual tested values are recorded in verification/.
The code was executed in the working container, not through a remote
proof assistant or a Wolfram service. No formal proof-assistant
verification is claimed.

No full third-party paper or web page is redistributed in this archive.
The mathematical source is original exposition with the prior mechanism
attributed above; the external sources are linked rather than bundled.

The theorem proved in the article implies the two formulas currently
labeled conjectures in the selected entry. This is a proof of those
claims, but the source review is not an exhaustive priority
investigation. The article and its computational artifacts are unrefereed
and not proof-assistant verified. No third-party source text or full paper
is redistributed in this archive.

## Provenance of this package

This directory is the merge of two independently produced research
archives on the same two OEIS A267220 conjectures:

- `a267220-apery-transform-supercongruences` (the base of the merge):
  the constant-term / integration-by-parts proof, the signed all-prime
  Gauss-congruence theorem for (-1)^(m*n)*b_m(n), the first-dyadic-descent
  sum identity, the sharper 2-adic bounds, the framing group law, the
  signed framed dilogarithm expansion and Euler product, and the
  verification run to index 250.
- `a267220-exponentiation-and-reversion` (folded in, then removed):
  the explicit Frobenius-defect identity with its logarithmic-error lemma
  and logarithmic Taylor identity, the binomial-moment seed family, the
  dependency-and-boundary audit now in Appendix B, the additional exact
  data (c_6, b_m(4), the partition formula, u_1(7) and the residues
  294 and 245 mod 343), the Liu citation, and the second verification
  program with its 18 symbolic checks of the defect identity.

Both archives targeted the same conjectures and shared the same seed
lemma, dilogarithm criterion, Lagrange inversion appendix, parameter-shift
proposition, framed potential, and counterexamples; those shared results
are proved once, using the base's proof. Where the two differed on the
2-adic bounds, the sharper bound is the proved one from the constant-term
route, and the weaker bound that the defect route alone yields is recorded
as such in Remark 8.4 rather than asserted as the result.
