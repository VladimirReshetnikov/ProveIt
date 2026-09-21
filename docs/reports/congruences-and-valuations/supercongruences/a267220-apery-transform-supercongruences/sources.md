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
