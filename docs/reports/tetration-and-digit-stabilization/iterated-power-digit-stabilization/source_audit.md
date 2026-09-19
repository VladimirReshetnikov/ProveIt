# Source and claim audit

Research check date: 19 September 2026.

## Selected open question

Marco Ripà, “Stabilization of one new trailing digit of a^(10^b) as b increases,
for every a not divisible by 10,” Mathematics Stack Exchange, question 5103929.
Posted 24 October 2025.

https://math.stackexchange.com/questions/5103929/stabilization-of-one-new-trailing-digit-of-a10b-as-b-increases-for-ever

The retrieved page defines S_a(b) and D_a(b) exactly as used in the article,
asks for a universal threshold b >= 3, and displayed zero answers. The page
connects the question to earlier work on integer-tetration congruence speed.
It already reports a base-dependent sufficient onset bound; pointwise eventual
unit speed is not claimed here as a new result.
A targeted search did not locate a resolution of this exact question. This
is a limited source check, not a guarantee against unindexed or unpublished
prior work. The page's relative “months ago” strings were not used to infer
its posting date; the absolute date shown in the source was used.

## Primary research background

1. Marco Ripà, *The congruence speed formula*, Notes on Number Theory and
   Discrete Mathematics 27(4) (2021), 43–61.
   https://nntdm.net/volume-27-2021/number-4/43-61/
   https://arxiv.org/abs/2208.02622

2. Marco Ripà and Luca Onnis, *Number of stable digits of any integer tetration*,
   Notes on Number Theory and Discrete Mathematics 28(3) (2022), 441–457.
   https://nntdm.net/volume-28-2022/number-3/441-457/
   https://arxiv.org/html/2210.07956v1

3. Marco Ripà, *Graham's number stable digits: An exact solution*, Notes on
   Number Theory and Discrete Mathematics 31(3) (2025), 607–616.
   https://arxiv.org/abs/2411.00015
   https://arxiv.org/pdf/2411.00015
   Version 2, 12 September 2025. The PDF was inspected, including rendered pages.

These sources establish context for genuine integer towers. The article does
not treat their existence as a proof of the separate exponent-schedule problem.
Its needed lifting identities and all announced results are proved directly.
The base-3 tower formula is explicitly identified as known, not as a new result.

## Initial topic orientation

The four Wikipedia pages supplied in the request were opened for orientation:
Tetration, Knuth's up-arrow notation, Conway chained arrow notation, and
Fast-growing hierarchy. They are not used as substitutes for primary sources
on the status of the selected conjecture.

## What the package establishes

- A counterexample to the exact publicly posed universal threshold.
- A proof that 3*2^99+1 is the smallest counterexample.
- Exact formulas for all decimal bases and the permanent-unit-speed onset.
- Explicit arbitrarily delayed examples.
- Exact least exceptional bases at every stage and a natural-density formula.
- Exact agreement with all later terms and with the decimal limit.
- A time-change identity for arbitrary increasing integer schedules.
- An arbitrary-radix valuation formula, convergence/limit-cycle criterion,
  and prime-power-versus-mixed-radix uniformity theorem.

These are deductions proved in the report. It does not claim that every
general auxiliary theorem is historically new. In particular, prime-adic
lifting, CRT, elementary order theory, and the base-3 tower result are prior
mathematics.

## What is not claimed

The result is not a resolution of analytic tetration interpolation, a
transcendence theorem for power towers, a result about arbitrary ordinal
notations, or a new calculation of Graham's number. The selected sequence
has recurrence X_(b+1) = X_b^10 rather than T_(b+1) = a^T_b.
No external site was posted to or edited. No proof-assistant kernel was run.
The included source is a research note with ordinary proofs and exact tests,
not a claim of independent peer review.
