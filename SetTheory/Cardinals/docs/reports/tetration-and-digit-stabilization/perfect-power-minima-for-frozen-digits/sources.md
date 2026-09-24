# Sources and research-status record

Checked on 19 September 2026. This is a provenance record, not a claim that every
publication, preprint, or unpublished discussion has been searched.

## 1. The precise target problem

Marco Ripa (question) and Max Alekseyev (answer), **Closed form for the general
term of 2, 49, 15625, 625, ...**, MathOverflow question 487698.

https://mathoverflow.net/questions/487698/closed-form-for-the-general-term-of-2-49-15625-625-dotsc

The question was posted 12 February 2025; the answer was posted 14 February 2025
and updated that day. The page inspected contains the problem definition,
the decimal-speed case formula, the first ten full sequence terms, an answer
listing the first 50 minimizing roots, and the conjectural assertion that the
minimum is always in the final-digit-5 case for n >= 3. It also contains the
two-tail conjecture and a comment asking for the exact maximal-degree variant.

The inspected answer supplies a computational pattern and a heuristic, not an
all-n global minimality proof. The report gives a deterministic proof for the
precisely defined extremal sequence and treats the strict-degree variant
separately. No claim is made that nobody could have proved the result elsewhere.

Alekseyev's 50 root values are independently reproduced by the formula and
compared in `code/verify.py`. Ripa's speed formula is independently transcribed
there as a cross-check. The proofs in the article do not rely on a probability
model for p-adic digits or on the correctness of an empirical extrapolation.

## 2. Foundational congruence-speed work

Marco Ripa, **On the constant congruence speed of tetration**, Notes on Number
Theory and Discrete Mathematics 26 (2020), no. 3, 245-260.

https://nntdm.net/volume-26-2020/number-3/245-260/
https://doi.org/10.7546/nntdm.2020.26.3.245-260

Marco Ripa, **The congruence speed formula**, Notes on Number Theory and
Discrete Mathematics 27 (2021), no. 4, 43-61.

https://nntdm.net/volume-27-2021/number-4/43-61/
https://doi.org/10.7546/nntdm.2021.27.4.43-61
https://arxiv.org/abs/2208.02622

The 2021 paper establishes the decimal speed formula and solves the different
problem of the smallest unrestricted base of a specified speed. It must not be
confused with the later problem imposing an nth-perfect-power constraint. Its
arXiv deposition date is 2022, not the date of the journal publication.
The report rederives the speed formula directly from differences of consecutive
towers and elementary valuation lifting.

## 3. Stable-digit counts

Marco Ripa and Luca Onnis, **Number of stable digits of any integer tetration**,
Notes on Number Theory and Discrete Mathematics 28 (2022), no. 3, 441-457.

https://nntdm.net/volume-28-2022/number-3/441-457/
https://doi.org/10.7546/nntdm.2022.28.3.441-457

This is related prior work on finite-height stable-digit counts and eventual
behavior, rather than the perfect-power minimum solved in this report.

## 4. Perfect-power existence versus perfect-power minimality

Marco Ripa, **On the relation between perfect powers and tetration frozen
digits**, Journal of AppliedMath 2 (2024), no. 5, Article 1771; arXiv:2602.00252v1,
deposited 30 January 2026.

https://doi.org/10.59400/jam1771
https://arxiv.org/abs/2602.00252
https://arxiv.org/html/2602.00252v1

The arXiv metadata identifies the earlier journal publication and states that
the arXiv version differs by an added reference and an OEIS citation. It should
not be described as a newly published 2026 journal result. The paper concerns
existence of perfect powers with prescribed congruence speed, including
infinitely many cth powers of speed c. Existence does not determine the minimum.
The report cites this work for context; the minimum theorem is proved without
using its construction or assuming any of its more general claims.

## Scope of the new argument

The elementary ingredients (valuation lifting, Chinese remaindering, Hensel
lifting, and factorization) are standard. The contribution developed in this
report is their assembly into an explicit all-n global-minimality proof,
particularly the lower bound x^2 + 1 >= 5^(n-v_5(n)) for every competing root
not divisible by 5. The report also gives the strict-degree classification,
exact tail signs, a sufficient two-parameter region, densities, and asymptotics.

Independent mathematical review is appropriate. Neither computational checks
nor this provenance record constitute external peer review, formal proof
verification, or an exhaustive certification of novelty.
