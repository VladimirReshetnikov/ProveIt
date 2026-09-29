# Source and proof audit

Date: 29 September 2026.

## 1. Repository connection

The repository main revision resolved during the investigation was:

    8d936ee2357f9decf78c2ecc7d9baf3100a6787d

Repository: https://github.com/VladimirReshetnikov/ProveIt

Primary continuation target:

    SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/
    oeis-sequence-asymptotics/a003407-dyadic-scaling-rigidity/

The target report's README and mathematical text were inspected. Its README explicitly makes no non-D-finiteness or natural-boundary claim. The present article resolves the former issue using identified published inputs. Its main proof does not depend on any theorem unique to that unrefereed report.

The earlier report records formal splitting bounds under the Ramsey project, including `LeanProofs.Sharma2012.theorem_2_8_holds` and the Davis–Entringer–Graham–Simmons even and odd counting recurrences. We rely on the published mathematical results, not on an unexecuted claim of kernel checking. No Lean build, Rocq build, or repository-wide axiom audit was run in this work. No repository files were changed.

## 2. Primary mathematical sources

### Enumerative results

**Davis, Entringer, Graham, and Simmons (1977)**, “On permutations containing no long arithmetic progressions,” Acta Arithmetica 34, 81–90.

Role: historical parity-splitting construction. The needed lower bound is reproved directly in the article.

**Arun Sharma (2009)**, “Enumerating permutations that avoid three term arithmetic progressions,” Electronic Journal of Combinatorics 16(1), R63.

https://doi.org/10.37236/152

Role: Theorem 2.8, the uniform upper splitting bound with constant 21. This structural theorem is imported, not rederived from a finite table.

**Boon Suan Ho (2026)**, “3AP-free permutations have no exponential growth rate.”

https://arxiv.org/abs/2602.13617
https://arxiv.org/html/2602.13617v1
https://doi.org/10.1016/j.disc.2026.115237

Role: published nonconvergence of theta(n)^(1/n), with the two dyadic scales used here. The proof mechanism is reproduced and the integer separation checked exactly. This result is not claimed as new.

**Bill Correll, Jr., and Randy W. Ho (2017)**, “A note on 3-free permutations,” Integers 17, A55.

https://arxiv.org/abs/1712.00105

**OEIS A003407**, entry and accompanying table, consulted 29 September 2026.

https://oeis.org/A003407

Role: count data. The Ho in the 2017 paper and Boon Suan Ho are different authors. Counts through 32 are independently regenerated in this package; counts 64 and 75 remain published inputs.

### D-finite and G-function theory

**Richard P. Stanley (1980)**, “Differentiably finite power series,” European Journal of Combinatorics 1, 175–188.

https://math.mit.edu/~rstan/pubs/pubfiles/45.pdf

Role: P-recursive/D-finite correspondence and standard closure context. The article also provides elementary explanations for the consequences it needs.

**Stavros Garoufalidis (2009)**, “G-functions and multisum versus holonomic sequences,” Advances in Mathematics 220, 1945–1955.

https://arxiv.org/abs/0708.4354

Role: Theorem 3 and Proposition 2.5, linking exponentially bounded arithmetic P-recursive coefficients to G-functions and Nilsson coefficient asymptotics. The article uses this G-function specialization, not a formal asymptotic ansatz for arbitrary polynomial recurrences.

**Stavros Garoufalidis (2011)**, “What is a sequence of Nilsson type?”, Contemporary Mathematics 541, 145–157.

https://arxiv.org/abs/1009.0276

Role: precise asymptotic framework, including a genuinely nonzero leading layer.

**Yves André (2025)**, “G-functions, motives, and unlikely intersections—old and new,” arXiv:2501.09867, Section 1.2; and André's G-functions and Geometry (1989).

https://arxiv.org/abs/2501.09867

Role: regular singularity and rational exponents for minimal G-function differential operators. These established arithmetic results are deep imported dependencies. Quasi-unipotent monodromy alone would not justify the asymptotic form, and no unproved geometric-origin conjecture is used.

### Existing profile method

**Hwang, Janson, and Tsai (2022)**, “Identities and periodic oscillations of divide-and-conquer recurrences splitting at half.”

https://arxiv.org/abs/2210.10968

Role: background for the continuous periodic-profile construction. The article reproves the bounded-toll specialization only to support its extensions; the construction is not presented as new.

## 3. Proof dependency map

**Base non-P-recursiveness.** Positivity and integrality; exponential upper bound; elementary deletion injection; Ho's root-growth nonconvergence; rational descent of a hypothetical complex recurrence; published G-function leading-layer theorem; the article's finite-window Vandermonde lemma; one-sided local-growth rigidity.

**All arithmetic sections.** Apply rigidity to the section, then use bounded-gap interpolation under the one-sided forward bound. A limit on any one section would force a global limit. No claim that arbitrary non-P-recursive sequences have non-P-recursive sections is used.

**Robust approximation theorem.** A pointwise logarithmic error o(n) preserves exponential boundedness and subexponential forward increases. The arithmetic coefficient condition is essential to the stated proof. This excludes neither unrestricted real-coefficient approximants nor rational approximants with uncontrolled common denominators.

**Positive polynomial observables.** A two-sided fixed-shift estimate follows by binary descent of the bounded splitting toll. Nonnegative coefficients prevent cancellation, making the largest total count degree determine the exponential logarithmic scale. Signed expressions are not covered.

**Logarithmic profiles and perturbed sampling.** Continuity gives local subexponential increments; phase density gives nonconvergent roots. For the stated perturbation scale, the logarithmic fixed-shift estimate controls the change of sampled index. These extensions are proved separately from the shorter main proof.

**Generating functions.** P-recursive/D-finite equivalence and multiplication of coefficient sequences by n! connect the ordinary and exponential series. Algebraic power series are D-finite, so ordinary transcendence follows. This is not differential transcendence.

## 4. Logical traps explicitly avoided

- Nonconvergence of nth roots is not, by itself, an obstruction to P-recursiveness. The rational-series counterexample `3^n + (-3)^n + 2^n` is discussed.
- A Nilsson expansion does not automatically imply a pointwise root limit: dominant phases may cancel. An invertible Vandermonde matrix supplies a nonzero term in every sufficiently late fixed-length window.
- The local condition is one-sided. Monotonicity is neither assumed nor proved.
- Complex recurrence coefficients do not weaken the conclusion for a rational sequence: finite-dimensional rational row-space descent is proved explicitly.
- Eventual recurrences are excluded. No fixed order, degree, or starting index is presumed.
- Finite recurrence-fitting failures are not substituted for an infinite proof.
- Natural boundaries and differential transcendence do not follow from non-D-finiteness.

## 5. Executed computation

`code/verify.py` was executed with its default bounds. Its delivered JSON records:

- independent subset-state enumeration for all n=0,...,32;
- agreement with independent direct permutation enumeration for n=0,...,8;
- agreement with the published small count values;
- exact splitting-inequality checks in this finite range;
- exact integer separation of the two published large-count bounds;
- exact rational brackets yielding a logarithmic separation greater than 1/2279;
- nonzero integer determinants for two finite recurrence rectangles.

The verifier took approximately eleven seconds in the construction environment. Its runtime is diagnostic. It uses arbitrary-precision integers, explicit non-optimizable checks, and exact Bareiss divisions; decimal logarithms are recorded only as diagnostics.

The two recurrence matrices have specifications `(order, coefficient degree, first row) = (5,3,0)` and `(4,3,8)`, with sizes 24 and 20. They use independently generated counts through 28 and 31 respectively. Their full signed determinants are recorded in the JSON. They exclude recurrences only on those specified finite windows.

`code/test_verify.py` supplies additional independent unit tests, including comparison of the integer determinant routine with a direct permutation definition for fixed small matrices and deterministic random matrices. Its actual test output is in `data/unit-tests.txt`.

None of these Python runs is a proof-assistant verification. In particular, the code does not establish Sharma's infinite upper recurrence, re-enumerate theta(64) or theta(75), or check the imported arithmetic differential-equation theory.

## 6. Novelty and remaining uncertainty

Targeted searches combined A003407 and 3AP-free permutation terminology with “P-recursive,” “holonomic,” and “D-finite,” and the relevant primary sources were inspected. No prior instance of the present non-P-recursiveness application was located. This is a bounded literature assessment, not an exhaustive priority certificate.

The article's intended contribution is the stated application and its stable extensions. The general finite-dimensional noncancellation device may have antecedents; no claim that Vandermonde arguments or arithmetic asymptotic rigidity are wholly unprecedented is made. The conventional proofs are supplied for independent review, not certified by a formal kernel or peer review.

The article proposes nine further research directions, with natural boundaries, nonlinear differential equations, profile geometry, monotonicity, signed cancellation, an elementary substitute for G-function theory, large-count certificates, effective recurrence obstructions, and other hereditary enumerations all explicitly separated from the proved results.
