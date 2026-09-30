# The Lower Critical Endpoint
## Arbitrary-Rate Condensation, Cauchy Cutoff Laws, and Degenerating Transseries

A 24-page research article prepared for Vladimir Reshetnikov, 29 September 2026.

## Files

- `lower_critical_endpoint.pdf`: compiled article.
- `lower_critical_endpoint.tex`: self-contained LaTeX source; the numerical tables are embedded.
- `verify.py`: exact finite algebra checks and floating-point numerical diagnostics.
- `verification_results.json`: complete recorded results of the full verification run.
- `verification_run.txt`: human-readable console output from that run.
- `requirements.txt`: dependencies for the verification program.
- `build.sh`: three-pass PDF build.
- `SOURCE_NOTES.md`: pinned repository provenance, literature, scope, and novelty boundaries.
- `VALIDATION.md`: compilation, mathematical-proof checks, and computational-validation boundaries.

## Research target

The paper addresses the lower-endpoint half of Question 4 in ProveIt's
`Critical_Hahn_Transseries_Beyond_Finite_Action_Folds/article.tex`, at commit
`3d5973524506411392a911470b5ddc35521568ea`.

The family is

    U(q) = c_epsilon [Li_(2+epsilon)(q exp(U(q))) + P(q exp(U(q)))],
    c_epsilon = 1 / (zeta(1+epsilon) + P'(1)),

where P is a fixed polynomial that alters finitely many nonnegative action
weights. The parameter epsilon tends to zero while the coefficient index n
tends to infinity.

## Main conclusions

The article proves a coefficient equivalent for **every** rate epsilon_n -> 0,
including nc_epsilon tending to infinity, remaining bounded, or tending to zero.
For rho = exp[-c_epsilon(zeta(2+epsilon)+P(1))] and

    d = (n c_epsilon / epsilon)^(1/(1+epsilon)),

it gives

    [q^n]U(q) ~ rho^(-n) epsilon/(n d).

The probability configuration producing the coefficient has one exceptional
action. Deleting that largest action recovers the unconditioned Poisson
configuration in total variation. In the dense regime the remaining actions
have a compensated, right-skewed 1-stable cloud on the smaller scale

    b = (n c_epsilon)^(1/(1+epsilon)).

For a prescribed retained fraction r, the smallest action cutoff is

    M_r = d + b [log(1/epsilon)/(1+epsilon) + F^(-1)(r)] + o(b),

where F is the explicitly normalized reflected 1-stable distribution in the
paper. Omitting the logarithmic shift causes asymptotically zero retention,
even though the leading relative scale is correct.

A separate convergent critical inverse chart is uniform through the removable
parameter endpoint. The endpoint equation itself degenerates to U=0; the paper
does not misidentify that endpoint as a nonzero critical solution.

## Proof and novelty status

These are conventional proofs in an unrefereed research article. General
one-large-summand principles, Cauchy condensation, and largest-summand deletion
are credited to the existing literature. The scoped contribution is the
explicit arbitrary-rate triangular-family theorem and its consequences here.
Global publication priority has not been established.

There is no new Lean formalization and no claim to solve general resurgence,
Borel summability, arbitrary slowly varying tails, or every lower-endpoint
transseries model. The formalization plan and nine further research directions
are in the article. No repository files were modified.

## Build

With a standard TeX installation including the packages listed in the source:

    sh build.sh

Alternatively run `pdflatex lower_critical_endpoint.tex` three times.

## Verification

With Python 3.10 or later:

    python -m pip install -r requirements.txt
    python verify.py

The full run writes `verification_results.json`. A shorter run,

    python verify.py --quick

writes `verification_quick.json` instead and does not replace the full record.

The recorded run passed **62 exact algebra assertions**. The coefficient,
cutoff, chart, finite-prefix, and CDF calculations are floating-point diagnostics,
not interval certificates. The full run uses extended-precision long-double
recurrences where supported and checks for underflow. The mathematical proofs
do not depend on these numerical calculations.
