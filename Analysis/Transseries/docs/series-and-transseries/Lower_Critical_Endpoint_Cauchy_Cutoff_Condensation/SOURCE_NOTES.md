# Source provenance and research scope

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected commit: `3d5973524506411392a911470b5ddc35521568ea`

The snapshot was obtained from the repository tree through the connected
GitHub read interface. The research target was chosen from the actual report,
not inferred from a title or from an earlier conversation summary.

Primary target:

https://github.com/VladimirReshetnikov/ProveIt/blob/3d5973524506411392a911470b5ddc35521568ea/Analysis/Transseries/docs/series-and-transseries/Critical_Hahn_Transseries_Beyond_Finite_Action_Folds/article.tex

Relevant passages: the model and exact coefficient identities in its opening
sections; Question 4, “Endpoint exponents and logarithmic crossover,” around
source lines 1502–1507; the adjacent editorial note explicitly distinguishing
the still-unaddressed lower endpoint from the upper-endpoint research packages.
The question and editorial discussion were read together, not as an isolated
search snippet.

Other inspected repository documents:

- `README.md`
- `Analysis/Transseries/README.md`
- `Analysis/Transseries/docs/series-and-transseries/README.md`

The documentation index was read in sections covering the existing regularity,
critical Hahn, marginal, logarithmic-endpoint, confluent, and stable–Gaussian
research packages. The new article does not claim those prior packages as its
own work and does not depend on their unreviewed endpoint proofs.

## External mathematical sources

1. Svante Janson, *Simply generated trees, conditioned Galton–Watson trees,
   random allocations and condensation*, Probability Surveys 9 (2012),
   103–252. DOI: 10.1214/11-PS188. https://arxiv.org/abs/1112.0510

2. Inés Armendáriz and Michail Loulakis, *Conditional distribution of heavy
   tailed random variables on large deviations of their sum*, Stochastic
   Processes and their Applications 121(5) (2011), 1138–1147.
   DOI: 10.1016/j.spa.2011.01.011. https://arxiv.org/abs/0912.1516

3. Igor Kortchemski and Loïc Richier, *Condensation in critical Cauchy
   Bienaymé–Galton–Watson trees*, arXiv:1804.10183v3, 21 November 2018.
   https://arxiv.org/abs/1804.10183v3

4. NIST Digital Library of Mathematical Functions, equation 25.12.12,
   polylogarithm expansion. https://dlmf.nist.gov/25.12.E12

The two condensation papers were inspected in full-text/PDF form around
relevant limit and deletion theorems. Their mechanisms are credited; a theorem
for a fixed distribution is not used as an unproved uniform theorem for the
moving-parameter family. The article supplies its own Poisson decomposition,
local concentration estimate, tilt estimate, and small-jump argument.

## Exact scope of the contribution

- Real positive epsilon approaches zero from above.
- The tail is exactly j^(-2-epsilon) beyond a fixed prefix.
- The finite-prefix polynomial is fixed and the resulting action weights are
  nonnegative, with a positive first weight.
- Coupling is exactly critical as defined in the article.
- The leading coefficient theorem permits every joint rate n -> infinity,
  epsilon -> zero. The Cauchy fluctuation law separately requires
  n c_epsilon -> infinity.
- Bounded intensity is treated separately by a discrete compound-Poisson law.
- The analytic inverse is a local convergent chart on specified branches.

Not claimed: global publication priority, peer review, a Lean-checked theorem,
a finite-n certified cutoff algorithm, arbitrary slowly varying tails,
noncritical coupling limits, full tree geometry, global continuation,
resurgence, or Borel summability.

## Research fingerprint

lower critical endpoint / exponent one / arbitrary-rate triangular Poisson
condensation / finite-prefix critical normalization / exact truncated-mean
center / reflected skew 1-stable cutoff / logarithmic action-budget shift /
sparse-dense matching / removable-parameter Hahn chart
