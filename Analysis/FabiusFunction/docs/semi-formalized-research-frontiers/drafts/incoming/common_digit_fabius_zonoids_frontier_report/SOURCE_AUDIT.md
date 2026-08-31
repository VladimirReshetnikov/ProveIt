# Repository audit and novelty boundary

## Requested scope

The target was the recursive LaTeX documentation tree:

`Analysis/FabiusFunction/docs/**.tex`

in the public `VladimirReshetnikov/ProveIt` GitHub repository.

## How the corpus was handled

The tree contains polished expositions, a canonical semi-formalized frontier
compilation, thematic draft families, generated or merged compilations, and
archived snapshots.  The audit therefore used a hierarchy rather than treating
identical archived copies as independent mathematical sources:

1. the live primary synthesis for definitions, normalizations, and established
   Fabius/Rvachev facts;
2. the canonical semi-formalized frontier document and its thematic manifest;
3. recursive filename, heading, theorem-label, and term scans across the draft
   subtrees;
4. targeted full-text checks of files whose titles or manifest descriptions
   intersected the new construction;
5. archive material as provenance and duplication control when its content was
   superseded or exactly repeated by a live compilation.

The report records this method in Section 1 and describes its conclusions as
**repository-novel**, not as unconditional historical priority.

## Existing themes treated as background rather than rediscovered

The audited corpus already develops, among other topics:

- the Fabius and Rvachev up-functions and their functional equations;
- the one-parameter geometric-uniform law at general `q` and at `q=1/2`;
- exact dyadic values and Thue-Morse identities;
- q-Pochhammer symbols, q-binomial coefficients, and related q-series;
- infinite sinc products and Fourier decay;
- endpoint asymptotics involving Lambert-W;
- inverse-Fabius asymptotics;
- Bell and Bernoulli polynomial/cumulant expansions;
- Legendre expansions and shifted-up-function representations;
- interpolation, parameter differentiation, and several asymptotic/frontier
  programs.

These topics are cited and reused only as inputs or comparison points.

## New organizing construction

The report instead fixes one digit sequence and evaluates the entire family at
several parameters simultaneously:

`X_q = (1-q) sum_{n>=0} q^n U_n`.

This common-digit coupling produces a multivariate infinite zonotope and makes
available structures that are invisible in the marginal laws alone.  Prior to
writing, the live synthesis, frontier compilation, thematic manifest, and
relevant parameter-front drafts were searched for combinations of the terms

- common digit / shared digit / common noise;
- zonoid / zonotope / support volume / mixed volume;
- hyperbolic secant covariance / sech kernel;
- mixed cumulant across parameters;
- correlation determinant / prediction error;
- confluent support volume / parameter-jet volume;
- Euler jet determinant / Meixner-Pollaczek innovation.

No matching theorem package was found in the audited live corpus.  The report
therefore develops these as its central repository-new direction.

## Main repository-new results developed in the report

- exact `d`-dimensional support volume
  `prod_{i<j}(q_j-q_i)/(1-q_i q_j)` for ordered positive parameters;
- the hyperbolic-coordinate form `prod tanh(u_j-u_i)`;
- equality of support volume with the square root of the standardized
  correlation determinant;
- exact linear-prediction errors and a Szego-kernel interpretation;
- all mixed cumulants in closed Bernoulli form;
- a stationary hyperbolic-secant Gaussian limit under hyperbolic translation,
  with explicit cumulant corrections;
- an Euler-number Hankel determinant and Meixner-Pollaczek derivative-
  innovation ladder;
- exact positive-parameter jet and multi-jet support volumes;
- an exact two-parameter geometric-comb boundary with log-periodic modulation;
- inverse-Fabius copula and Legendre coefficient bridges;
- conjectural signed, complex, Fourier-ray, endpoint-copula, q-Barnes, and
  Thue-Morse extensions.

## Important correction incorporated before release

Although the samplewise parameter jet exists for every `|q|<1`, its simple
support-volume product is valid only in the positive chamber `0<q<1`.
Numerical determinant checks expose orientation changes for negative `q`.
The released theorem and code therefore reject a signed extension and place it
in the explicitly conjectural chamber program.
