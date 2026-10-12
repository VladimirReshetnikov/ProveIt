# Reproducible verification

All scripts run without network access or a ProveIt checkout. Use Python 3 with
the versions in the package-level `requirements.txt`. Run the commands below
from the package root. Each script writes its JSON record into `evidence/`.

## Suites and scope

| Script | Exact checks | Numerical diagnostics |
|---|---|---|
| `verify_gamma_normalization.py` | Analytic proof is in the article | 14 checks at 42 digits: original source matrices for m=1,2,3; parameterized determinants including unequal complex parameters; Gamma deformation and scalar digamma/polygamma integrals |
| `verify_gaussian_moments.py` | Determinants of exponential jets use finite polynomial arithmetic | 15 moments at 42 digits; entries are ordinary quadratures; includes n=3 fourth moment and positive shifts other than 1/4 |
| `verify_colored_moments.py` | 41 symbolic assertions: zeta coefficients, simultaneous-tail-zero counterexample, alternating zeros, Bernoulli constants | 11 checks at 50 digits: 3 integer and 2 noninteger direct kernel quadratures, Stieltjes dictionaries, exceptional beta constants, primitive, and color expansion |
| `verify_two_clusters.py` | 448 rational assertions against the predecessor monomial formula and cluster exchange | 4 beta-integral versus spectral-sum comparisons at 90 digits, including a displacement outside the local collision-series disk |
| `verify_two_cluster_negative.py` | Analytic continuation is proved in the article | 3 checks at 55 digits for q=-4, Landen continuation, and the oriented mass primitive |
| `verify_family2_bridge.py` | Second certificate using nine of the existing relation rows; independently evaluates h12 and verifies the actual printed RHS | None; exact arithmetic only |
| `verify_depth_two.py` | Complete 15-row rational shuffle/distribution certificate with zero residual and convergent remaining coordinates | Optional 80-digit quadrature directly from strict colored iterated-integral definitions |

~~~bash
python3 verification/verify_gamma_normalization.py
python3 verification/verify_gaussian_moments.py
python3 verification/verify_colored_moments.py
python3 verification/verify_two_clusters.py
python3 verification/verify_two_cluster_negative.py
python3 verification/verify_depth_two.py --numeric
python3 verification/verify_family2_bridge.py
~~~

For a fast replay of only the depth-two exact certificate:

~~~bash
python3 verification/verify_depth_two.py
~~~

The last command deliberately omits the numerical diagnostic from the newly
written record. Use `--numeric` to reproduce the complete supplied record.

## What the evidence establishes

The Gamma moment diagnostic constructs its left sides from determinants of
one-dimensional integrals and coefficient arithmetic; it does not compute
the left sides from the Gamma quotient being checked. The colored direct
quadratures use the elementary kernel series at colors strictly inside the
unit disk. The cluster suite compares a scalar beta kernel with independently
organized strict harmonic sums and Hurwitz-zeta spectral tails.

Exact rational assertions check finite algebraic identities. The depth-two
certificate additionally requires the analytic shuffle and limiting arguments
proved in the article. Floating-point quadrature residuals do not certify an
error bound and do not establish historical novelty. No numerical relation
search is used as a mathematical proof.

## Recorded residuals

The supplied runs passed their explicit tolerances. Their largest observed
residuals were approximately:

- Gamma normalization: `7.1e-43` relative.
- Gaussian moments: `4.9e-41` absolute.
- Colored moments: `5.4e-37` absolute, in a noninteger endpoint quadrature.
- Two-cluster spectral faces: `3.3e-75` absolute.
- Negative-argument/primitive checks: `3.9e-53` absolute.
- Depth-two integral diagnostic: `2.7e-82` absolute.

Rounding and integration behavior may vary with dependency versions or working
precision. Read each JSON record for actual parameters, both sides, tolerances,
and the stated meaning of the check.
