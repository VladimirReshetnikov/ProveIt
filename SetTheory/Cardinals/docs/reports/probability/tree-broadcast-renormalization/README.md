# Binary broadcasts: a sharp analytic renormalization threshold

This self-contained research note proves a theorem package about the sum of
the spins in the last level of a binary broadcast on a rooted `b`-ary tree.
The root is fixed to `+1`, and each independent edge sign has mean `theta`.

## Main results

For `X_n = (b theta)^(-n) sum_{|v|=n} sigma_v`, the transforms

`exp(-Var(X_n) t^2 / 2) E exp(t X_n)`

converge locally holomorphically near zero **if and only if
`theta > b^(-3/4)`**. The limiting residue is jointly analytic in the
parameter and argument, with an exponential convergence estimate on
compact parameter intervals. An explicit third/fourth-cumulant calculation
proves failure at and below the threshold, including the fourth-cumulant
boundary and the small binary-tree interval where the initial forcing is
positive.

The note also proves:

- A finite-depth critical-window theorem for
  `theta_n = b^(-1/2) exp(gamma/(2n))`, uniform for bounded real `gamma`,
  with exact variance and all-orders parameter expansions.
- Arbitrary-order uniform lattice local limit expansions, justified by
  separate high-frequency bounds over a complete Fourier interval.
- A full expansion of majority-decoding success, including fair tie
  handling and the half-integer lattice offset for odd `b`.
- At `b=2` and exact criticality,
  `p_n = 1/2 + 1/sqrt(pi n) - 5/(4 sqrt(pi) n^(5/2)) + O(n^(-7/2))`.
  The `n^(-3/2)` correction vanishes.
- Finite even-cumulant renormalization for every `theta > 1/b`, provided
  sufficiently many even cumulants are removed.

## Files

| File | Purpose |
| --- | --- |
| `article.tex` | Complete article, proofs, references, and research questions |
| `article.pdf` | Compiled 20-page article |
| `verify.py` | Standard-library-only exact rational verification |
| `verification.json` | Recorded exact results and finite-distribution checks |
| `provenance.json` | Source pin, specific manuscript path, and claim scope |
| `../VALIDATION.json` | Final compilation and artifact verification summary |

## Reproduction

```bash
python verify.py --output verification.json
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The verification uses `fractions.Fraction` for every assertion. The recorded
run passes **392 exact scalar checks**, plus exact fixed-series identities
through degree ten. Independent probability-generating computations cover
critical trees with up to 81 leaves and several noncritical rational
correlations. The script verifies finite algebra; the analytic convergence
and Fourier estimates are proved in the article. There is no Lean
formalization in this package.

## Relation to prior work and novelty boundary

Broadcast recursions, the critical central limit theorem, and earlier
moment-asymptotic methods are established and credited. The note explicitly
distinguishes level sums from whole-tree magnetization and majority decoding
from optimal reconstruction using the complete boundary.

The precise contribution proposed for further review is the sharp local
holomorphic renormalization threshold, the uniform analytic residue across
the finite-depth critical window, and the all-orders local/decoder
consequences. The proofs are independent derivations. The literature audit
does not certify historical priority for every statement.

The motivating `openai/math` manuscript belongs to family 236 and concerns
the factor-of-IID threshold for the free Ising model. **Its main theorem is
not assumed here.** The source was inspected using the GitHub plugin at
commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`; the exact path is in
`provenance.json`.

## Suggested integration

The directory can be placed under a probability/statistical-mechanics area
of ProveIt, for example `Probability/TreeBroadcastRenormalization/`.
All build and verification commands work relative to this directory; no
external repository checkout is required. No remote repository was modified.
