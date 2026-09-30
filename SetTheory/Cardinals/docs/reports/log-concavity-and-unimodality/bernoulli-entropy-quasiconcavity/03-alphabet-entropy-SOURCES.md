# Sources and repository audit

## Pinned repository source

Repository: https://github.com/VladimirReshetnikov/ProveIt

Snapshot: `1085b506d65e207a05b7e9c861bb1fe88432fe38`

Directory:
`SetTheory/Cardinals/docs/reports/log-concavity-and-unimodality/bernoulli-entropy-quasiconcavity/`

Inspected with the connected GitHub tools:

1. `README.md`: description of Parts I and II, their scope, the binary results,
   and the explicit statement that the block criterion does not classify
   categorical distributions without evaluating its block quantities.
2. `article.tex`, source lines 1470–1770: binary rank-one criterion,
   hyperbolic optimizer, uniform nine-bit bound, and exact half-order result.
3. `article.tex`, source lines 2350–2530: block-product theorem in Section 22,
   Q7 in Section 23, and neighboring research questions and verification limits.

The exact target is Q7's categorical-simplex part. The current article does
not purport to solve the question for every structured distribution family.
The abstract block-product matrix principle, the binary ten-bit half-order
threshold, and the prior binary order classification are credited to this
source and re-derived as needed, not rebranded as new.

## Primary bibliographic records checked

### Sakai and Iwata

Yuta Sakai and Ken-ichi Iwata, *Sharp Bounds Between Two Rényi Entropies of
Distinct Positive Orders*, arXiv:1605.00019v2, 2016.
https://arxiv.org/abs/1605.00019

The record and abstract describe sharp norm/entropy bounds at two distinct
orders. This is antecedent context for the extremal problem. The full proof
was not inspected and is not an external dependency of the present proof.

### Reeb and Wolf

David Reeb and Michael M. Wolf, *Tight bound on relative entropy by entropy
difference*, IEEE Transactions on Information Theory 61 (2015), 1458–1473;
arXiv:1304.0036v3.
https://arxiv.org/abs/1304.0036

The record and abstract explicitly include a tight dimension-dependent bound
on variance of surprisal, for classical and quantum systems. The present
varentropy endpoint is given with an independent derivation and credited as
connection to this prior problem, not claimed as a new classical extremal
problem. The full paper's proof was not inspected.

### Wang (recent ordinary-sum preprint)

Haoran Wang, *The Sharp Rényi and Tsallis Threshold in the Shepp–Olkin
Concavity Problem*, arXiv:2609.27433v1, submitted 23 September 2026.
https://arxiv.org/abs/2609.27433

The abstract states a threshold for the ordinary Bernoulli sum. Only the
abstract and metadata were checked; its proof is not reviewed or used.
The current paper studies the independent joint vector instead. No transfer
between these two observables is assumed.

## Search limits

Targeted searches for categorical product-entropy concavity, finite-alphabet
thresholds, and related power-sum extremal results did not establish an
exhaustive priority history. Searches with the seventeen/eighteen terminology
did not return a relevant primary match. Absence of a search match is not
proof of novelty. The package makes a repository-relative extension claim
and records the limitation explicitly.

No third-party paper text or repository source files are bundled.
