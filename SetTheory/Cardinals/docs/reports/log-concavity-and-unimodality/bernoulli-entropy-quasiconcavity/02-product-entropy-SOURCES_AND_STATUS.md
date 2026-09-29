# Sources, proof status, and priority boundaries

Checked on 29 September 2026.

## Repository source

Pinned baseline: `ac9107d74083fcfe8064b4aaeda7989612e6a5b6`.
Relevant source:
`SetTheory/Cardinals/docs/reports/log-concavity-and-unimodality/bernoulli-entropy-quasiconcavity/article.tex`.
Its README and the article's setup, subunit fixed-mean theorem, one-coin Renyi
threshold, separate-coordinate concavity, and higher-dimensional ordinary-sum
counterexample were inspected through the GitHub connector.

Pinned source:
https://github.com/VladimirReshetnikov/ProveIt/blob/ac9107d74083fcfe8064b4aaeda7989612e6a5b6/SetTheory/Cardinals/docs/reports/log-concavity-and-unimodality/bernoulli-entropy-quasiconcavity/article.tex

The existing report concerns the **ordinary sum**. The present manuscript's
main target is the **joint independent vector**, equivalently an injectively
weighted encoding. Neither model should be silently substituted for the other.

## Primary literature inspected

1. E. Hillion and O. Johnson, *A proof of the Shepp--Olkin entropy concavity
   conjecture*, Bernoulli 23(4B), 2017, 3638--3649.
   https://arxiv.org/abs/1503.01570
   https://doi.org/10.3150/16-BEJ860
   Original PDF page containing Conjecture 4.2 inspected as a screenshot.

2. H. Wang, *The Sharp Renyi and Tsallis Threshold in the Shepp--Olkin
   Concavity Problem*, arXiv:2609.27433v1, submitted 23 September 2026.
   https://arxiv.org/abs/2609.27433v1
   Abstract and HTML consulted. It states the ordinary-sum threshold is exactly
   one and establishes subunit power-sum concavity. This manuscript reports that
   claim for current context; it does not rely on or independently certify the
   preprint's proof. No priority claim over that unweighted result is made.

3. C. Tsallis, *Possible generalization of Boltzmann--Gibbs statistics*, Journal
   of Statistical Physics 52, 1988, 479--487.
   https://doi.org/10.1007/BF01016429
   Publisher page checked for the entropy convention and bibliographic details.

## Priority audit

Searches included combinations of Tsallis entropy, Bernoulli products,
concavity, dimension thresholds, weighted sums, and Shepp--Olkin. Several highly
specific queries returned irrelevant results. No inspected primary source stated
the exact nine-versus-ten product dimension theorem or the scalar profile derived
here. This is **not** a comprehensive bibliographic search and does not establish
priority. The manuscript's proposed original contribution is the dimension
classification and its exact refinements, not the known entropy definitions,
rank-one matrix lemma, binary Renyi threshold, or product factorization alone.

## Evidence boundaries

- Analytically proved in the article: universal dimension theorem, local/global
  scalar criterion, hyperbolic inequality, unique optimizer, exceptional-order
  values, quartic law, derivative sign, arbitrary-near-unit weighted-mean
  obstruction, strong concavity, endpoint asymptotics, full product-order
  classification, and block-product criterion.
- Finite exact computer-assisted certificates: the two explicit finite midpoint
  inequalities and the nonexceptional threshold table. The local curvature
  certificate is also an explicit integer inequality printed in the article.
- Symbolic checks: 14 finite identities/root counts; not a proof assistant.
- Numerical only: profile plots and displayed decimal approximations. These are
  never used to decide the sign of a claimed exact inequality.
- Not done: referee review, full literature-priority confirmation, Lean
  formalization, classification of all collision patterns, proof of global
  unimodality, a complete generic rational-order software solver.

An important constraint distinction is explicitly preserved: the five-low,
five-high sign direction preserves the mean Hamming count; the adjusted direction
for near-unit weights preserves the mean of the actual weighted sum. These are
two different constraints, both handled in the article.
