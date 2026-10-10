# Integration into ProveIt

Baseline: commit `afed07429d3d37eceb6c8e9e54cf4da2d3f39d53`.
Source chapter: `Analysis/Polylogarithms/docs/manuscript/chapters/04-depth.tex`.
Source blob: `6171912ff7724784cabb789a066c61223ab298bc`.

## Recommended additive layout

Keep this package together, for example under
`Analysis/Polylogarithms/docs/articles/gaussian-signed-kernel-continuation/`.
Keeping `code/` and `data/` immediately below the article directory preserves
all relative paths in the scripts. This is a suggested new destination, not a
claim that the directory already exists.

The main manuscript can import `integration/gaussian-continuation-section.tex`
after the current section containing the weight-five/six candidates. Adapt the
relative `\input` path to the chosen destination. The fragment assumes the
manuscript's existing `theorem` environment and amsmath support, uses only its
own `gcc:` labels, and leaves the original equation labels intact.

Insert `integration/bibliography-items.tex` inside the manuscript's existing
`thebibliography` environment, before its closing command. Reuse an existing
Panzer entry instead of creating a duplicate reference when convenient,
updating the fragment's citation key consistently.

## Exact source-status changes

| Source label | Action | Proof route |
|---|---|---|
| `gauss:eq:wt5-sporadic` | Promote to theorem | Article equations (6.6)--(6.8); two shuffle rows |
| `gauss:eq:g51` | Promote to theorem | Article Theorem 5.1, Gaussian specialization |
| `gauss:eq:g42` | Promote to theorem | Same |
| `gauss:eq:g33` | Promote to theorem | Same |
| `gauss:eq:g24` | Promote to theorem | Same |
| `gauss:eq:g15` | Promote to theorem | Same |
| `gauss:eq:S4-closed` | Keep conjectural | Equivalent form, certified discrepancy, restricted-module obstruction only |

The machine-readable version is `integration/source-status.json`.

The prose introducing the candidate display should no longer say that all of
these equations lack analytic derivations. Split it into proved Gaussian double
reductions and the remaining candidates. The four weight-five Gaussian
coordinates span at most **two**, not merely at most three, directions modulo
the indicated depth-one products. This is an improved upper bound, not a proof
of independence.

Do not upgrade the subsequent triple-polylogarithm identities, numerical
period dimensions, the all-odd-weight rank conjecture, or the S4 identity.
The signed-kernel and unique-zero theorems have a broader domain than the
integer-weight tables; retain their exact hypotheses.

## Review and replay

Compare source labels against the actual integration commit before applying
text. This package was checked against a pinned snapshot, not every future
version of `main`. Run `python code/verify.py`, `python code/numerics.py`, and a
fresh manuscript LaTeX build after integration. The standalone fragment was
smoke-tested with representative manuscript environments, not by rebuilding
the complete remote manuscript.

No repository write, commit, pull request, or original-file replacement was
performed in preparing this package.
