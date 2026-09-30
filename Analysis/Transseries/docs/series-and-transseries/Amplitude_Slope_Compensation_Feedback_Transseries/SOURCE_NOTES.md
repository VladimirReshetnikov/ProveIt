# Source notes and claim provenance

## Repository snapshot

Owner/repository: `VladimirReshetnikov/ProveIt`  
Commit: `ebd8344bca77d8352cd745b7df374618a290a029`  
Inspection date: 29 September 2026.

Repository resources were read through the GitHub connector. The following
paths identify the inspected material, rather than a claim of exhaustive review.

1. `Analysis/Transseries/README.md` — project split, formal modules, and document
   organization.
2. `Analysis/Transseries/docs/series-and-transseries/README.md` — current inventory
   and the explicit warning that the recent research arrivals are unmerged,
   not reviewed claim by claim, and not Lean-formalized.
3. `Analysis/Transseries/docs/series-and-transseries/Exponential_Feedback_Regularity_Classification/article.tex`
   — source lines 1440–1508, especially lines 1470–1483, “Amplitudes, general
   actions, and multiple scales.” This explicitly asks for weighted analogues
   of the unit-amplitude classification.
4. `Analysis/Transseries/docs/series-and-transseries/Negative_Ray_Summation_Exponential_Feedback/article.tex`
   — source ranges 1–540, 600–1030, and 1360–1515. These supply the unit-amplitude
   result, inverse-block and Bessel method, the distinction between fine and
   angular summation, and the explicit question “Weighted actions and joint
   amplitude–slope thresholds.”

Pinned source links:

- https://github.com/VladimirReshetnikov/ProveIt/tree/ebd8344bca77d8352cd745b7df374618a290a029/Analysis/Transseries
- https://github.com/VladimirReshetnikov/ProveIt/blob/ebd8344bca77d8352cd745b7df374618a290a029/Analysis/Transseries/docs/series-and-transseries/Exponential_Feedback_Regularity_Classification/article.tex
- https://github.com/VladimirReshetnikov/ProveIt/blob/ebd8344bca77d8352cd745b7df374618a290a029/Analysis/Transseries/docs/series-and-transseries/Negative_Ray_Summation_Exponential_Feedback/article.tex

The present article gives its own proofs. It does not assume the correctness
of an earlier draft's asymptotic classification merely because the draft is in
the repository. No claim is made that the entire canonical volume was read.
No source material was added to or edited in the repository.

## Primary external references

- Ira M. Gessel, *Lagrange inversion*, Journal of Combinatorial Theory A 144
  (2016), 212–249. DOI: 10.1016/j.jcta.2016.06.018.
  https://arxiv.org/abs/1609.05988
- David Sauzin, *Introduction to 1-summability and resurgence* (2014),
  arXiv:1405.0356. Sections 7 and 9 distinguish fine summability from an arc of
  directions. The article supplies a fixed-tube inverse proof rather than
  invoking a theorem with a stronger angular hypothesis.
  https://arxiv.org/abs/1405.0356
- NIST DLMF, Sections 10.9 and 10.25, for the Poisson integral and modified
  Bessel power series. The normalized beta-measure formula needed in this
  article is proved directly.
  https://dlmf.nist.gov/10.9
  https://dlmf.nist.gov/10.25

These sources were checked online. A targeted literature search did not
establish publication priority for the weighted results. No absence-of-prior-art
or “first-ever” claim is made.

## Provenance of the mathematics

Classical tools: finite Lagrange inversion; analytic implicit inversion where
its kernel really is analytic; beta/Bessel integral representations; factorial
bounds; convolution estimates for summable series; positive-coefficient
singularity arguments.

Contributions developed in this package: the two joint amplitude–slope budgets;
weighted uniform inverse remainders; the sharp weighted fine-summability
criterion; the strong-damping exact forward type; dense power-cost coefficient
root limits and probability concentration; the corresponding weighted Borel
continuation estimate and explicit examples.

The unit-amplitude inverse-block/Bessel strategy is credited to the inspected
negative-ray draft and its classical antecedents. Unit-amplitude special cases
are not presented as new discoveries.

## Verification status

The exact finite checks and the rational interval certificate were executed.
The floating diagnostics are labeled separately. The article was built by
three pdflatex passes; its rendered pages were inspected for layout and
formula clipping. The package contains no Lean proof and no claim of
independent peer review. See `data/build_info.json` for final run details.
