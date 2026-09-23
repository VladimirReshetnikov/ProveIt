# Research audit

Date: September 23, 2026.
Repository: https://github.com/VladimirReshetnikov/Surreal
Observed commit: `a45d72292a46dac13300d395101df188efb84eef`.

## What was compared

The GitHub connector was used to read branch metadata, repository navigation, the root README, the initial formalization-status discussion, the infinite-dimensional spectral report's README and article opening, and the three-duals report's README. The mathematical comparison relies on the precise theorem descriptions and labels in those sources. It does not assert an independent proof audit of every page of those reports or every repository file.

The two most relevant report directories are:

- `docs/surcomplex/infinite-dimensional-hahn-spectral-theory`
- `docs/surcomplex/three-duals-of-hahn-vector-spaces`

The spectral report already supplies automatic adjointable-operator reconstruction, norm-attainment/least-bound criteria, and coercive nonsurjective examples. The duals report supplies arbitrary-rank spherical completeness and detailed failures of unrestricted Riesz representation. Those are not claimed as new here. The root formalization ledger's actual clause-specific proof coverage is not replaced by any statement in this delivery.

Published primary sources consulted or bibliographically checked include Conway, Soler and Holland, Kato, Simon, Bagayoko et al., Freni, Ishizuka, and Lack--Tobin, as cited in the article. Searches also targeted Hahn/Hilbert orthogonal graphs, projection lattices, and isometric positive forms. They did not reveal the exact combined candidate statements. This is limited negative search evidence, not an exhaustive literature exclusion.

## Candidate original theorem package

The all-projector residue/graph classification; the closed-operator infinitesimal-graph criterion; the polynomial positive-kernel obstruction; failure of binary lattice operations and a countable orthogonal join; the exact residue threshold for isometric standardization of a positive metric; and the automatic set-support descent of global adjointable class maps are the proposed contribution package.

The Kato--Nagy intertwiner formula, formal exp/log machinery, Hahn support calculus, ordinary closed-operator graph orthogonality, and an abstract Soler obstruction are explicitly not claimed as inventions. Some positive results are natural extensions or syntheses of these tools. Priority must be evaluated at the level of the stated hypotheses and conclusions, not the presence of a familiar formula.

## Deliberate safeguards

1. Coefficient Hilbert summation and strong Hahn summation are distinct. A constant l2 vector is allowed; its infinitely many coordinate squares are not called a strong Hahn scalar family.
2. All fixed-workspace supports and Hilbert coefficient spaces are sets. The global section uses class theory explicitly and quantifies over given class maps.
3. Spherical completeness means nests of valuation balls, not arbitrary ordered-field norm balls. The full fine topology on No is separately treated.
4. Strongly summable positive-order powers are not assumed to be topological partial-sum limits at high rank.
5. Ordinary boundedness of coefficient operators is essential. A common support by itself is insufficient for countable projection synthesis.
6. Orthoclosed means equality with the double orthogonal complement. The c00 example is not orthoclosed; the closed-unbounded-operator graph is.
7. No unrestricted Riesz, projection, countably additive spectral-measure, or field-valued least-operator-norm theorem is asserted.
8. No surreals-specific theorem is labeled Lean-verified. Successful PDF compilation and finite checks are not proof-assistant verification.

## Finite verification

The supplied Python program performs 234 exact identity checks using fractions.Fraction. It checks finite real rational matrices and formal coefficients through degree 14. Its scope explicitly excludes infinite-dimensional boundedness/domain arguments, arbitrary Hahn support proofs, missing joins/meets, and proper-class assertions. The JSON records that limited scope.

## Publication status

AI-assisted research manuscript, with written proofs; not independently refereed. No named published open problem is claimed solved. Novelty is proposed and qualified, not certified.
