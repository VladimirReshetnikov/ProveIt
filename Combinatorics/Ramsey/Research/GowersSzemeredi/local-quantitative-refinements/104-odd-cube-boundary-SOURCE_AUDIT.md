# Source audit — 7 October 2026

## Repository inspection

### openai/math

Pinned research snapshot:
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Read the introduction, lines 1–125, and the complete normalized-cube comparison
section of:

`preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/`

The selected files are `build/sections/00-introduction.tex` and
`build/foundations/06-normalized-cube.tex`.

The introduction states a fixed-length bound
r_k(N) <= C_k N exp(-c_k (log N)^(epsilon_k)) and derives its reciprocal-sum
consequence. The selected comparison section concerns conditional image measures,
Boolean jets, and normalized chart errors. These are contextual sources only.
The complete manuscript was not independently rechecked and its main theorem is
not used in the present proof.

Repository: https://github.com/openai/math

### ProveIt local research

Pinned inspection snapshot:
`42906e55ba0aeafe58e2ba507df64aa2899f80bc`.

Read selected beginning portions of:
`Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/README.md`

Read in full:
`Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/101-cube-stability-formalization_plan.md`

The plan explicitly says it is not a checked Lean development and describes the
predecessor's cube, energy, rounding, boundary, and odd-order architecture.
Other search results were used for navigation, not to certify unseen proofs.

Repository: https://github.com/VladimirReshetnikov/ProveIt

### Later ProveIt formal-port checkpoint

Read commit metadata and relevant change descriptions at:
https://github.com/VladimirReshetnikov/ProveIt/commit/97ce7d847a4190d3457cf4af67d5ebb32558fd98

The repository reports a 106-module build for the first 100 pinned upstream
manifest entries and an axiom audit of 2,928 public OAI theorems. The record
explicitly leaves Results.Conclusions unverified. Those repository-reported
checks were not rerun here. This is a later checkpoint, not the same snapshot
as the selected research-file inspection. Its dependency audit does not certify
an entire progression proof or identify all distinct manuscript bounds.

## Direct predecessor

The complete earlier `sharp_cube_stability.tex` manuscript, dated 7 October 2026,
was read from the user's Library (666 file lines). Its full title is:

*Sharp local stability for additive cubes: Exact energy bounds, a sharp
subgroup-boundary inequality, and the deletion–addition transition.*

Important inspected parts:
- the normalization and universal local profiles;
- elementary rounding and its 1/60, 1/50 constants;
- the unrestricted coefficient 2^(k+1)-2;
- exact deletion and addition examples, including the singleton 2k example;
- the odd-order estimate with loss 35 delta^4;
- the odd-order exact-profile conjecture (Conjecture 12.1);
- the boundary inverse and odd-order boundary questions.

The exact integrated TeX filename was not inferred from an unrelated repository
listing. The Library manuscript supplies the statement being resolved; source
101's retrieved formalization plan confirms the corresponding repository route.

## Established literature

Tanja Eisner and Terence Tao, *Large values of the Gowers–Host–Kra seminorms*,
Journal d'Analyse Mathématique 117 (2012), 133–186, arXiv:1012.3509.
The abstract and bibliographic record were checked for the near-extremizer
context; none of its technical theorems is needed to prove the present results.

https://arxiv.org/abs/1012.3509
https://doi.org/10.1007/s11854-012-0018-2

W. T. Gowers, *A new proof of Szemerédi's theorem*, GAFA 11 (2001), 465–588,
is the contextual foundational reference, not an unproved input here.
https://doi.org/10.1007/s00039-001-0332-9

## Novelty distinctions

Reused with attribution: cardinality cube bounds and recursion; the energy–coset
characterization; the explicit rounding mechanism; the unrestricted boundary
recursion; the Boolean three-cube determinant census; the second-Bonferroni hole
estimate; singleton ternary examples and binary sharpness examples.

Advances relative to the predecessor: the exact odd-order cubic profile without
fourth-order loss; its occupancy/energy proof and finite quantitative rigidity;
a uniform local upper bound with coefficient 2k for all dimensions and all
quotients without two-torsion; quantitative boundary remainders and inverse
structure; resulting higher-dimensional odd-order local profiles.

The optimal first-failure comparison is proved and used here. Historical priority
for that comparison or for the package beyond the explicit predecessor has not
been certified by an exhaustive literature review. No claim that every recent
repository result was reviewed or independently established is made.
