# Source audit and literature boundary

## Repository checkpoint

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected commit: `7d99e5deeb209a4671060990cb1ea3d672d57064`.
The GitHub commit endpoint reports 2026-10-06T19:47:40Z.

Relevant source directories supplied by the user:

- `Combinatorics/Ramsey/Papers/sz-thm-gowers-proof`
- `Combinatorics/Ramsey/Lean/GowersSzemeredi`

Repository content was read through the connected GitHub interface. No write
operation was performed. This audit is a source inspection, not a successful
local build of the repository.

## Inspected definitions and theorem implementation

The following two files were fetched with the exact commit above as their ref:

1. `Combinatorics/Ramsey/Lean/GowersSzemeredi/Definitions.lean`
   - Blob: `97113b7afa6925a2dd4b76641eeaeff09597ab6a`.
   - Relevant definitions: `fourier`, `balanced`, `cubeDifference`,
     `UniformOfDegree`, `UniformSetOfDegree`, `gowersNorm`, `cubeForm`,
     `AdditiveCube.vertex`, `cubeCount`.
2. `Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs03CubeUpper.lean`
   - Blob: `c017515bdd43b3c7dd8a5d0e90747a20403d4ddc`.
   - Proves `lemma_3_10_holds` using the unnormalized indicator/constant
     norm powers and `gowersNorm_add_le`.
   - Imports `Proofs03Minkowski` and `Proofs03Cubes`.

Additional default-branch reads during the inspection:

3. `Combinatorics/Ramsey/Lean/GowersSzemeredi/Sections01_03.lean`
   - Returned blob: `f9fcd166af0ea5a8e8c674576c1e47f3705485cd`.
   - Records the proposition-valued `lemma_3_10` statement.
4. `Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs01_03.lean`
   - Returned blob: `e72f7bd53a23d5880cbddbfebd0664d529e47c10`.
   - Contains the Fourier identities, including Parseval and additive
     quadruple energy. This was inspected as supporting infrastructure;
     the main audit does not claim a local build.

The source-paper directory listing returned the TeX blob
`41085a0efde8c1932e86e80c791984f52841c22e`. The paper's relevant printed
Lemma 3.10 was also checked in the public primary PDF below, including a
rendered view of printed page 485 (PDF page index 20).

## Public primary sources checked

- W. T. Gowers, *A new proof of Szemeredi's theorem*, GAFA 11 (2001),
  465-588, DOI 10.1007/s00039-001-0332-9.
  https://www.cs.umd.edu/users/gasarch/TOPICS/vdw/sz-thm-gowers-proof.pdf
- Hamed Hatami, *On generalizations of Gowers norms and their geometry*,
  arXiv:0903.3237. https://arxiv.org/abs/0903.3237
- James Leng, Ashwin Sah, Mehtaab Sawhney, *Improved Bounds for Szemeredi's
  Theorem*, arXiv:2402.17995. https://arxiv.org/abs/2402.17995
- Luka Milicevic, *A quasipolynomial inverse theorem for the U^k(F_p^n)
  norm in the high characteristic*, arXiv:2609.33733.
  https://arxiv.org/abs/2609.33733
- Ruizhe Shi, Yiqi Dong, *An Improved Upper Bound for Colorings Without
  Symmetrically Colored k-Term Arithmetic Progressions*,
  arXiv:2607.20752v2, dated 24 August 2026.
  https://arxiv.org/html/2607.20752v2

The 2026 items are cited as primary preprints with their stated results.
The manuscript does not claim independent verification of their complete
proofs. It does not relabel their progression-conjecture results as new work
of this package. No exhaustive literature search can establish historical
originality of the local cube identities; that question is expressly left
unsettled.

## Verification status of this package

- Exact finite-group coefficient checks: executed; all 24 passed.
- Stirling identities: checked exactly for d=2,...,14.
- Two-frequency U^3 polynomial: all 390625 assignments checked exactly.
- Small-cube Smith-normal-form censuses: executed; all assertions passed.
- Determinant-5 and kernel certificate: checked exactly.
- LaTeX: compiled with pdflatex/latexmk.
- PDF: rendered and visually reviewed; no mathematical content is in an
  external figure, image, or font file that the user must obtain separately.
- Lean verification of new results: not performed.
