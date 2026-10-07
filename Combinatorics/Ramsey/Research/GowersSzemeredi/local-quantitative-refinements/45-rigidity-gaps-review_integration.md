# Internal AI cross-check: normalization, interfaces, and source ledger

**Status.** This review was performed by an AI collaborator within the same preparation workflow. It is not a human peer review, an external referee report, or a Lean/kernel verification.

Reviewed `sections/integration.tex` and `sections/source_ledger.tex` against the inspected source files and the relevant consolidated statements. The source audit is pinned to commit `6ce33539ea468f51719a211c18aabdde262a24dd`.

## Verdict

The normalization conversion, including the factor `N^7`, is correct. The named Lean definitions and declarations match the inspected files. The main source-question links and the distinction between existing and newly proved comparisons are consistent with the consolidated article. No substantive mathematical correction is required.

One small precision improvement is recommended: specify `d>=1` in the general scaling identity, since the manuscript defines normalized `U^d` only in that range. The actual fourth-uniformity application uses `d=2,4` and is unaffected.

## 1. The `N^7` factor

In the repository, `gowersNorm d f` is the `2^d`-th root of the absolute value of the **unnormalized** cube sum, over one base point and `d` side variables. For a cyclic group of order `N>0` and `d>=1`, the cube sum is nonnegative and equals `N^(d+1) Q_d(f)`. Thus

\[
 \Gamma_d(f)=N^{(d+1)/2^d}\|f\|_{U^d}.
\]

In the two relevant dimensions,

\[
 \Gamma_2(f)^{16}=N^{12}\|f\|_{U^2}^{16},\qquad
 \Gamma_4(f)^{16}=N^5\|f\|_{U^4}^{16}.
\]

Multiplying the normalized inequality by `832 N^12` gives exactly

\[
 4795\Gamma_2(f)^{16}\le832N^7\Gamma_4(f)^{16}.
\]

The factor is on the correct side and has the correct exponent. It must not be deleted or replaced by `N^8`.

## 2. Uniformity degree and cube signs

The inspected definition is

```
UniformOfDegree f alpha n :=
  sum_a ||sum_s cubeDifference f a s||^2 <= alpha * N^(n+2).
```

The sum on the left is the unnormalized cube quantity in dimension `n+1`. Consequently degree `d-1` uniformity is precisely `Q_d(f)<=alpha`; there is no additional square or power of `N` in this conversion. `UniformSetOfDegree` applies that definition to the balanced indicator.

The repository's `cubeArgument` is `s - e dot x`, while `AdditiveCube.vertex` uses a plus sign. Replacing every side variable by its negative is a bijection and identifies the two sums. The integration section correctly describes this harmless sign conversion.

`cubeCount` counts every base-and-side tuple whose vertices lie in the set. It therefore includes degenerate cubes. The private lemma `gowersNorm_indicator_pow` in `Proofs03CubeUpper.lean` proves the indicator equality quoted in the manuscript. Calling it “proved locally” correctly avoids implying that this private declaration is directly available as a public import interface.

## 3. Existing declarations

The following names were found in the inspected source files:

* `Definitions.lean`: `cubeDifference`, `gowersNorm`, `cubeCount`, `UniformOfDegree`, `UniformSetOfDegree`.
* `Proofs03CubeUpper.lean`: `gowersNorm_indicator_pow` and `lemma_3_10_holds`.
* `Sections06_07.lean`: `theorem_7_2` and `proposition_7_3`, with energy hypotheses expressed through `Finset.addEnergy A A`.

The interface discussion explicitly disclaims a newly compiled Lean extension. That disclaimer is appropriate: these observations verify source-level compatibility, not formalization of the new theorems.

## 4. Consolidated source labels

The checked consolidated article contains the following labels with the stated content:

* `gsr:en:14:thm:energy-sharp-stability`: the sharp coset-distance envelope under `0<=epsilon<=1/100`, including uniqueness of the nearest coset.
* `gsr:fz:q:II:cosetrange`: the question asking for a larger universal range, coordinate splitting, and all exact envelope examples. The existing note already gives punctured-subcoset examples, so the new contribution is the full classification and enlarged range, not merely that construction.
* `gsr:en:14:thm:collision-sharp-stability`: the corresponding product-coset result under the same small-defect cutoff.
* `gsr:fz:q:III:normgap`: the higher real centered norm comparison, including source 03 Question 1, source 04 Question 3, and source 14 Question 11. It records the exact third-order constant and leaves higher orders open.
* `gsr:cc:04:cub:quartic`: the coefficient `P_d=2^(d-3)(3^d-2^(d+1)+1)`, with `P_4=100`, and attribution to the corresponding results in sources 03, 08, and 09.

The source ledger represents these existing claims accurately and does not attribute their proofs to the present manuscript.

## 5. Later-source qualification

The inspected repository README explicitly states that sources 15–23 had not yet been written into the consolidated article, while their supporting files were present. This supports the ledger's distinction between the consolidated sources 01–14 and the later supporting material.

The source-15 verifier was independently fetched through the GitHub connector at the pinned commit:

```
Combinatorics/Ramsey/Research/GowersSzemeredi/
local-quantitative-refinements/code/15-collision-amplification-verify.py
```

Its blob is `27bda011d0c095f760338e2e368dc6ce8891d0b0`. Its stability-certificate function explicitly requires `0<=eps<=Fraction(1,100)`. This confirms the narrow verifier statement in the ledger; it is not being treated as proof that no later-source theorem could have a different hypothesis.

This internal cross-check does not certify a line-by-line audit of every source 15–23 proof. The manuscript already states that limitation. Likewise, the source ledger's publication-priority paragraph is appropriately restricted to the primary sources actually inspected, and it expressly does not convert a limited literature search into a claim of global novelty.

## 6. Packaging consistency

The ledger promises `data/source_manifest.json` with exact blob identifiers. That file must be present in the delivered package and agree with the pinned commit and paths. At the time of this review the mathematical sections were complete while the packaging manifest was still being assembled; this review does not claim that the final archive has independently been inspected.

The U4 certificate command and its `certificates/` destination are separate from that source manifest. Keeping the mathematical verification data and the source-identity manifest as distinct files is consistent with their different purposes.

