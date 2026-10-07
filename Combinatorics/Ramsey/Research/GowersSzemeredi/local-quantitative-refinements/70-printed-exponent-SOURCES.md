# Sources and provenance

## Scope

All ProveIt snapshots use immutable commit `95460768cc4015862fec316f83df5861b04d28bc`. The repository dependency manifest pins Mathlib at `81a5d257c8e410db227a6665ed08f64fea08e997`; the Mathlib DFT snapshot uses exactly that dependency commit. The package independently recomputes each stored file's byte length, SHA-256, and Git blob SHA-1, using `SHA1("blob " + decimal_length + NUL + original_bytes)`. No newline normalization is performed during packaging.

`provenance/source_manifest.json` is curated metadata, not raw tool output. Its URLs bind repository, path and commit. The offline verifier checks this binding and the stored bytes; it does not contact GitHub, compile Lean, establish a complete dependency closure, or audit theorem axioms. The snapshots preserve the source text for inspection of the cited mathematical interfaces, including their own caveats and imports.

## Main interfaces

- `Definitions.lean`: proper progression, negative-sign unnormalized Fourier transform, and uniformity definitions
- `Sections12_13.lean`: the Section13 context, stages, polynomial bilinearity and fixed Theorem13.12 target
- `Proofs13InitialProgression.lean`, `Proofs13QuadraticRecurrence.lean`: initial analytic progression and weighted critical-height interfaces
- `Proofs13UniformDensityParameters.lean`, `Proofs13UniformEdgeModels.lean`, `Proofs13DenseEdgeModels.lean`: actual-density and rounded-radius facts, plus all-density scalar Bohr models
- `Section10.lean`, `Proofs10ProgressionLinearity.lean`: the short-difference scalar-linearity interface
- `Proofs13CommonStepSelection.lean`: constructive common-step row selection; its old hardcoded Bohr wrappers cannot be used unchanged with the new row length
- `Proofs13CompleteRowExtraction.lean`, `Proofs13IndexedRowExtraction.lean`: all-scale row extraction and the related indexed span interface; the article also supplies the direct short-parent geometric argument
- `Proofs13CoefficientExtraction.lean`, `Proofs13CoefficientPartition.lean`: coefficient extraction and the localized all-scale bilinear-cell theorem
- `Proofs13ContextExtraction.lean`, `Proofs13FourierSquareExtraction.lean`: original-phase context extraction, actual density, retained mass and Fourier assembly
- `Proofs13AllDensityExtraction.lean`, `Proofs13UniformSquareExtraction.lean`: source all-density and density-uniform comparison interfaces
- `Mathlib_Fourier_ZMod.lean`, `lake-manifest.json`: exact DFT normalization and its pinned dependency

## Selected exact snapshots

- [Definitions.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/95460768cc4015862fec316f83df5861b04d28bc/Combinatorics/Ramsey/Lean/GowersSzemeredi/Definitions.lean)
  - 15,504 bytes; Git blob `97113b7afa6925a2dd4b76641eeaeff09597ab6a`
  - SHA-256 `17241a9ffa53e2c6b335eb326920952a7f3da25e5e5a601a7aca5606462f5e4b`
- [Mathlib_Fourier_ZMod.lean](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Analysis/Fourier/ZMod.lean)
  - 9,097 bytes; Git blob `101a428d82866a93cba10e85c589fe38864a212e`
  - SHA-256 `0735a2370e6a0fb62fed50660757914a01400c19b6f66a1d768c71b907d972c9`
- [Proofs10ProgressionLinearity.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/95460768cc4015862fec316f83df5861b04d28bc/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs10ProgressionLinearity.lean)
  - 6,948 bytes; Git blob `f51c55910b85bc762dd9cd57b4b7f15ea8660499`
  - SHA-256 `a4d443a9c6563df42bc1f9fc458d77a3108ea00cd9e0301744732355c037c9af`
- [Proofs13AllDensityExtraction.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/95460768cc4015862fec316f83df5861b04d28bc/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs13AllDensityExtraction.lean)
  - 3,655 bytes; Git blob `f36393ca017aa5e7daac296a58760adf231eb9f2`
  - SHA-256 `41a29e4e73e77185c7c016a8b0af83880a4e83077c46d10d55c49f9dbaf0eaab`
- [Proofs13CoefficientExtraction.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/95460768cc4015862fec316f83df5861b04d28bc/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs13CoefficientExtraction.lean)
  - 4,122 bytes; Git blob `9903ff2c5e6f4095ed66b9cfa13762e729ee4e92`
  - SHA-256 `b5a26a0306e387aed555854825e503ed1ca1437ba8f72167fc1d401def467bdd`
- [Proofs13CoefficientPartition.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/95460768cc4015862fec316f83df5861b04d28bc/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs13CoefficientPartition.lean)
  - 12,598 bytes; Git blob `a87abd980abfe1005b3e93a7d7f36b5138a24897`
  - SHA-256 `4da1cbff5acc05fcb11bb4e6b75d4c95463a1c2d9999b564a1269e5575f111ff`
- [Proofs13CommonStepSelection.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/95460768cc4015862fec316f83df5861b04d28bc/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs13CommonStepSelection.lean)
  - 11,904 bytes; Git blob `64b24185597da4f9505a13693d56635f96906cda`
  - SHA-256 `ec870b3bceda885eb5e67bd48c14b53290d322bd74905c2a8bba442899f1aa5c`
- [Proofs13CompleteRowExtraction.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/95460768cc4015862fec316f83df5861b04d28bc/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs13CompleteRowExtraction.lean)
  - 2,426 bytes; Git blob `cd319ad022b37f0daeba2e506d3d02c64f4bbe9e`
  - SHA-256 `f0bcfc7913e27d811d8c001d396e828ccde24a11f8cb0c6831c8f6300e9664d5`
- [Proofs13ContextExtraction.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/95460768cc4015862fec316f83df5861b04d28bc/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs13ContextExtraction.lean)
  - 32,417 bytes; Git blob `42aac1bc5b9702c4abf61bc54b3a4f041e4d1fab`
  - SHA-256 `695c4672084f298a1527c9a7d357bd4ab88b3ea31200e80eb164759f1e3e2892`
- [Proofs13DenseEdgeModels.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/95460768cc4015862fec316f83df5861b04d28bc/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs13DenseEdgeModels.lean)
  - 9,074 bytes; Git blob `9945ff83c9b55912013d828289b8f02ae942e9c9`
  - SHA-256 `ea10b3f0ff83e62d75eeca5e9ef63511191b2b0133dedf80568b1466389aee50`
- [Proofs13FourierSquareExtraction.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/95460768cc4015862fec316f83df5861b04d28bc/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs13FourierSquareExtraction.lean)
  - 4,245 bytes; Git blob `cf0d04dbc84041bf522fa89f7901b1201b16aae6`
  - SHA-256 `9816935a1099a95796287d7fe786a9a709baa0424631bf68810c1f35f1f0174c`
- [Proofs13IndexedRowExtraction.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/95460768cc4015862fec316f83df5861b04d28bc/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs13IndexedRowExtraction.lean)
  - 4,099 bytes; Git blob `f870f074457163ac84e9dbae14b1968a908f84fa`
  - SHA-256 `e25689717db3aa6a0524b839661d7b315d3b65d8f3f33f45f244c28d24ee3412`
- [Proofs13InitialProgression.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/95460768cc4015862fec316f83df5861b04d28bc/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs13InitialProgression.lean)
  - 62,335 bytes; Git blob `915f11a363b23cd565df77e5ce85bc6518cadd75`
  - SHA-256 `a5702e827134b740fc5db793991c60549fc1af46f8169c84bd70a00a8a381b65`
- [Proofs13QuadraticRecurrence.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/95460768cc4015862fec316f83df5861b04d28bc/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs13QuadraticRecurrence.lean)
  - 18,416 bytes; Git blob `d81ea5384a8ef59127054ab1eb490e86bfb0d6f2`
  - SHA-256 `5c8778017c93cc316989aba95cf9d0c3511e2c507f5843030cb1c9bb498cc9da`
- [Proofs13UniformDensityParameters.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/95460768cc4015862fec316f83df5861b04d28bc/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs13UniformDensityParameters.lean)
  - 9,135 bytes; Git blob `9cd948c5b3b8fbb926df8df5421f833b0271fee4`
  - SHA-256 `4c425f0569c6605e8e16a068155c635ece7d1e09b590faf9455a4312b2a4c5b1`
- [Proofs13UniformEdgeModels.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/95460768cc4015862fec316f83df5861b04d28bc/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs13UniformEdgeModels.lean)
  - 7,361 bytes; Git blob `4bb47ae8b6f6b3f8728a03feb52bac4027547725`
  - SHA-256 `262fccb05196b05389f7456e49a150b212631f73bb0a5929d460600dd8f98bcc`
- [Proofs13UniformSquareExtraction.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/95460768cc4015862fec316f83df5861b04d28bc/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs13UniformSquareExtraction.lean)
  - 4,857 bytes; Git blob `31d4c858f6761dca4ff71b2770e35f9863cc7c7e`
  - SHA-256 `5136674d3eebc4d74b8bcf383753e48c083c81afbd3e16602e256e174e76fb56`
- [Section10.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/95460768cc4015862fec316f83df5861b04d28bc/Combinatorics/Ramsey/Lean/GowersSzemeredi/Section10.lean)
  - 24,924 bytes; Git blob `302e8a223f56dcdabf29f30ca3c80ac62a7adbfc`
  - SHA-256 `8b63d784485ba8291b614a9153399cae216d2adaf37c9770344521083523cb2d`
- [Sections12_13.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/95460768cc4015862fec316f83df5861b04d28bc/Combinatorics/Ramsey/Lean/GowersSzemeredi/Sections12_13.lean)
  - 28,878 bytes; Git blob `1de556b791c7dac188d91f554231b11e2cf31cea`
  - SHA-256 `6e6318bcce96a0e2023f6743d9c52cc1f9bd6b416beeeec6c3841916334743d8`
- [lake-manifest.json](https://github.com/VladimirReshetnikov/ProveIt/blob/95460768cc4015862fec316f83df5861b04d28bc/lake-manifest.json)
  - 3,141 bytes; Git blob `dc6d553da8d0ca6a9ad926545920d21f9dc6b4c7`
  - SHA-256 `95e215b005fe9aacc1e5490c781d57e3044d2da5ca452495cfcd0e4eff908665`

## Separate bounded status check

A single bounded repository-status check on 7 October 2026 at approximately 02:50 UTC used the separate snapshot `7d0199a11c8b1420e4e47acac4d9a12f541f915c`. This is a status observation, not the proof pin. The [status catalogue at that snapshot](https://github.com/VladimirReshetnikov/ProveIt/blob/7d0199a11c8b1420e4e47acac4d9a12f541f915c/Combinatorics/Ramsey/gowers-proof-status.json), Git blob `43534cd4aaaa42dac5d4f7f84539293b326b3157`, marked `theorem_13_12` open, listed no exact companions, and listed its extraction-exponent, explicit-bound and odd-square relatives. The target `Sections12_13.lean` still had blob `1de556b791c7dac188d91f554231b11e2cf31cea`, identical to the proof-pin snapshot included here.

Reading those listed companion sources and a bounded directory/search check found no implementation of this exact near-maximal interface. This is not evidence of exhaustive absence, a kernel audit or a priority claim. The offline builder checks only the bundled proof sources and their dependency pin; it does not reperform this later status observation. The raw status retrieval, directory listing and full connector response are not included in the package.

## External mathematical inputs and source attribution

These references are links, not bundled papers. The article states the precise hypotheses it imports. Hash verification of Lean interfaces does not prove their analytic dependencies or any external recurrence input.

- Cheuk Fung Lau, Theorem 1.1, [arXiv:2407.01611v1, p.2](https://arxiv.org/pdf/2407.01611v1#page=2), with [versioned full-text HTML](https://arxiv.org/html/2407.01611v1). The quadratic specialization uses epsilon=1/16 and M=6, giving `2 c2 <= 685/32 < 22`. The coefficient- and tolerance-uniform starting threshold remains unspecified.
- James Maynard, Theorem 1.1, [Simultaneous small fractional parts of polynomials, GAFA 31 (2021), 150–179](https://link.springer.com/article/10.1007/s00039-021-00559-3); [published full text](https://d-nb.info/1234805944/34) and [arXiv:2011.12275v1](https://arxiv.org/pdf/2011.12275v1). The optional published-only variant has an unspecified absolute quadratic exponent constant and requires the downstream repairs stated in the article.
- Tanja Eisner and Terence Tao, [Large values of the Gowers–Host–Kra seminorms, arXiv:1012.3509v2](https://arxiv.org/pdf/1012.3509v2), Theorem 1.1(2), Remark 1.6 and Section 2. This is an antecedent for phase normalization, separation and cocycle extension. No unspecified constant from that paper is used for this article's explicit near-maximal interval.
- The existing [canonical own-step certificate at the main pin, lines 6894–7183](https://github.com/VladimirReshetnikov/ProveIt/blob/95460768cc4015862fec316f83df5861b04d28bc/Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/article.tex#L6894-L7183) supplies the source-attributed finite partition mechanism. Neither the complete canonical article nor an extracted copy of its text is included here.
- The [literal paper-source Theorem13.12 paragraph, lines 2893–2895](https://github.com/VladimirReshetnikov/ProveIt/blob/95460768cc4015862fec316f83df5861b04d28bc/Combinatorics/Ramsey/Papers/sz-thm-gowers-proof/sz-thm-gowers-proof.tex#L2893-L2895) is distinguished from the sufficiently-large-prime quantification of the pinned Lean target.

The package makes no exhaustive literature or moving-branch absence claim, no novelty certificate, and no claim that the stronger printed-exponent conclusion is exported by a Lean theorem in these snapshots.
