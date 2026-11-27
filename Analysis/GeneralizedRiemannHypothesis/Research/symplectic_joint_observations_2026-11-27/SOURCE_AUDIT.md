# Source and novelty audit

Date: 27 November 2026.

## Pinned repository

Repository: https://github.com/VladimirReshetnikov/ProveIt

Commit: `6d284fcf75bc3a91bb2e79ba7636f94724bff62c`.

The requested directory was retrieved through the GitHub connector. The full Article section inventory was mapped and all 20 section files were retrieved. The main mathematical comparison concentrated on `Article/sections/spn.tex` and `Article/sections/src.tex`, supplemented by the article introduction, assessment document, formalization README, the newest relevant symplectic packets, and the exported upstream theorem statements. This was not an independent audit of every one of the article's 997 theorem-like statements.

The Article README reports 142 merged reports and 770 pages; the directory README lists 42 additional placed reports. Ten further ZIP files were present in `docs/incoming` at this snapshot. Source Git blob hashes were verified for 25 retrieved text files, including all article sections and the two inspected upstream statement files. Exact identifiers and SHA-256 values appear in `sources/manifest.json`.

## Direct mathematical starting points

`Article/sections/spn.tex` contains:

- `spn:thm:complete-law`: exact two-frame likelihood, relation-space refinement, and sharp minimum ambient dimension.
- `spn:lem:alt-gram`: finite alternating Gram statistics.
- `spn:q:symplectic`: remaining regimes and the distinguishing power of correlated observations.

`Article/sections/src.tex` connects this branch to the source proof's second-moment spanning lemmas and positive-type matrix estimate `New.card_mul_sum_det_eq_zero_le`.

The directly related incoming papers inspected were:

- `uniform_symplectic_blocks.zip`: uniform two-frame rectangular rank blindness.
- `rectangular_symplectic_blocks.zip`: two-frame rank and residual-defect joint laws.
- `grh-two-open-questions.zip`: exact optimal tests and limiting offsets for two nondegenerate frames, alongside a separate prime-variance paper.

The other successfully retrieved incoming ZIP text files were inventoried and scanned for relevant overlap. Their mathematical results were not all reverified.

## Explicit coverage limitation

`Analysis/GeneralizedRiemannHypothesis/docs/incoming/grh_uniform_extensions_2026-11-27.zip` was identified at Git blob SHA `fcddc0beadb909de6850ca2ba3bab403095f7239`, size 1,073,938 bytes. The contents API returned an empty base64 payload, and the blob interfaces attempted UTF-8 decoding of binary ZIP data and failed. The archive is **unreviewed**. No claim of non-overlap with its contents is made.

## Upstream premise

The vendored `Main.lean` exports RH and GRH for Dirichlet L-functions. The upstream revision is `72fead102f663d5c7a407964a13dc0cf9d977207`.

Andrew Sutherland's primary verification page, https://math.mit.edu/~drew/shortgrh/, updated 27 November 2026 at 17:27 UTC, reports completed kernel replays, axiom checks, independent checker runs, and comparisons of the theorem statements. We read that current record and the source exports. We did not rerun those upstream builds or kernel checks. The new theorems in this packet use no analytic RH or GRH assumption.

## External primary literature inspected

1. Jason Fulman and Larry Goldstein, *Stein's method and the rank distribution of random matrices over finite fields*, Annals of Probability 43 (2015), 1274–1314, DOI 10.1214/13-AOP889. Related rank distributions and total-variation methods.
2. Tiange Li, Yinan Li, Youming Qiao, Dacheng Tao, and Yingjie Wang, *On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields*, arXiv:2604.00591v2, https://arxiv.org/abs/2604.00591. Proposition 5.2 treats symmetric random Gram matrices over odd fields, using a rank-enumerator formula for chi-square divergence. It is an important predecessor to the general idea of Gram-law uniformity.
3. Tom Farshi, Daniele Toniolo, Carlos E. González-Guillén, Álvaro M. Alhambra, and Lluis Masanes, *Mixing and localization in random time-periodic quantum circuits of Clifford unitaries*, Journal of Mathematical Physics 63 (2022), 032201, DOI 10.1063/5.0054863. Primary record: https://discovery.ucl.ac.uk/id/eprint/10146567/ ; author manuscript: https://arxiv.org/abs/2007.03339. Related finite binary symplectic submatrix bounds.
4. Jimmy He, *Random walk on the symplectic forms over a finite field*, Algebraic Combinatorics 3 (2020), 1165–1181, https://www.numdam.org/articles/10.5802/alco.131/ . A different transvection-walk cutoff, not this simultaneous frame observation law.
5. OpenAI, *A counterexample to Sidorenko's conjecture*, September 23, 2026, Proposition 5.3. Triple Lagrangian-subspace profile/orbit counts are related prior work, rather than the framed full-block likelihood and dimension threshold here. Pinned source: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/A-counterexample-to-Sidorenkos-conjecture-September-23-2026/paper.pdf .

## Proposed contribution and qualification

The proposed contribution is the exact joint law for an arbitrary number of prescribed-form symplectic frames; its efficient kernel polynomial; its constructive simultaneous realization criterion; a uniform threshold with explicit bounds controlled by total frame dimension; and the resulting hierarchy in which every proper frame marginal is nearly uniform while the full law is nearly separated.

The precise combined theorem was not located in the inspected repository material or targeted primary literature. This supports a new extension relative to the inspected project. It is not a proof of worldwide novelty. The classical fact that pairwise independence does not imply joint independence is not itself claimed as new. Forest independence follows from a standard transitive-orbit argument; its role here is to make the matrix example exact at the pairwise level.

The threshold bounds leave a bounded critical-window profile open. The exact likelihood is computable, but counting all invariant strata at increasing dimension is a separate problem. No further general RH, Artin conjecture, or arithmetic conjecture is claimed.

## Verification boundaries

Three derivations and two independently implemented likelihood computations were compared within this research session. The review notes are internal mathematical checks, not external peer review. The artifact contains written proofs and exact finite tests, and does not contain a claimed Lean formalization.
