# Source and novelty audit — October 7, 2026

## openai/math

Reviewed the repository overview/README and the source of the preprint **Quasipolynomial Bounds for Arithmetic Progressions**, dated September 23, 2026:

- `preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/build/main.tex`
- `preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/build/sections/01-setup.tex`

The GitHub API reported commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, dated October 6, 2026. The source announces strong global progression conclusions; the repository cautions that verification status varies. This package neither verifies nor depends on those conclusions. The weighted higher-order setting is motivational.

## VladimirReshetnikov/ProveIt

Reviewed the root, Ramsey research directories, and `Combinatorics/Ramsey/FORMALIZATION_STATUS.txt`. The status material distinguishes finite weighted identities and stability lemmas from residual hypotheses and unfinished multiscale interfaces.

An API commit read returned `d021a5efa3b08bf3bacd16b5b31669c4820e9796`; a tree read returned `fb9602e556560a15704b4feb176ba6de08378665`. The metadata and returned main-branch content did not establish one consistent immutable snapshot. These two identifiers are not interchangeable. A directory listing exposed a `sharp-local-cube-stability` name, but subsequent direct directory retrieval returned 404, including a retry against `main`. No successful direct repository read of that folder is claimed.

## Precisely identified predecessor

Independently retrieved from the user's Library:

**Sharp local stability for additive cubes: Exact energy bounds, a sharp subgroup-boundary inequality, and the deletion–addition transition**, dated October 7, 2026, source filename `sharp_cube_stability.tex`.

The earlier manuscript contains the explicit source label `conj:oddexact`, asking for the loss-free cubic odd-order local profile. Its preceding estimate carries a `-35 delta^4` error. That concrete open question, rather than a vaguely attributed literature conjecture, is resolved in this package. The Library artifact was read as a source; it is not redistributed and is not falsely assigned an immutable Git commit.

## External literature

- Tanja Eisner and Terence Tao, *Large values of the Gowers–Host–Kra seminorms*, J. Anal. Math. 117 (2012), 133–186, arXiv:1012.3509, DOI 10.1007/s11854-012-0018-2. General near-extremizer background, not a source of the exact polynomial identity proved here.
- Ben Green and Terence Tao, *An inverse theorem for the Gowers U^3 norm*, arXiv:math/0503014. Background only; the current arXiv record notes a correction to a general-group formulation. No theorem from it is used in the proof.

Primary repository and author/arXiv sources were used for mathematical context. Targeted searches for additive-cube stability, odd-order exact profiles, and near-extremizer results did not locate the exact identity derived here. That bounded search is not an exhaustive priority investigation.

## Scope of the result

The proof is self-contained and does not assume any major unverified claim in either motivating repository. The most concrete novelty claim is the resolution of the expressly stated predecessor conjecture, together with the weighted exact decomposition and the consequences written out in the article. Wider priority remains subject to review.
