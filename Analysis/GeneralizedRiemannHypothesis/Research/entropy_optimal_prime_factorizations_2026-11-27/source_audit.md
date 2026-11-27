# Source audit — 27 November 2026

Access method: GitHub connector (`fetch` for directory listings and `fetch_file` for source). Repository: `VladimirReshetnikov/ProveIt`, branch `main`. Below are exact blob IDs returned with the source at the time of reading. The branch is mutable; these blob IDs identify the consulted content. No repository changes were made.

## Vendored input

Prefix: `Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/`.

| File | Git blob SHA | Use |
|---|---|---|
| `README.md` | `a04f66a62af93fc0757f2aa573f3b053fde51bfa` | Vendor provenance and separate Lake build |
| `grh/README.md` | `68cd862687bac1dadf3f14dc7266365e5c8b1ec4` | Reported theorem scope, axioms and verification |
| `grh/src/Statements.lean` | `1cd1bce93344065936b2b392b23306254e0785ef` | Exact Mathlib-based statements |
| `grh/src/Main.lean` | `1adf4187a938510363cdb0dde0a6d628ff39c600` | Exported theorems |
| `grh/src/New/Reduction/OneSidedBound.lean` | `99e5240de112527b739068b692e5007720d310c1` | Ramp-smoothed prime remainder, main inequality and reduction architecture (introductory portion) |

Vendor README identifies upstream commit `72fead102f663d5c7a407964a13dc0cf9d977207` (25 Nov 2026). Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. The source reports only `propext`, `Classical.choice`, and `Quot.sound` for its exports. This research note did not rebuild or replay the source, verify those axioms independently, or formalize its own new theorem. Dirichlet GRH is accepted as input, not re-established here.

The precise useful exports are `LFunction_ne_zero_of_half_lt_re` and `LFunction_eq_zero_re`, with `riemannHypothesis` available for RH. The analysis applies only to ordinary Dirichlet L-functions; it does not assert a new RH for a larger family.

## Merged article

Prefix: `Analysis/GeneralizedRiemannHypothesis/Article/`.

| File | Git blob SHA | Use |
|---|---|---|
| `README.md` | `7f3286088c94a8df3d8b9846112ea83dbbbbfa25` | Corpus size and verification status |
| `article.tex` | `2d95d3db42756d4dcea77ecd304c92ded01ad7c6` | Structure |
| `sections/abstract.tex` | `649adf939b67e9807d87854cec0668016868c2d6` | Scope |
| `sections/intro.tex` | `b68b38b12772e23ffae3a25a1d449881435a4e5c` | Status distinctions and relationships |
| `sections/src.tex` | `f69668b2f95261630bb1282c2cc1f9c172b7e530` | Input statement and source mechanism (relevant opening portion) |
| `sections/dir.tex` | `da58d506e24a05e1b888da2802398f277d9ea727` | Related theorem statements, bias proof, mixed-modulus counts and open questions |
| `sections/ana.tex` | `f05f1cbf50dee52273e72b76f7b0f5aa2f3e51ce` | Heading-level overlap check |
| `sections/li.tex` | `87871b581808b4388135617b7d38cae1438bece5` | Heading-level overlap check |
| `sections/zer.tex` | `1f1e31367ea4fdd259786e3997d46ecd279d5cbc` | Heading-level overlap check |
| `sections/rec.tex` | `da56d6ad5a1a699e335dcfd327bcdc9492c64017` | Heading-level overlap check |
| `sections/spn.tex` | `886e8716472aa82fd45ff68da03be946e9dbd3da` | Heading-level overlap check |

Relevant labels: `dir:lem:bias`, `dir:thm:quotient`, `dir:thm:short`, `dir:thm:factorization`, `dir:thm:minority`, `dir:thm:factorlower`. The direct-arithmetic section treats stronger robustness and relative-count guarantees at larger unspecified constants. This note instead computes the optimal leading constant for support at fixed mixed moduli; it does not inherit those other guarantees.

Repository links:
- https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean
- https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/GeneralizedRiemannHypothesis/Article
- https://github.com/VladimirReshetnikov/ProveIt/blob/main/Analysis/GeneralizedRiemannHypothesis/Article/sections/dir.tex

## External comparison and analytic input

- Montgomery & Vaughan, *Multiplicative Number Theory I: Classical Theory*, CUP 2007, Thm 13.11, Eq. (13.28), p. 428. This exact integrated character bound was verified in retrieved text of the book. It is the sole GRH-dependent estimate in the proof. The prime number theorem and finite group Fourier analysis are standard unconditional results.
- Booker & Pomerance, *Squarefree smooth numbers and Euclidean prime generators*, Proc. AMS 145 (2017), DOI 10.1090/proc/13576; https://arxiv.org/abs/1607.01557
- Munsch & Shparlinski, *On smooth square-free numbers in arithmetic progressions*, JLMS 101 (2020), DOI 10.1112/jlms.12297.
- Erdős & Rényi, *Probabilistic methods in group theory*, J. Analyse Math. 14 (1965), 127–138. https://www.renyi.hu/~p_erdos/1965-15.pdf
- Ma & Tang, *An Erdős problem on random subset sums in finite abelian groups*, https://arxiv.org/abs/2602.05768 (2026).

Search was targeted and not a systematic review. No claim of established publication priority is made. The new argument is fully included, and can be reviewed independently of the novelty claim. The full 723-page article and 300,000-line Lean project were not exhaustively audited.
