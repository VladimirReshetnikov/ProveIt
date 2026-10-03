# Source and proof-dependency audit

## Repository

Repository: https://github.com/VladimirReshetnikov/ProveIt

Observed main-branch snapshot:

    6996fee43cc97b6c16351def7507d59a95bf62f0
    2026-09-30T16:07:39Z

Selected documentation was read through the GitHub connector on
30 September 2026:

- README.md
- Algebra/SurrealNumbers/README.md
- Algebra/SurrealNumbers/docs/README.md
- Selected directory and branch metadata.

The large recursive-tree response was truncated. The audit is not an
exhaustive search of the repository, and no independent Lean build was run.
The article treats the documented field foundations as context, not as a
claim that the present theorems have already been formally checked.

## Prior user research

The research library supplied the title and abstract of:

*Finite Convexity and Exact Lexicographic Optimization over the Surreals:
A finite-dimensional theorem package and a one-objective compiler for
multiscale linear programs*, research draft dated 22 September 2026.

The visible library filename was `article(20260923-000126).pdf`. Its
presence in the current repository tree was not established. It is cited
to avoid presenting finite Farkas theory, finite convexity, or exact
lexicographic compilation as gaps or new contributions here.

## Classical mathematical inputs

- Gonshor, *An Introduction to the Theory of Surreal Numbers* (1986):
  surreal field foundations and finite normal-form arithmetic.
  https://doi.org/10.1017/CBO9780511629143
- Fiorini, Rothvoss, Tiwary, *Extended formulations for polygons*:
  generic LP lower-bound mechanism and special compact polygon lifts.
  https://arxiv.org/abs/1107.0371
- Kaibel, Pashkovich, *Constructing Extended Formulations from Reflection
  Relations*: the general reflection framework.
  https://arxiv.org/abs/1011.3597
- Yannakakis, *Expressing combinatorial optimization problems by linear
  programs* (1991): nonnegative slack factorization correspondence.
  https://doi.org/10.1016/0022-0000(91)90024-Y
- Gouveia, Parrilo, Thomas, *Lifts of convex sets and cone factorizations*:
  conic slack factorization correspondence.
  https://arxiv.org/abs/1111.3164
- Gouveia, Robinson, Thomas, *Worst-Case Results for Positive Semidefinite
  Rank*: generic PSD lower bound, with an Archimedean objective-selection
  step replaced in this manuscript by finite definability.
  https://arxiv.org/abs/1305.4600
- Fawzi, Gouveia, Parrilo, Robinson, Thomas, *Positive semidefinite rank*:
  normalization and lower-semicontinuity background.
  https://arxiv.org/abs/1407.4095
- Mahboubi, Cohen, *Formal proofs in real algebraic geometry: from ordered
  fields to quantifier elimination*: a formalized real-closed-field
  quantifier-elimination reference, not a Lean dependency already imported.
  https://arxiv.org/abs/1201.3731

## Candidate contribution

The candidate contribution is the explicit finite-support pair with
identical complete power-jet data and identical initial slack matrices,
unbounded LP and PSD lift-size ratios, a fixed-rank common field, the
sharp rank-two existence variant, and the stated precision/higher-
dimensional consequences. The underlying generic bounds, reflection
method, residue-closure idea, and transfer principle are not claimed new.

Searches combined surreal polytopes, surreal extension complexity,
nonnegative rank Hahn, and valuation/leading-term terminology. This
limited search did not establish priority or exhaust all related work.

## Proof status

The article contains written proofs with its imported classical theorems
identified. The verification script checks finite exact identities and
instances. No statement is represented as independently refereed or
Lean-verified. No file is presented as a successful Lean compilation.
