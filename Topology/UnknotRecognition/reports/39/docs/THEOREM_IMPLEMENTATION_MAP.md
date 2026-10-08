# Proof and implementation map

| Article result | Code/artifact | Boundary |
|---|---|---|
| Exact checkpointed SU(2) compiler (Theorem 4.1) | `multivariate.py`, `degrees.py`, generated `.wl` examples | Compiles the full exact formula; does not decide general real feasibility itself. |
| Rank–checkpoint–degree complexity (Theorem 4.4) | Degree preflight and explicit formula construction | Uses an established singly exponential existential-real decision algorithm, not implemented in this package. |
| Strict hybrid separation (Proposition 5.1) | `experiments/benchmark.py::mixed_presentation`, raw tradeoff data | Synthetic presentation DAGs, not claimed knot families or whole-pipeline timings. |
| Optimal tree checkpoints (Theorem 5.2) | `optimal_tree_cap`; exhaustive test against all trees through six leaves and five caps | Formula trees only. Shared-DAG optimizer is exhaustive and small-instance bounded. |
| Optimal fixed-seed propagation (Theorem 6.2) | `minimum_degrees`, `verify_profile` | Minimum unreduced derivation degree for fixed seeds, not minimum free word length or global minimum seeds. |
| Presentation preservation (Proposition 6.3) | `compile_seeds`, recorded figure-eight certificate | Relative to the supplied crossing system; production caller must validate its source knot diagram. |
| Visible-overpass quasi-polynomial class (Theorem 6.4) | Seed compiler plus the generic theorem | Diagram-visible parameter; no efficient bridge minimization is assumed. |
| Integer phase criterion (Theorem 7.2) | `dihedral.analyze`, exact certificates | Entire noncommuting traceless slice for two generators. |
| Compressed polynomial backend (Theorem 7.3) | `normal_forms`, `solve`, `verify` | Fully implemented algebraic decision, with resource caps. Topological interpretation requires verified knot/meridian provenance. |
| Two-seed polynomial diagram class (Theorem 8.1) | Bounded `find_small_seeds`, seed compilation, integer backend | The asymptotic statement uses exhaustive seed allowance. The package has no full production PD adapter. |
| Exact univariate decision (Proposition 9.1) | `univariate.py` | Independent reference formulation; can expand to exponential size on a short grammar and therefore preflights degree. |

The local replay routines share arithmetic with their producers. They are not
proof-assistant formalizations. Independent checking is provided by rational
quaternion evaluation, symbolic matrix compilation using SymPy, exact root
counts, a separate relaxation algorithm, exhaustive small tree choices, and an
exact Wolfram regression. Topological existence theorems are explicitly cited
external inputs rather than conclusions of the unit tests.
