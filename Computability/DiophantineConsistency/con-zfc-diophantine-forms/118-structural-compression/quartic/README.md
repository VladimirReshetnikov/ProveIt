# Direct C222 quartics with 68 nonnegativity predicates

The main output is the complete equation

    P(z_0,...,z_588)=0,  z_0,...,z_588 in Z.

It has exact degree 4, 8,156 nonzero monomials, and coefficient height
2,445,790,974,704. Both its 371 quadratic sum-of-squares residuals and
every expanded coefficient are supplied in `fused68/support8/`.
The source is the direct C222 calculus construction at ProveIt commit
`84e16e43092614bae262ca59651cb9d77e31a255`. Relative to its matched
75-predicate source, this saves 15 variables and 1,520 monomials with no
change in degree or coefficient height. No global minimality is claimed.

Two additional fully materialized alternatives trade variables for smaller
coefficients:

| Directory | Integer variables | SOS rows | Degree | Monomials | Height |
|---|---:|---:|---:|---:|---:|
| `fused68/support8/` | 589 | 371 | 4 | 8156 | 2445790974704 |
| `fused68/support32_quadratic_first/` | 595 | 377 | 4 | 7595 | 6956012 |
| `fused68/support16_affine2/` | 600 | 382 | 4 | 7075 | 964213 |

## Read the proofs

1. `PROOF_PAIR_GUARDS.md`: six interval-sign equivalences using retained
   common-bound witnesses; 75 predicates reduce to 69.
2. `PROOF_FUSED68.md`: a strict repeated-square output bound replaces two
   scalar signs; 69 predicates reduce to 68 and the principal polynomial
   has 589 variables.
3. `CALIBRATION_DEPENDENCIES.md`: exact immutable source interface and the
   named inherited C222/ZFC-refutation calibration, with its formalization
   boundary.

The new unbounded proofs restore every old predicate before using any
inherited semantics. Finite coefficient checks do not replace those proofs.
The ordinary equivalence is formalizable in ZFC; this packet does not
supply a new complete Lean build or an emitted object-ZFC proof.

## Independent check

Only Python's standard library is required. From this directory run:

    python3 -B check_fused68.py

This checks exact copied source hashes, all six row-sum identities, the
complete 69/68 guard replacement, all 22 square transitions, the carrier
identity, every monic substitution and integer inverse, every collected
quartic coefficient, and occurrence of every declared coordinate. It
imports neither producer nor optimizer. The result is written to
`CHECK_FUSED68.json`.

The original 69-predicate comparison suite can be checked with:

    python3 -B check_pair_guards.py

## Full regeneration

Run sequentially from this directory:

    python3 -B build_pair_guards.py
    python3 -B extra_profiles.py
    python3 -B build_fused68.py
    python3 -B check_pair_guards.py
    python3 -B check_fused68.py

`old75/` retains regenerated matched baselines, `pair69/` the intermediate
results, and `fused68/` the final equations. Copied optimizer and independent
projection-verifier sources are in `upstream/`; their original license is
included there. Every copied source is authenticated in
`SOURCE_PROVENANCE.json`.

## Sparse polynomial format

A term `[c,[i_1,...,i_k]]` means the integer coefficient `c` times
`z_(i_1)...z_(i_k)`. Repeated indices are powers, and the empty index list
is the constant monomial. Indices begin at zero. `equation.json` records
quadratic residuals whose squares are summed; `polynomial.json` records
the complete collected quartic. `projection.json` records the exact
integral restoration of deleted raw coordinates. None of the final
coefficient files contains an unevaluated power, a parameter port, or a
placeholder for a future computation.
