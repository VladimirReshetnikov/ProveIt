> Release binding: all new generated artifacts in this directory use the complete mixed-radix Wang943 tuple, B=2^(5^9), selected by COEFFICIENT_BINDING.json. Historical source tuples mentioned below document predecessors or valid alternatives, not the selected numerical instance. The sibling coefficients/COEFFICIENT_PROOF.md proves the full adapter and simultaneous canonical restrictions.

# Two-weight twelve-variable synthesis

The new polynomial uses twelve strictly positive integer unknowns, has exact
degree **1081**, and has a **120-operation** division-free circuit. It improves
both degree and operations over package 20's twelve-variable 1145/123 result.
It does not dominate package 21's 1353/116 point in operation count, and no
eleven-variable or globally optimal construction is claimed.

| Presentation | Variables | Equations | Degree | Operations |
|---|---:|---:|---:|---:|
| Product | 12 positive | 1 | 1081 | 120 |
| System, direct final comparison | 12 positive | 3 | max 1072 | 115 |
| Sum of squares | 12 positive | 1 | 2144 | 123 |

The new idea is to replace package 21's first-root weight L by a separate
M of smaller degree: W=2I(T+Raic), L=1+HW, M=2W. The rationality proof uses
uniform bounds on every complex conjugate, then the special Pell saturation
lemma restores integrality and the main congruence.

Read `TWO_WEIGHT_PROOF.md` for the full mathematical proof and exact leading
form. `TWO_WEIGHT_SECTION.tex` is an insertable report section. The executable
circuits are `two_weight_norm12_{product,system,sos}.json`.

Reproduce with Python 3 and its standard library:

    python build_two_weight_norm12.py
    python check_separation.py

The first emits all circuits and `TWO_WEIGHT_CHECKS.json`; the second writes
`SEPARATION_CHECKS.json`. Tests include exact eight-conjugate multiplication,
parity, liveness, degree diagnostics, 500 exact bound cases, and 18 isolated
completeness fixtures. They do not construct a K215 halting witness or replace
the semantic proof.

The default is one complete package-20 coefficient tuple. A sibling
`COEFFICIENT_BINDING.json` can replace the entire binding after a proved
compiler transfer. It must contain tuple_id, tuple_sha256, recipe, and aliases
exactly {beta: beta, K0: K, MC: MC, MF: MF_source}. This is a binding override,
not permission to splice individual coefficient ports.

All upstream sources were fetched with the GitHub connector at commit
`ae3007ca4467011e0e051c84acb4a1dd13971b0e`. `SOURCE_PROVENANCE.json`
records their original Git blob hashes and verified byte-exact local SHA-256s.
The builder is adapted from package 21's evaluator; its source and license
notices are retained under `sources/21-norm12/`. The new separation argument,
proof, fixtures, and report section are this synthesis's contribution.

This establishes an ordinary mathematical reduction formalizable in ZFC
through the inherited blank K215 compiler and calibration. It is not a new
end-to-end proof-assistant formalization or a proof of ZFC consistency.
