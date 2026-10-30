# Independent replay of the 87-gate root factorization

The finite audit passed in separate normal and optimized Python runs. Both
produced the same candidate SHA-256
`da6b88365da3ec9db6040373c25de20b30baf63edc9fdf742de2aa4b2c06e6e8`
and the same 87-gate count (47 products, 22 additions, 18 subtractions),
with all 13 inputs and four ports live. It checks the pinned 88-gate parent,
the changed root block, unchanged surrounding gates, exact local sparse
polynomial identity, and rejection of a sign mutation. See the two retained
[audit records](adaptive-first-root-factor87-independent-evidence/).

An isolated generic Lean replay at `/tmp/adaptive-first-root-factor87-lean-go63gxwc`
and an isolated syntax replay at `/tmp/adaptive-first-root-factor87-syntax-cemx04n3`
passed all four modules. Each corresponding source, object, and complete log
hash matches the [author packet](adaptive-first-root-factor87-author.md).
The generic checks cover exact signed-pair equality over commutative semirings;
the syntax checks instantiate the repository's `Expr.splitNatural` evaluator
and preserve an arbitrary contextual zero test. Their axiom reports list only
`propext`. The syntax replay inherits the explicitly guarded recomposed
provider; Mathlib and the toolchain remain inherited boundaries.

The finite circuit audit plus the local Lean lemma do not establish the
complete 87-row expression equality in Lean. The actual one-hole expression
context, the full literal binding, nonstandard-model calibration and the
requested HA/PRA proofs remain separate work. The maintained equation and its
current record interface have not been replaced.
