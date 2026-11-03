# Conditional source-to-80-graph construction

`ScaledReverseGraph.graph_zero_of_source` is a Lean theorem for every model of
IΣ₁ in the imported framework. From the explicit hypotheses in its statement,
it constructs one positive valuation that makes the actual selected 80-operation
Lean graph's output zero. The hypotheses include an unscaled Pell interval,
rank and phase equations, a power equation, a size inequality, and a natural
transport equation. They are not discharged merely by stating that a 90-graph
valuation is zero.

The constructed valuation is `[v₀, v₁, v₂, i, T, v₅, v₆, n, η′, ζ′]`.
The fresh scaled Pell witnesses `η′, ζ′` need not equal the unscaled source
interval witnesses `eta, zeta`. The shared `i, T, n` and auxiliary witnesses
come from a single application of `reverse_data`. The first three slots and
slots 5 and 6 retain the source values; consequently the same `q`, `X`, `Y`,
rank and transport data are used internally in the construction. The theorem
conclusion exports existence of a positive zero, not those coordinate
equalities as separate conclusions. The parameter `p 1` remains arbitrary.
The proof binds the actual graph fields E, A, Q, V and Z and then uses the
imported cross-product/output theorem.

The accepted guarded run is `observations/graph-attempt09/`. Its output object
was `/tmp/scaled-reverse-graph-vb48va1n/ScaledReverseGraph.olean`, SHA-256
`b9c5f5fd35821e237cb3995b0dd34311b552147c26f2b0d58ad0c82e23d4c107`.
The accepted source and runner SHA-256 values are respectively
`4e08225410c6070945b0f21e9dcc3b0471d4f6d69802f3472851cc42687c5925` and
`25d358719352b31edfdf768d5c797ff05bd1e7078317fc3aade5c59c7f70dde0`.
The runner verifies selected direct-import paths and hashes before and after
Lean; its receipt retains provider pins and resource samples. Earlier
observations are failed scratch attempts, some with `sorry`, and are not proof
evidence. The accepted check reports only the listed standard Lean axioms and
no `sorryAx`.

The result is conditional model-level graph construction. It does not yet
prove that a 90-graph zero supplies these hypotheses, a machine/graph endpoint,
or an internal iPRA theorem. The external JSON/PDF and exact fixed coefficient
tuple remain separate binding obligations; in particular, the retained 80
coefficient at `p 1` differs from the symbolic 90 tuple. The run inherits the
documented limits on transitive object/source provenance, package and dynamic
dependencies; direct-import pins alone do not discharge them.
