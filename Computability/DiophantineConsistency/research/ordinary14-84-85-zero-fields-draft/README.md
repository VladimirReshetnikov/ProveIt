# Signed zero-field extraction for the 84 and 85 graphs

`ZeroFields.lean` is an **unelaborated source-only draft**. For each graph
separately it proposes extraction of all five signed residual equalities from
that graph's own `InternalZero` statement. The third residual is `aux - 1`,
not `aux`; all five live in `DiffRing V`. The proposed proof unfolds the
literal output shape and applies the separately drafted arbitrary-model
`fiveSquares_eq_zero_iff` interface.

The theorem statements assert neither positivity of a witness valuation nor
any conversion of these signed equalities to natural Pell norms, carrier
balances, rank windows, or q-divisibility. Those graph-specific steps are still
needed for the arithmetic comparison. All imports, typeclass instances,
rewrites and tactics are uncompiled, and provider compatibility, the iPRA
endpoint and external file/PDF correspondences remain separate.

`python3 -I -S -B check_source.py` replays both graph generators and the
first-root draft receipt, inventories the five fields, and tests the
five-square zero condition on 3,125 bounded integer tuples. These finite
controls do not prove the arbitrary-model lemma or Lean elaboration; no Lean
is invoked.

Independent source review is recorded in
`../../reviews/ordinary14-84-85-zero-fields-draft-independent/`.
