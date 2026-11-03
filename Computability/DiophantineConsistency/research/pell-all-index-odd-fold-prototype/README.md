# Fold an arbitrary odd internal Pell index

`PellOddFold.fold_odd_index` proves in every IΣ₁ model that any odd internal index `s` folds to an odd `p ≤ n` when `n>0`, with ordinates signed-congruent modulo `xcoord n`. It uses the actual remainder modulo `2n`, the separately checked arbitrary-block antiperiod and reflection, and preserves odd parity. No proposed main Pell norm, `half_index`, or standard-index restriction is assumed.

The guarded author check `observations/attempt02/` passed without diagnostics, yielding `/tmp/pell-all-index-odd-fold-t52feqmz/PellOddFold.olean`, SHA-256 `853721216a20dbf04c1babafbbb79526d92db0aee5f3a6127625d86208bc3175`; attempt01 failed and is retained. Printed axioms are `propext`, `Classical.choice`, `Quot.sound`. Its runner pins selected prototype objects and one inherited provider, not the complete project/package/dynamic or historical source-object ancestry. Resource monitoring is sampled; no paired replay is claimed.

This gives a modular representative, not yet equality with an arbitrary target ordinate, a machine theorem, or an iPRA endpoint.
