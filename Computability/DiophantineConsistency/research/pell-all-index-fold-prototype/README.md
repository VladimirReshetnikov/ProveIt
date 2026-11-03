# Internal Pell antiperiod and reflection

In every IΣ₁ model, `PellFold.lean` proves the Pell ordinate is signed-congruent modulo the strong abscissa after any internal number of shifts by twice the strong index. It also proves exact equality of ordinate residues on reflection about that index. The arbitrary-block result uses Σ₁ induction. No norm for a proposed target ordinate is assumed and `half_index` is not invoked.

The guarded author check `observations/attempt02/` passed without diagnostics, yielding `/tmp/pell-all-index-fold-ad1a76zq/PellFold.olean`, SHA-256 `302aefad9e2d7a9b4fce22e989d4c4a791f3e79ef83cb6f245a2ed0ed1b4140e`. Attempt01 failed and is retained. Printed axioms are `propext`, `Classical.choice`, `Quot.sound`. The runner pins explicitly listed prototype objects and one inherited provider, not the complete project/package/dynamic or historical source-object ancestry. Resource samples are discrete; no paired replay is claimed.

This is modular arithmetic infrastructure; it does not alone identify a target ordinate or prove a machine or iPRA endpoint.
