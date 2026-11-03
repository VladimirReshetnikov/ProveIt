# Nonnegative transport restores the mask gap

`Direct80TransportMask.positive_mask_of_nonnegative_transport` proves in every IΣ₁ model that nonnegativity of the actual signed graph transport `B`, together with positivity of its `F` and `w` inputs, implies `F+alpha<q`. The proof evaluates the exact graph expression, observes that `(K0+w)*(q-F-alpha) ≥ F>0`, and uses positivity of `K0+w`. It needs neither a graph-zero assumption nor any sign for rank or signed carrier.

Guarded author `observations/attempt02/` passed without diagnostics, producing `/tmp/tenpositive-80transport-mask-4bo36dze/Direct80TransportMask.olean`, SHA-256 `5a957da824becfc4ea1eb5a95820e4e43a675b097bab4f920e5e6e26b8cded61`; attempt01 failed and is retained. Printed axioms are `propext`, `Classical.choice`, `Quot.sound`. The runner pins selected prototype objects and one inherited provider, not full transitive project/package/dynamic or historical source-object ancestry. Resource checks are sampled; no paired replay is claimed.

This is a one-way implication: deriving nonnegative transport still requires the graph carrier estimates, and the later fixed-port rank bounds, machine theorem and iPRA endpoint remain separate.
