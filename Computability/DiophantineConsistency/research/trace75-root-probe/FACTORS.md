# Trace75 positive graph root extraction

`Trace75Factors.graph_roots` discharges the remaining representative
hypotheses for the actual trace75 registers. In any `IΣ₁` model, for arbitrary
natural ports with `0 < beta` in the model and any ten strictly positive
witnesses, a zero of the Lean trace75 ring value in the model's difference
ring yields positive `tau,f0` satisfying `E=tau²` and
`1+Delta*U²*E=f0²`. The proof supplies positive natural representatives of
Δ, U, E and M; for M it justifies the truncated subtraction of one before
casting to the difference ring. The result is trace75 K2 radical extraction;
it is not an equivalence to machine halting, an iPRA proof, a trace74 guard,
or a Lean binding of external JSON or fixed coefficient bytes.

Accepted source `Trace75Factors.lean` SHA-256
`14667194d1027fb9c5b23825165efdf67488c0f2632dedd62e3c1075fdce8eb2`;
`run-factors-v2.py` accepted `observations/factors-attempt02/`, object
`/tmp/trace75-factors-4hp2mk1k/Trace75Factors.olean` SHA-256
`1bae9331cfbca4e35cb48916f135b63eedc8b5c827f8f24ae6f12b2dff111975`.
The `#print axioms` output is `[propext, Classical.choice, Quot.sound]`.
Attempt01 compiled but its runner rejected an unused-simp-argument warning;
that snapshot and log are retained, and the accepted source removes the
unused argument. Direct imports are pinned; the fresh symlink overlay selects
historical project dependencies and the freshly compiled trace75 provider.
No full selected transitive/package/dynamic closure audit or independent
Lean replay is claimed.
