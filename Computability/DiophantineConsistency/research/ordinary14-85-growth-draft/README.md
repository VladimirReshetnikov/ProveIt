# Direct 85 growth bound — source draft

This unelaborated source replay adapts the arithmetic steps of
`FreeJPowerGrowth` to the direct 85 own-zero interfaces, without invoking a
FreeJ graph theorem. It retains positive beta, an **explicit beta≥46** bound,
positive valuation, four port casts and mask inequalities. The proposed first
lemma derives X≥16 from direct q∣3X; the second uses the proposed exact
indices and the existing model `power_bound` interface to derive `2^R<Y`.
It assumes no q∣X, 84 zero, FreeJ zero, or X=2^R.

This is not a Lean-checked theorem. In particular beta≥46 still needs a
symbolic compact-port instantiation, and the factor-three projection, exact
indices and all their draft dependencies require compatible guarded builds.
The checker inventories source interfaces, replays the factor-three receipt
and tests only elementary threshold/index identities. It does not reprove the
model power bound or test graph-zero existence. Power equality, Mersenne
cancellation, 85→84, iPRA endpoint and file/PDF semantics remain separate.

Independent source review is recorded in
`../../reviews/ordinary14-85-growth-draft-independent/`.
