# Independent review: 80-graph transport, repunit, and scaled sandwich

`graph_natural_transport` starts from the same positive 80-graph zero's derived mask gap and integral signed transport. Under beta≥31, odd beta, and the low/high port bounds, it constructs natural `t` and positive `C=q−F−alpha` satisfying `(K0+w)*C=F+b*t`. Both truncated subtractions are justified by the strict mask inequality before embedding them in the difference ring. The theorem does not assume `t` or C positive as extra hypotheses.

`graph_repunit` takes the **same** positive internal N supplied by radix alignment and proves `J=rep d N`, `q=2^(d*N)`, the rank bound and the residual power for w. It additionally assumes `d≥2` and the model equation `beta+1=2^d`; it does not produce a second independently chosen repunit length. The rank-three theorem supplies the separate `3q<rankNat` bound.

`graph_population_of_half_binomial` uses this same N, the actual `q³` factor in `Y`, and the rank bound to establish a population lower bound. Its statement explicitly assumes both `rankNat=2r+1` and the natural half-binomial representation `2Y=binom(2r,r)+zX`. The latter is not established by these packets. The checked conditional result does not establish graph-to-halt soundness.

The generic lower scaled sandwich uses the actual shifted-base coefficient inequality. Its graph binding obtains r from graph variable height and n from alignment, then derives `n=r+1` from their exact equations before using either Pell ordinate; it does not identify two existential witnesses by assumption. The generic upper theorem proves its corresponding coefficient inequality, but its actual upper conclusion still assumes the separate perturbation bound `6r≤A0` and the crude-power inequality `6r*(X+1)^(2r)<A0*X^r`. The generic rounding theorem requires **both** strict sandwich inequalities as explicit premises, plus the exact power and mask equations; it does not yet discharge the missing graph upper bound or the half-binomial identity.

A later [graph sandwich join](../../research/ten-positive-80-sandwich-both-prototype/README.md)
has since derived both inequalities for one graph witness. That later result
is outside this captured review and requires its own audit.

The captured `check.py` verifies nine accepted producer receipts, current source/runner/Lean and object hashes, selected predecessor pins, direct import resolutions and matching accepted producer hashes, diagnostics, axiom allowlists and sampled resources. It inventories 12 terminal histories and checks their archived source/log hashes; the generic upper attempt01 was warning-rejected and is not promoted. Selected paths and hashes are in `observations/attempt01/stdout`.

This is a read-only review with no independent Lean replay or complete transitive serialized/package/dynamic and historical source-to-object reconstruction. Axiom reports are Lean metatheory dependencies, not object-theory iPRA axioms. Resource observations are sampled; fixed-recipe/PDF binding, machine reconstruction and iPRA remain separate.
