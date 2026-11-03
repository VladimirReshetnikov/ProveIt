# From a model halt to a calibrated packing and both Pell seeds

`CompactHaltPellSeed.halt_calibrated_seeds` proves in Lean that, in every
model of `IΣ₁`, a model-internal halt of the represented decimal215 machine at
time `T` yields a **single** Boolean controller `δ` and corresponding compact
pulsed cell function `X`. The function and controller are model-Σ₁-definable,
the controller has the explicit positive/nonwrapping support bounds, and
`X` satisfies the full symbolic compact `PackingInput` at
`N=haltLength T` and `s=haltStride T`. No physical mask, block-size,
product-bound, residue, seed or packing hypotheses remain.

Set `q=Exp.exp (590069*N)`, `β=Exp.exp 590069-1`,
`J=rep 590069 N`, and `c=(low+q*(high+β))*J`, using the exact symbolic
compact masks. The same `X` has

```
rank (paramKernel rho) N s X % (590069*N) =
  (590069*s) % (590069*N)
```

and satisfies `SeedBundle` for that exact rank. `SeedBundle` copies the full
outer and auxiliary Pell seed conclusions of `CompactOuterPellSeed.seeds`,
including positivity, the outer size bound, all Pell equations and the two
auxiliary residues. In the theorem's conclusion the rank and seed facts are
expressed under a local instance binder for `X`'s model-Σ₁-definability; the
preceding conjunct explicitly proves that instance, so it is supplied by
the theorem rather than an extra assumption. The proof uses
`CompactRankResidueJoin.rank_eq_window` to select precisely the `c` above
before invoking the arbitrary-`c` halt calibration. The seed theorem then
uses the same kernel, dimensions, pulse and function, not a separately chosen
packing.

This is an all-model construction for the symbolic compact packing. It does
not derive the remaining transport quotient or adaptive gamma lift, construct
a positive zero of the exact free-J graph, bind the symbolic constants to
retained bytes or displayed PDF, or prove that an equivalence is derivable in
iPRA.

The bounded single-author run `observations/attempt02` actually exited 0
without warnings or `sorryAx`; the named axiom report contains only `propext`,
`Classical.choice`, and `Quot.sound`. These are Lean metatheory dependencies,
not additional object-theory axioms. Source SHA-256:
`534fd921acf1e14e87cc098f7631dc5b062036e3434af3d72d7a98617f70a147`;
object SHA-256:
`30b2b18f1c287610ba89a58e469f9efdedd41ba71d5014709323669c90d7c23c`.
Before compilation, the runner compared all 531 overlapping project files
between the seed-rebuild and halt overlays and found no mismatch. Direct
imports and their companion slots, the selected seed and halt project
inventories, and the other recorded roots were unchanged at the subsequent
checks. The terminal receipt, inventories, direct dependency guards, exact
source and compiler log are retained. The earlier `attempt01` failed on a
parser ambiguity in the seed bundle and a definability simplification depth
limit; its exact source and log remain available.

This is a mixed-provider, author-only exploratory result. Point-in-time
overlap and guard checks do not authenticate the full package, transitive or
dynamic-loading ancestry, nor establish an independently reviewed paired
replay. The build's process resource observations and filesystem checks do
not establish continuous monitoring.
