# Same halt witnesses with the auxiliary ordinate ordered

`CompactHaltFirstOrdered.aux_ordered` takes `R>0` and the existing
`PositiveAuxData u R sY`, and supplies `OrderedAuxData u R sY`: the full
original auxiliary witness data plus `auxw≤y` for the **same** existential
auxiliary `f,i,T,auxw,y`. It applies the exact seed-ordinate theorem to the
existing norm, positivity and rank; no separate seed is constructed.

`halt_first_ordered` applies this to `halt_first_gamma` in any `IΣ₁` model.
From the model-internal decimal215 halt, it retains the chosen definable
Boolean controller and pulsed word, symbolic packing, calibration, positive
shifted transport, outer seed, first-carrier data and positive adaptive gamma,
and replaces the auxiliary data with its ordered strengthening. Its only
non-instance starting hypothesis is the model halt. Rank positivity follows
from the same packing. The result explicitly returns the word's
model-Σ₁-definability before the local instance binder for its other data.

The auxiliary order makes `y-auxw` the exact model-natural difference for
the corrected free-J coordinate `delta(a)*i+(y-auxw)`. The auxiliary `auxw`
is distinct from the transport power, and the positive adaptive gamma is
distinct from the outer seed's gammaOld. The theorem does not yet assemble
the twelve-coordinate graph valuation, prove its exact graph zero, bind the
symbolic tuple to retained coefficient/PDF bytes or establish an iPRA proof.

The bounded mixed-provider single-author `observations/attempt01` actually
exited 0 without warnings or `sorryAx`. Both named Lean metatheory axiom
reports are exactly `[propext, Classical.choice, Quot.sound]`, not
object-theory axiom lists. Source SHA-256:
`5424190d6d69e7414c630ebf4ffcc942352d1bf46632f9f4afda605e7c2c315f`;
object SHA-256:
`ef1d7230ffe6d23a7fc1f32730337e5d1f47d795ddc3acc5e4776dfd38b51545`.
The exact source, direct dependency/companion guards, compiler receipt and
selected project/root inventories are retained. Recorded guards and
inventories were unchanged at final checks, with the preflight overlap
comparisons recorded in the attempt. These point-in-time observations do
not authenticate the full transitive, package or dynamic provider ancestry,
constitute an independently audited paired replay, or imply continuous
filesystem/resource monitoring.
