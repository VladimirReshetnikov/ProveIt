# Proposed noncircular inner-coordinate lift

The removed coordinate occurs only in the deleted `cTminusR` row and twice in the retained `Na` row. Let `I = C*T−Rank` in the difference ring. An arbitrary assignment to the 15 remaining coordinates admits an integer lift by setting the removed coordinate to I; it need not admit a natural lift. A finite example in the checker has I negative and is not claimed to be a seed zero.

A possible model proof of natural lift from a sign15 zero is:

1. Work directly from the six retained sign15 residuals, represented ports, positivity of beta, and explicit MC/MF bounds. Reconstruct the unchanged transport, first norm, main norm and strict norm without using a sign16 zero or assuming an inner-coordinate witness.
2. Expand the substituted Na row as the signed relation with `f²*(C*T−Rank)−C`. Apply the generic absdiff-square identity directly to the two natural terms `f²*C*T` and `f²*Rank+C`. This should establish the auxiliary maintained norm without first proving I nonnegative or introducing the deleted coordinate. The existing sign16 auxiliary client uses a retained inner witness and cannot simply be invoked here.
3. Apply the maintained window theorem to those five premises, yielding `2*Rank<C`. The generic sign theorem then gives `0≤ι C*ι T−ι Rank`; the difference-ring nonnegative-representative theorem supplies a natural inner witness. Complete both directions by transferring the six retained rows and the removed defining row.
4. Specialize the port bounds and compose with the sign16 symbolic endpoint only after all preceding model obligations are Lean checked. An iPRA endpoint still requires its own checked transport, and linking the theorem to this external JSON or a PDF requires additional verified binding.

These are proposed steps only. In particular, extraction of the substituted auxiliary norm, all expression/value identifications, the noncircular window assembly and the natural lift remain unproved for sign15.
