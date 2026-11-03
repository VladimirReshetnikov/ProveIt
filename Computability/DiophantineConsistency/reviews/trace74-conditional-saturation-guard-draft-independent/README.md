# Independent source review: conditional saturation and guard

The unchecked draft `research/trace74-conditional-saturation-guard-draft/Trace74ConditionalSaturationGuard.lean`, SHA-256 `9920fb51ab7f6d45ff5b671ac98d39da38adf45b211c8f69910aa343deaffd9b`, has no mathematical blocker identified in this source review. Its README SHA-256 is `c5a6acc0568f3803b645fc2588e3399734398ec8350fcdd89b9c1ac56761fc6c`. No Lean check was run.

The statement retains its arbitrary model `V` with `ORingStructure` and IΣ₁, the same `u,q,C,F,MC,J,H,R`, and every explicit premise: `q=Exp.exp u`, `0<C`, `C-1<q`, `F<q`, `MC*J+1<q`, `F<=MC*J`, the exact natural four-block equation, the mask-population upper bound and the rank-population lower bound. The output asserts both no-carry conditions for those same values and `F+C<q`.

Matching the current sources of `ArithmeticSaturation.saturation` and `ArithmeticRankForcing.noCarry_add_lt`, the proposed application takes `A=C-1`, `M=MC*J+1`, and the original `F,H,R`. Replacing `q` by `Exp.exp u` makes the assumed block and population premises fit the saturation theorem. The first no-carry conclusion and the two strict digit bounds then give `(C-1)+(MC*J+1)<q`. Since `C>0`, `(C-1)+1=C`, and `F<=MC*J`, the same inequality yields `F+C<q` in the correct direction. The draft's proof terms and imports remain subject to elaboration by Lean.

The natural block identity, bounds and population inequalities are assumed rather than derived from any 74 graph zero. The checked all-ring identity alone does not supply them, and this draft does not invoke the guarded 75 saturation result. No fixed-BFS guard, 74/75 equivalence, or iPRA result follows from this review.
