# Independent source review: conditional natural rank binding

Reviewed unchecked `research/trace74-natural-rank-window-draft/Trace74RankBinding.lean` SHA-256 `f6d61f45242ec1c783064f5cae28fc0b56e8abd1182c5c35cc1110f9cadfd143`. Its first statement proposes the actual 74-induced signed `regs` rank's universal commutative-ring shape. Its second applies that identity to the same ports and model valuation, equating signed rank with the difference-ring cast of `Trace74NaturalRankWindow.rank`, assuming only `v 1 < q p v` and `v 2 ≤ q p v`.

The subtractions used by the cast are justified in the displayed proof: F<q gives F≤q and 1≤q−F; consequently C≤q≤q(q−F), and q>0 gives q²≥1. These ensure the three natural truncated subtractions cast to the intended difference-ring subtractions. The ring shape algebra groups the first two original rank terms into q(q−F)−C. No reverse F+C<q guard or graph zero is assumed. We found no mathematical blocker, but `change`, `simp`, homomorphism rewrites, tactic elaboration and resource use are untested; no Lean was run.

The draft does not derive F<q or C≤q from a graph zero, derive a natural rank window on its own, or prove the fixed-port guard, 74/75 equivalence, external file binding or iPRA. A later checked run must pin and select both direct providers and preserve their inherited ancestry limitations.
