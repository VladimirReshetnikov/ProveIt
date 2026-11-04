# Independent source review: conditional natural rank window

Reviewed unchecked `research/trace74-natural-rank-window-draft/Trace74NaturalRankWindow.lean` SHA-256 `41ed8bb4e577c4d1acd15214de7ad3683d0d48233ac2bfef2ca2555118c9cec0`. Its IΣ₁-model scalar theorem assumes beta≥31, J>0, 0<F<q, 0<C≤q, MC<beta<MF<2 beta and q=beta J+1. It defines G=q(q−F)−C and R=G(q²−1)+(MC+q MF)J; the proposed conclusion is 3q<R and R+q³+q+1≤q⁴, using the same scalar parameters. Neither F+C<q nor any graph zero is assumed.

The lower-bound argument uses q−F≥1 and C≤q to make the truncated G subtraction exact, then beta+1≤MF and J≥1 imply q≤MF J, M≥q² and 3q<q². The upper-bound proof supplies nonnegative L and Z and checks G+L+q+1=q² and M+Z+q+1=(q−1)(1+2q); its displayed ring identity gives R+L(q²−1)+Z+q³+q+1=q⁴. These relationships have no apparent mathematical blocker under the stated assumptions. Lean elaboration, tactic behavior and actual resource use are untested.

This source-only review does not derive those scalar assumptions, the existence of a natural rank representative, or the window from an actual graph zero. It does not establish the fixed-port guard, 74/75 equivalence, external file binding or iPRA. No Lean was run.
