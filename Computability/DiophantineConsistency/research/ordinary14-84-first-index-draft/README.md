# First Pell index from an 84 own-zero — source draft

This unelaborated source proposal composes the 84 own-zero first norm with the
existing `ArithmeticPellFirstNorm.positive_parameter_solution` interface.
Under positive beta and J,w,s and an explicit beta port cast, the first norm
has parameter `Q=X*Y²>0`, and the proposed result supplies an index `n≤k`
with the exact first-root and doubled-ordinate coordinates. The equality
`ell*(ell+k)=Q*(Q+1)*k²` is a polynomial identity; the signed first-root
magnitude remains unchanged.

The source makes no conclusion that this `n` is related to the rank, no main
index, no rank window or gamma bound. Draft imports, model tactics, provider
compatibility and endpoint are uncompiled; no file/PDF interpretation follows.
The checker replays the first-norm draft receipt, checks the norm identity on
200 finite values and checks 16 elementary first-step Pell controls. It does
not invoke Lean or prove arbitrary-model classification.

Independent source review is recorded in
`../../reviews/ordinary14-84-first-index-draft-independent/`.
