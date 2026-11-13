# Natural scalar rank lower bound 40 — source draft

This unelaborated source proposal derives `R≥40` from positive beta,J,F,alpha,
`q=1+J*beta`, and `F+alpha<q`; MC and MF need only be natural. The 84 own-zero
client supplies the scalar gap with explicit beta/K casts and all-positive
valuation. It does not need mask upper bounds. The proof uses explicit natural
subtraction reconstruction before deriving `q−1≥2`, `q−F≥2`, scalar factor
at least 5 and `q²−1≥8`.

The bound would supply P72Exact's `26≤R` premise if all component drafts
were compiled and provider-compatible; it does not establish the remaining
exact-index premises. The finite sharpness control beta=2, J=1, q=3,
F=alpha=w=h=1 and K=MC=MF=0 satisfies the guard and gives R=40, but is not
claimed to be a full graph zero. The checker tests 1,000 finite scalar
instances and replays the natural-rank draft receipt. No Lean run, iPRA
endpoint, external-file or PDF correspondence is claimed.

Independent source review is recorded in
`../../reviews/ordinary14-84-rank-lower40-draft-independent/`.
