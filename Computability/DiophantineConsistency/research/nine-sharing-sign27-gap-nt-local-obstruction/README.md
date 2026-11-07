# Local obstruction to dropping the gap input

In the 27-witness seed, the gap residual can be solved algebraically for v3; only gap and Nt contain v3, and substitution into Nt has residual syntactic degree at most 3. A reverse lift would have to show that this reconstructed v3 is natural. Gap and Nt alone do **not** give the required nonnegativity, even for every positive β and nonnegative K0.

For arbitrary integers a ≥ 1 and K ≥ 0, set β=a, K0=K, v1=v2=0, v3=−2, v9=(a−1)K+a, v4=a(K+1)+K+2, and gap witness v22=a²−1. The displayed values except v3 are nonnegative. Exact formal polynomial evaluation of the two source-pinned residual ASTs in Z[a,K] gives gap=Nt=0. Thus a positivity proof using only these two residuals and the indicated basic bounds cannot justify the proposed lift. Other residuals are not required to vanish in this construction: it is **not a counterexample to the full system**, not a proof that no additional assumption or full-system lemma can work, and not a lower bound on witness count.

`python3 -I -S -B check.py` exited 0, reproducing `result.json`. The finite sparse-polynomial identity check is external, with no Lean proof or model equivalence claim. The [independent review](../../reviews/nine-sharing-sign27-gap-nt-independent/README.md) separately checked the identities and nonnegativity argument.

Pins: 27 seed `5bd7f45de28980c6ac9d3974a0087b1d9f8faf9b060b8a115843ea0cc4adff3d`; checker `46f8d5830c37585799ae2d0097f0239e0bcf7c219ff81f1868f704250bd940dd`; result `291613efec69d4da5e930769c5a678ec631c8581c54b9405c527600565966f92`.
