# Independent source review: actual residue main congruence

The proposed signed main pair matches the actual 90 graph at arbitrary gamma. With `E=X*Y`, `R'=R+E*q`, and `P=U*(X+a*c)+H*(U*gamma+R'+1)`, `N=H*k`, its signed root is `P-N`. The source calls the direct orientation with **R′**, not R, preserving the required `X*Y*q` term. An independent free-ring check verifies both `P-N=Dstar` and the later regrouping of `P=N+U*main` into the displayed `FreeJMainCongruence` balance after `U=q⁵*s`.

The signed rank/cast bridge explicitly assumes `F<=q`; it is needed to reconcile natural truncated subtraction with the graph's signed expression. The 12-coordinate tuple is exactly `(J,F,alpha,f,i,X,Y,T,eta,zeta,y,gamma)`, with the 90 graph's shifted coordinates used where appropriate. It is an arithmetic tuple for `FreeJMainCongruence`; the source does not assume a free-J literal zero or old `core.z` equality. The q⁴ rank conclusion is delegated to the existing fact-level `rank_congruence_from_main`.

The further early-index client combines the actual first norm with the separately reviewed fact-level Pell wrapper. It explicitly takes a graph zero, J and beta positivity, X positivity, `F+alpha<q`, `R>=24` and the rank window. Its conclusion is the early congruence and `k=2n+4Qw`, not the later exact index. The source still uses the 90 graph's shifted eta and does not establish an eta-zero generalization.

The source interfaces, regrouping identities and finite rank-cast controls were independently checked, and the author's receipt reproduces. The graph and rank extraction, simplification/cast tactics, providers, compact physical port binding, exact-index bridge and iPRA endpoint remain unelaborated or otherwise open; no Lean run was performed.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-residue-main-congruence-model-independent/check.py | cmp - reviews/ordinary13-residue-main-congruence-model-independent/result.json
python3 -I -S -B research/ordinary13-residue-main-congruence-model-draft/check.py | cmp - research/ordinary13-residue-main-congruence-model-draft/receipt.json
```
