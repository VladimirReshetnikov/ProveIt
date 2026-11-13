# Independent-k signed rank: proposed natural representation

This source-only packet isolates the noncircular k=0 rank step. Its fact-level `first_norm_F_lt_q` proposes `F<q` from natural beta>0, J>0, F>0, `q=beta*J+1`, and the **explicit** k=0 signed first-norm equation. The variables alpha, d and r are model naturals. It assumes neither k>0 nor eta≤k, and requires no positive d, X or strict gap `q−F−alpha>0`. It does not extract that first norm from a child zero.

Let b=beta*J, C=q−F−alpha and Bt=C*d−F. When C>0, natural alpha≥0 immediately gives F<q. When C≤0, Bt<0 and the first norm `(b*r−Bt)²=b²` has positive left root, so `b*r−Bt=b`. Naturality and b>0 force r=0 and Bt=−b. Since C*d≤0, `F=b+C*d≤b=q−1<q`. This also handles d=0 and avoids invoking the desired k positivity or the strict-gap theorem.

The existing `Residue90GraphNormsDraft.rank_representation` works for **any** natural port tuple and valuation once `v 1+1≤q`; its model q is `1+v 0*(p 0:V)`. It represents the exact signed expression by the model natural

```
((q−1)*(q−F)+alpha)*(q*q−1) + (MC+q*MF)*J,
```

with natural truncated subtraction. Its explicit F≤q and automatic 1≤q guarantee the `P72Root.ι_tsub` rewrites. The old literal has a different k construction, but this rank theorem's statement and source proof do not mention k or that graph's zero. The separate source-only `rankExpr` is a reconstruction of the new child rank's exact ordered expression tree, and proposed `rank_representation` applies the existing generic arithmetic lemma to it. The checker verifies the R-row tree against the pinned 84-row child, including multiplication order. The generated graph structure does not export an R field, so a Lean graph-to-`rankExpr` subexpression connection and its use in the main-root shape are still separate work.

Both proposed theorems are unelaborated: imports, `ι_lt_ι` reflection, positivity and nonlinear tactics, ring normalization, port casts, and the inherited `Residue90GraphNorms` provider graph remain unverified. In particular, the strict first-norm equation must still be derived from `InternalZero` and k=0 using the separate child unit bridge; this packet does not prove k>0, eta≤k, a zero correspondence, provider closure or an iPRA endpoint. `#print axioms` commands are future requests only.

An [independent source review](../../reviews/ordinary13-independent-k-rank-representation-second-independent/README.md) found that the helper equality is oriented opposite to the final target, making the proposed `linear_combination h` a likely sign error. The original remains unchanged; reversing that equality is still subject to Lean verification.

The receipt reproduces the child unit checker, verifies the exact graph rank tree and generic rank helper signatures, and tests finite cases of both first-norm branches, including d=0. Finite controls do not prove the model statement or check Lean. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-independent-k-rank-representation-draft/check.py | cmp - research/ordinary13-independent-k-rank-representation-draft/receipt.json
```
