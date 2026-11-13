# Independent source review: zero-k rank representation

The mathematical first-norm argument in `research/ordinary13-independent-k-rank-representation-draft/` is sound under its stated model-natural hypotheses. A source-level equality-orientation hazard remains in its final rank-helper call.

Let `b=beta*J>0`, `C=q−F−alpha`, `B=C*d−F`, with q=b+1 and all model variables natural. When `C>0`, alpha is nonnegative, so `F<q`; the source reflects this signed comparison back with `ι_lt_ι.mp`. When `C≤0`, natural d and positive F give `B<0`; the first norm and positivity of `b*r−B` force `b*r−B=b`. Discreteness of the model-natural r supplies `r=0`, and hence `B=−b`. Since `C*d≤0`, `F≤b<q`. This covers d=0 and does not require positive X, positive k, eta≤k, or a strict positive C. Reflection and tactic elaboration still require a Lean check.

The retained `Residue90GraphNormsDraft.rank_representation` is fact-level in arbitrary natural p and v, assumes only `v 1+1≤q`, and gives `ι(rank)=signed expression`. Its q and rank use exactly the same beta, J, F, alpha and mask ports as the independent-k child; it does not mention the parent's k or require a parent graph zero. Independent reconstruction of the child's ordered rank tree matches the proposed `rankExpr`, including `MC+MF*q`. Arithmetic commutativity accounts for the different expression order in the retained helper. This supports applicability, subject to the proposed casts and provider build.

However, the draft's own goal is `rankExpr.evalRing = ι(rank)`, the **reverse** of the retained helper's equality, while the final tactic is `linear_combination h`. In the installed mathlib tactic, applying `eq_of_eq` to a hypothesis `A=E` and a goal `E=A` leaves `E+E=A+A`, which is not a ring identity. The source therefore likely needs the opposite hypothesis orientation, for example `linear_combination -h`, after the existing simplification. This is a source-level diagnosis; no Lean execution established the exact error or checked the proposed repair. The reviewed original has not been modified.

The checker pins both sources, reproduces the author's receipt, independently reconstructs the complete ordered rank expression, checks helper direction and hypothesis, and exercises both first-norm branches over bounded naturals. The small orientation control demonstrates the sign issue but is not a Lean type check. No graph-to-first-norm extraction, proof of rank representability for a child zero, parent-child zero map or iPRA endpoint is claimed.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-independent-k-rank-representation-second-independent/check.py | cmp - reviews/ordinary13-independent-k-rank-representation-second-independent/receipt.json
```
