# Independent k: conditional obstruction at k = 0

This is a source-only investigation of the exact [84-row independent-k graph](../ordinary13-eta-zeta84-independent-k-candidate/README.md). It does **not** establish that a full graph zero forces k>0, that eta≤k, an unrestricted zero map, or an iPRA endpoint. No Lean source has been elaborated and no provider or axiom replay has run.

Write b=Jβ, q=b+1, X=q w, Y=q³s, a=XY+Y, H=3+4a, U=Yq², F=n_F+1, alpha=n_alpha+1. In the exact graph s=n_s+1 and c=eta+Yk. At k=0 the displayed main root is

```
z = U(X+a eta) + H(U gamma+R+1),
z² = U²(1+(H+a²)eta²).
```

The proposed fact-level `zero_k_impossible` takes precisely these identities, a represented natural R with R+1<q⁴, q>0, s>0, and Y=q³s as **explicit hypotheses**. It deduces U|z by the existing signed square-divisibility theorem; rearranging the first identity yields U|H(R+1), whence q⁵|H(R+1). Signed-to-natural divisibility reflection and `ArithmeticAdaptiveFactorThree2011.cancel_factor_three` then give q⁴|(R+1), impossible since 0<R+1<q⁴. This proof does not need a choice of main-root sign. The proposed source has not been checked by Lean.

There is a possible path to the missing rank hypothesis. It is **conditional on the actual graph's first norm, J>0 and X>0**, which must be separately bound for this changed literal. Let C=q−F−alpha, Bt=C(X+K)−F, and take the natural port K≥0. The exact first root at k=0 is z₀=b r−Bt, and the first norm says z₀²=b². Since X=q w and X>0, w>0 and X≥q. If C<0, then −Bt≥X+F>q−1=b; thus z₀>b, contradicting the first norm. Therefore C≥0. This also gives F≤q, so the signed graph rank can be represented by the natural expression

```
R = ((q−1)(q−F)+alpha)(q²−1) + J(MC+q MF).
```

For C>0, the existing `Residue90CompactPortBoundsDraft.compact_rank_window` is a source-level candidate for the needed bound with its explicit compact beta and mask hypotheses. For C=0, the same first norm forces r=0, F=q−1 and alpha=1: now Bt=−F and b r+F=b. Thus

```
R = q(q²−1) + J(MC+q MF).
```

If beta>0, J>0, MC<beta and MF<2beta, then q≥2 and the mask term is strictly less than (q−1)(1+2q). Consequently `R+1 < q³+2q²−2q < q⁴`; the last strict inequality follows from `q⁴−(q³+2q²−2q)=q(q−1)(q²−2)>0`. These are mathematical implications under the listed hypotheses, not Lean-checked graph theorems. The inequalities require ordered model-natural arithmetic and proper signed/natural cast interfaces.

The earlier eta/zeta-natural unit bridge's generic `first_ne` accepts arbitrary k; `first_pattern`, `main_pattern`, `factor_units` and `signed_norms` are formulated for its **parent literal**, where k=eta+zeta. They cannot simply be applied to the new child expression. A new exact child literal and factor binding are required before using their generic ring/mod-four machinery. Likewise the existing J-positive and X-positive clients target the parent literal. The fact-level X=0 obstruction `Residue90XZeroArithmeticDraft.xzero_impossible` accepts arbitrary c and a signed root; a new child-specific binding must show its hypotheses, including compact beta casts, first/main norms and shape, without assuming eta≤k or k>0. The graph-to-rank representation, strict and weak gap windows, and matching source/provider selection remain separate obligations. The retained parent `PolynomialBridge`, compact port/encoding and physical PDF boundaries are not discharged here.

Nothing here proves eta≤k. Existing partial norm and high-index constructions allow eta>k but are **not full graph zeros**, so they neither refute nor establish a full-zero inequality. The fixed-port values and source-level results must be coherently built and checked before claiming an internal theorem.

The receipt pins the child graph, main helper interfaces and earlier rank client. The checker tests 800 exact graph evaluations at k=0, the two first-norm gap branches and factor-three implication on finite integers, and checks the weak-gap polynomial identity. These controls confirm arithmetic transcription only: finite checks do not prove the model statement, extract units, or validate Lean. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-independent-k-zero-main-rank-draft/check.py | cmp - research/ordinary13-independent-k-zero-main-rank-draft/receipt.json
```
