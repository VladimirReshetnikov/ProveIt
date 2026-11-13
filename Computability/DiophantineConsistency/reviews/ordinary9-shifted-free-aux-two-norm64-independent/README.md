# Independent review: nine-variable shifted free-auxiliary two-norm graph

The [reviewed candidate](../../research/ordinary9-shifted-free-aux-two-norm64/README.md) has nine natural inputs and 64 live binary operation rows. Its standard-integer zero existence is equivalent, for any four nonnegative ports, to that of the **shifted free-y² child**. I found no mismatch in the graph projection, the factor/completion directions or the degree-60 argument. The separate reverse bridge to the original shifted parent, where y² must really be a square, remains open; no Con(ZFC), Lean/iPRA or PDF equivalence follows.

Independent ancestor tracing from the shifted free-y² child's A0 and A1 gives exactly the candidate's first 61 rows, with the same ordered expressions. The remaining three rows square A0 and A1 and add them. All 64 rows and all nine named witness inputs are structurally live. On integers the output is zero exactly when A0=A1=0.

For child-to-candidate, a product-output zero makes each of the four integer factors ±1. The exact first and main factors cannot be −1 modulo four, as confirmed by all 1,280 respective residue patterns; hence their residuals vanish. For candidate-to-child, q=1+beta*J≥1, shifted s≥1 and shifted `k=eta+zeta+1≥1` give `c=eta+Yk>0`. The independently reviewed general completion then chooses natural f, shifted i, shifted T and a free auxiliary square making the strong residual zero and auxiliary factor one, without changing the two retained residuals. This is ordinary-integer reasoning, and the completion may deliberately choose a nonsquare free y². It neither lifts that witness to the original parent nor disproves a different parent witness.

For fixed beta≠0, the degree claim also checks out. The exact expansion of A1 cancels the highest `U²a²c²` terms. With witness degrees bounded by `deg(U,X,a,c,H,S)≤(6,2,6,5,6,7)`, its three remaining groups have degree at most 28, 30 and 26; A0 has degree at most 24. The sole degree-30 group has leading homogeneous term

```
8*beta²¹*J²¹*w²*s_input⁵*(eta+zeta_input)*gamma_input.
```

It is nonzero for beta≠0, so the two-norm output has degree exactly 60. On the reviewed ray the degree-60 coefficient is `64*beta⁴²`; independent exact univariate polynomial controls also confirm it for varied positive and negative nonzero beta and varied other ports. For beta=0 this review makes no degree-60 claim.

The receipt reproduces the author's and general-completion review checkers, independently traces the A0/A1 ancestors and graph liveness, checks both factor patterns, and exercises the degree and shifted-c positivity on bounded controls. The written polynomial and completion arguments establish the stated standard-integer claims; those controls do not constitute Lean elaboration, provider/axiom validation, parent reverse transport or PDF semantics. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B reviews/ordinary9-shifted-free-aux-two-norm64-independent/check.py | cmp - reviews/ordinary9-shifted-free-aux-two-norm64-independent/receipt.json
```
