# 26-witness sextic candidate via gap congruence

This **external source-only candidate** starts from the independently reviewed 27-witness seed. Write its old coordinates and ports as

`a = beta*(v1+1)`, `q = a+1`, `n = v2+1`, `t = v3+1`, `f = v4+1`, `H = K0+v9+1`, `Q = v15`, and `g = a*q+t-a*n`.

The old gap residual is `v22-g` and the q3 residual is `Q-q³`. Remove old gap coordinate 22 and its residual; shift old 23–27 down one. Substitute `g` for the two bare gap occurrences in tau/cTminusR. To avoid quartic residuals, replace each old `v22*q²` by `(a-n)*Q+(n+t)*q²`. The exact identity

`g*q² - ((a-n)*Q+(n+t)*q²) = -(a-n)*(Q-q³)`

shows that the two modified residuals agree with the lifted old residuals when q3 vanishes; all other surviving residuals agree identically. The formal sparse-polynomial checker verifies these identities for the actual source-pinned ASTs over integer indeterminates, including signs and index shifts. The resulting sum of squares has 17 residuals in 26 natural witness coordinates, with input coordinate 0 unused.

Every residual has syntactic degree at most three. The q3 residual is unchanged from the audited 27 seed; its x1³ coefficient is −beta³, so the x1⁶ coefficient of the square-sum is a sum of integer squares at least beta⁶ > 0 for the fixed positive beta. Thus this external integer polynomial has exact degree six. This is not a Lean degree theorem. Coefficient metadata is copied unchanged at the same relative directory depth; byte identity alone does not prove model-port equality.

The proposed natural reverse lift must establish that `g` is nonnegative and represented by a natural model element. The unchanged Nt residual has the exact identity

`Nt = H*(q-n-t) - n - (f-1)*a`.

For an intended IΣ₁ model with natural variables, positive beta, and nonnegative K0, one has `a≥1`, `H≥1`, `n,t,f≥1`. Nt=0 gives `H*(q-n-t) = n+(f-1)*a > 0`; ordered-ring positivity gives `q-n-t>0`, so `q-n>0` and `g=a*(q-n)+t≥0`. Proving the corresponding natural representative, ordered-ring sum-of-squares decomposition, positivity/division-free order reasoning, injective embedding and model-port casts is an explicit all-model obligation. The q3 residual must also vanish before using the two congruences. Conversely, an old zero has `v22=g`, so dropping it and using q3=0 transfers each surviving residual. These are mathematical proof plans, not checked Lean theorems. No zero-set bridge or iPRA endpoint is claimed, and the existing quartic Jones theorem does not directly apply to this sextic seed.

`python3 -I -S -B build.py --check` reproduces the AST. `python3 -I -S -B check.py` checks every residual congruence and the Nt identity exactly as formal multivariate integer polynomials, the syntactic degree bound, and 16 finite lift controls. Both exited 0. Finite controls are not an all-model proof. The [independent audit](../../reviews/nine-sharing-sign26-sextic-gap-independent/README.md) checked all 17 formal congruences, the Nt identity, degree, coefficient paths and conditional positivity argument.

Pins: builder `255175ae6d43c41c8893c39e82d05b66ec0d407f7237e05054492cf7d12ea5b3`; checker `c1cd665b9e9bc170bbdb416662e7e56c6397a4e038b4e1da8af2df4d6ae0d3c7`; seed `36efa7dd3b2ea06d210b8975db2cbfc4f7494549c87204ada18747a720cb1f25`; result `a321080a1ccccc7ac10dc76b95a507d7d877855800449b6eaa67fa227480d89d`.
