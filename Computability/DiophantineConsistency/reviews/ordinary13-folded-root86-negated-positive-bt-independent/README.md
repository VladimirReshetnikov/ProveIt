# Independent review: positive-Bt first-root repair

**Result: pass.** For fixed integer ports with `beta>0`, a positive zero of the sign-reversed candidate with `Bt>0` yields a positive zero of the 88/30 parent while preserving the other twelve coordinates. The proof may choose the other first-root branch. It does not prove `Bt>0`, exclude candidate zeros with `Bt≤0`, or settle unrestricted reverse existence. No Lean or file-binding theorem is asserted.

At a candidate zero, the sum of integer squares makes both displayed first and main residuals zero. Since `M=q³(q−1)>0` and `U=Yq²>0`, the facts `M²|Z²` and `U²|Dstar²` give `M|Z` and `U|Dstar` by prime valuations. Reducing the first expression modulo `q³` and `q−1`, respectively, and using coprimality gives `Y=q³s` with `s≥1` and `Bt=(q−1)t` with `t≥1` under `Bt>0`.

If `k=2`, positivity forces `eta=zeta=1` and hence `c=2Y+1`. With `a=XY+Y`, this gives `1<c<2(a+2)`. The main radicand lies strictly between the consecutive squares `((a+2)c−1)²` and `((a+2)c)²`, a contradiction. Thus `k>2`.

The stated inverse first-Pell step has positive integer coordinates, preserves norm, and gives `0<k'<k`; positivity of the first coordinate follows by comparing its two positive terms' squares, and positivity of `k'` follows because the squared difference is `k²−4>0`. A norm-one solution with `k'=1` lies strictly between consecutive squares, so `k'≥2` and `tau'≥2m+1`. Inverting the step yields `k≥8m+4`. The first Pell identity then gives `tau−ell>k/4>2m≥2s`. For `Bt≥1` and `t≥1`, the proposed parent coordinate

`r_old=k*(Bt−1)+t−s+(tau−ell)`

is positive and makes the parent first expression `M*tau`. The other three residuals are independent of that coordinate, so they stay zero. This establishes a positive parent witness at the same remaining coordinates regardless of the given candidate's root branch.

The independent checker reproduces the author and earlier signed-fold receipts, verifies actual residual dependencies in both graphs, and checks exact polynomial identities for the Pell descent and consecutive-square gaps. Its finite controls are evidence for those identities, not a replacement for the unbounded argument above. Run from `Computability/DiophantineConsistency` with `python3 -I -S -B reviews/ordinary13-folded-root86-negated-positive-bt-independent/check.py`; stdout must match `result.json`. No Lean process was run.
