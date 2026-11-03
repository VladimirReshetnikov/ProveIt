# Further reduction: historical first-root `+s` proposal

**Later status:** The 89-row graph, the bounded-port positive-zero
equivalence, and the fixed-port all-model halt bridge have since been checked;
see [the absorbed graph record](../ordinary12-absorb89-probe/README.md).
The 89-row [iPRA join](../ordinary12-absorb89-ipra-join/README.md) has also
passed with an independently audited receipt. Formal display binding remains
separate. The text below records the earlier speculative state and the useful
first-factor counterexamples.

The 90-row expression contains the first-root segment

`Z = b*((ell+k+r)-k*Bt+s)-Bt`,

where `b=J*beta`, `q=1+b`, `X=q*w`, `Y=q³*s`, `k=eta+zeta`, and `ell=X*Y²*k`. A possible 89-row rewrite would replace `r+s` by a single positive input `rPrime`, giving

`Z = b*(ell+k+rPrime-k*Bt)-Bt`.

A 90-graph witness maps forward by `rPrime=r+s`, but the inverse requires `rPrime>s`. This inequality is not established for zeros of the proposed rewrite, and no graph, liveness, or model-equivalence result is claimed here.

A possible proof route starts from the first norm. Informally, if `magnitude(Z)=b*first` and `Bt>0`, the root equation gives `b ∣ Bt`; writing `Bt=b*t` with positive `t` yields

`rPrime = (1+k*b)*t - (ell+k) ± first`.

The first norm `first²=1+ell*(ell+k)` and `ell=(X*Y²)*k` with `X*Y²≥1` suggest `3*first > 3*ell+k`. In the plus-sign branch, `b*t≥1` would then give `rPrime>k/3`, and the checked first-Pell growth bounds might imply `k/3>s`. The minus-sign branch is unresolved: `(1+k*b)*t` can nearly cancel `ell+k+first`, so this lower bound does not follow. These observations have not been translated into Lean for the proposed graph; the sign issue prevents treating the one-gate deletion as sound.

`check-89-first-branches.py` records two exact positive first-factor examples with `rPrime=s`, one for each root sign. Both satisfy `beta>0`, `MC<beta`, `MF<2*beta`, `F+alpha<q`, `Bt>0`, `b ∣ Bt`, and the first norm. In the plus example `(s,w,K,rPrime)=(14,2,1,14)`; in the minus example it is `(3,2,20995,3)`. The script gives every derived value. Both have first Pell index 1 and fail the q⁴ rank congruence, so they are **not** full-graph counterexamples and do not settle the high-index case. Their value is to show that the stated first-factor hypotheses alone cannot imply `rPrime>s`; the early-index and rank information would have to be used. The captured run is in `observations/89-branches-attempt01/`.
