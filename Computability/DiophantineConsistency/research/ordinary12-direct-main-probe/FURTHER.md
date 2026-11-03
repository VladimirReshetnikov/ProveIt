# Further reduction: absorbing the first-root `+s` (unproved)

The 90-row expression contains the first-root segment

`Z = b*((ell+k+r)-k*Bt+s)-Bt`,

where `b=J*beta`, `q=1+b`, `X=q*w`, `Y=q³*s`, `k=eta+zeta`, and `ell=X*Y²*k`. A possible 89-row rewrite would replace `r+s` by a single positive input `rPrime`, giving

`Z = b*(ell+k+rPrime-k*Bt)-Bt`.

A 90-graph witness maps forward by `rPrime=r+s`, but the inverse requires `rPrime>s`. This inequality is not established for zeros of the proposed rewrite, and no graph, liveness, or model-equivalence result is claimed here.

A possible proof route starts from the first norm. Informally, if `magnitude(Z)=b*first` and `Bt>0`, the root equation gives `b ∣ Bt`; writing `Bt=b*t` with positive `t` yields

`rPrime = (1+k*b)*t - (ell+k) ± first`.

The first norm `first²=1+ell*(ell+k)` and `ell=(X*Y²)*k` with `X*Y²≥1` suggest `3*first > 3*ell+k`. In the plus-sign branch, `b*t≥1` would then give `rPrime>k/3`, and the checked first-Pell growth bounds might imply `k/3>s`. The minus-sign branch is unresolved: `(1+k*b)*t` can nearly cancel `ell+k+first`, so this lower bound does not follow. These observations have not been translated into Lean for the proposed graph; the sign issue prevents treating the one-gate deletion as sound.
