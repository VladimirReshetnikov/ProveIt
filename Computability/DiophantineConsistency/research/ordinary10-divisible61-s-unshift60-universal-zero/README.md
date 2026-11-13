# Unshifting s makes the 10/61 candidate universally solvable

The 60-operation literal candidate in this packet deletes the 10/61 graph's `s=n_s+1` row and replaces `Y=q³*s` by `Y=q³*n_s`. It has a natural zero for **every** natural port tuple with `beta≥2`, including the fixed compact ports. Thus the original positive-shift argument cannot justify this one-gate change. This does not decide whether the original 61-operation graph has a zero, rule out a different witness map, or prove any Con(ZFC) or iPRA equivalence.

The construction is the direct 10/61 projection of the separately pinned 85-probe s-unshift obstruction. For natural `K0,MC,MF` and `beta≥2`, define

```text
L = ceil((K0+2)/beta),   w = beta*L-K0-1,
q = beta+1,
R = (1+beta²)*(q²-1) + MC + q*MF,
t = (beta-1)*(w+L)-1.
```

The ceiling gives `L≥1` and `1≤w≤beta`; hence `t≥1`. Also `R≥1`. In the unchanged ten-input order of the 61 graph, set

```text
(n_J,n_F,n_alpha,n_w,n_s,n_h,n_tau,n_eta,n_zeta,n_gamma)
 = (1,0,0,w,0,t,1,1,R-1,0).
```

Every input is natural. The altered graph has `Y=U=ell=0`, `C=beta-1`, `kbase=R`, and `k=R+1`. Its carrier is zero because

```text
C*(X+K0)-F = beta*((beta-1)*(w+L)-1) = beta*t,
```

and the normalized first norm is zero because `tau=1` and `ell=0`. The main root and residual vanish because `U=0` and `R-kbase=0`. Hence all three squared residuals and the literal output are zero. The compact beta is `2^(67*8807)-1≥2`; the compact port values are natural, so the construction applies without expanding them.

`check.py` pins the predecessor and beta sources and checks the exact two-row edit, topology and liveness. It evaluates **all 60 literal rows over the integer polynomial ring** in symbolic `beta,w,L,MC,MF`, with `K0=beta*L-w-1`, and checks the three residuals and output are identically zero. The ceiling inequalities above ensure that every concrete natural `K0` produces natural witnesses; finite ceiling controls supplement that elementary argument. No huge compact coefficient or witness is expanded.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary10-divisible61-s-unshift60-universal-zero/check.py | cmp - research/ordinary10-divisible61-s-unshift60-universal-zero/receipt.json
```

This is a standard-integer counterexample to this particular local change. No Lean, build, staging, model transport, parent bridge or fixed-port no-solution equivalence has been established.
