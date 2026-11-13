# A one-row free-square candidate and a noncompact full-zero obstruction

The exact [85-row eta/zeta-natural probe](../ordinary13-eta85-zeta-zero-boundary-audit/probe.json) computes `f2=f*f` and `rho=f2−1`. A possible one-row reduction replaces f by an independent natural t, computes `f2=t+1`, and uses t in place of rho. This packet generates the resulting 84-row candidate and checks the pointwise forward substitution `t=f²−1` when f≥1. It does **not** establish a zero correspondence, compact-port result, model theorem, or equation reduction.

At the signed noncompact ports `(beta,K0,MC,MF)=(-1,-1,20,0)`, the candidate has the exact natural witness, in its input order,

```
(J,n_F,n_alpha,t,n_i,n_T,n_w,n_s,r,eta,zeta,y,gamma)
= (1,0,0,16875,0,1,0,0,0,15,4,202499,0).
```

The checker evaluates every row. Here q=0, k=19, Bt=1, Z=−1, R=18, A0=A1=0, `f2=16876`, Q=50625, I=225, strong residual=0, V=202497, auxiliary factor=1, and the complete output is zero. Yet `129²<16876<130²`, so there is no integer f with `f²=t+1`.

The obstruction is stronger than failure of that literal substitution: keep the other twelve witness coordinates and these ports fixed in the 85-row parent, allowing any integer f. Its first and main factors are still one, so an output zero would require the remaining two integer factors to multiply to one. The parent's strong factor is `1+225²−3(f²−1)`, which is never −1 modulo four. It must therefore equal +1, forcing `f²=16876`, impossible. Thus no parent zero can lift this particular child witness while leaving its other coordinates unchanged.

This uses beta<0 and K0<0 and hence says nothing conclusive about the fixed natural compact ports. It also does not rule out a replacement changing other coordinates or settle parent/child existential zero existence. The proposed candidate remains a research probe. The checker generates all 84 rows from the pinned parent, tests the positive-f forward substitution on 300 modular examples, evaluates the full counterexample exactly and checks the mod-four obstruction. It does not run Lean or prove an iPRA endpoint. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-eta-zeta84-free-square-obstruction/check.py | cmp - research/ordinary13-eta-zeta84-free-square-obstruction/receipt.json
```
