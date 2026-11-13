# A 60-operation carrier rewrite and a failed inverse

This packet records a **conditional candidate**, not a verified reduction of zero existence. It rewrites the reviewed 10-variable/61-operation relaxed two-norm equation into a 10-variable/60-operation graph. The natural forward map from every 61-graph zero is valid under the reviewed assumptions `beta>0, K0>0`; the obvious inverse additionally needs `q−F−C>0`. The exact full zero below shows that condition is not forced by the 60-graph equations at arbitrary positive ports. It does not show that these two equations have different zero-existence status for the same ports, and does not address the fixed compact tuple.

Both graphs remain downstream of the relaxed free-auxiliary-square child. No original-parent, Con(ZFC), iPRA or Lean claim follows.

## Exact graph rewrite and conditional maps

The old graph computes `q=1+b`, `qF=q−F`, `C=qF−alpha`, and `G=alpha+qF*b`, with alpha a strictly positive shifted input. Every old graph zero has C>0 by the [independently reviewed carrier argument](../../reviews/ordinary10-two-norm-divisible61-independent/README.md). Hence replace the alpha input by natural `n_C=C−1` and use

```text
C = n_C+1,
G = q*qF−C.
```

This identity is exact because `q=1+b` and `C=qF−alpha`. The old four operations producing alpha, C, the product `qF*b`, and G become three, with every other operation and output unchanged. A 61-zero therefore maps to a 60-zero, preserving the other nine witness inputs and all ports.

Conversely, a 60-zero satisfying `qF−C≥1` maps back by `n_alpha=qF−C−1`. Without that inequality the unchanged-output identity only identifies the old graph evaluated at a signed alpha, which is outside its natural input domain. The following full graph zero demonstrates that this is a real restriction of the direct coordinate inverse, even when beta and K0 are strictly positive. It does not rule out an unrelated witness transformation.

## An exact positive-port zero with forbidden reconstructed alpha

Use `beta=K0=1`, `MF=0`, and the symbolic nonnegative `MC` defined below. Choose the new inputs `J=1`, `F=1`, `C=1`, `w=17`, and `s=2`. Thus

```text
q=2, X=34, Y=16, U=64, M=X*Y²=8704,
a=Y*(X+1)=560, H=4a+3=2243, A=a+2=562.
```

Let `(tau,k)` be the 45th pair in the Pell recurrence starting at `(1,0)` with multiplier `2M+1` and coefficient `M(M+1)`; explicitly each step is

```text
(tau,k) ↦ ((2M+1)*tau + 2M(M+1)*k, 2*tau + (2M+1)*k).
```

Let `(g,c)` be the 67th pair starting at `(1,0)` for the standard multiplier `A` and coefficient `A²−1`:

```text
(g,c) ↦ (A*g+(A²−1)*c, g+A*c).
```

Exact finite computation verifies `0≤eta=c−Y*k<k` and that `g−X−a*c` is a positive multiple of H. Define

```text
t = (g−X−a*c)/H,
R = k−1 + U*t,
MC = R−3.
```

Take `h=34`, `n_eta=eta`, `n_zeta=k−eta−1`, and `gamma=0`. All listed coordinates and ports are natural. Here `qF=1`, `G=q*qF−C=1`, and the literal rank is `R=3+MC`. The first norm holds because `tau²=1+M(M+1)k²`; the carrier is `C*(X+K0)−F=34=b*h`. Finally `shift=R−(k−1)=U*t`, so the literal main root is `Dstar=U*(X+a*c+H*t)=U*g`, and the second Pell norm makes the main residual vanish. Thus all three squared residuals and the actual 60-graph output are zero. The reconstructed old alpha is `qF−C=0`, so no corresponding natural old alpha input exists under this direct inverse.

The chosen `MC` depends on these Pell numbers and is not the fixed compact mask. The exact finite checker evaluates every operation of the literal candidate graph; it does not rely on a bounded search as a proof of an unrestricted no-go theorem. The predecessor's standard-integer proof and any compact-port specialization are separate obligations.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary10-carrier60-inverse-boundary/check.py | cmp - research/ordinary10-carrier60-inverse-boundary/receipt.json
```

The checker pins the reviewed source graph, verifies the exact row transformation and 60-operation liveness, and checks the concrete witness entirely with integer arithmetic. No Lean, build, provider or iPRA audit was run.
