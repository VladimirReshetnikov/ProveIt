# F=0 at compact ports: first-root witness and an extremal-C index bound

At the exact fixed compact ports, the 84-row F-unshift probe has an actual **first-norm solution** in the remaining F=0, C>0 branch with C=beta and X>0. The actual main norm rules out this particular first-Pell index; the full branch remains open. All statements here are ordinary-integer arithmetic, not Lean or an iPRA proof.

Take `J=1`, `F=0`, `alpha=1`, `w=s=1`, so `q=beta+1`, `X=q`, `Y=q³`, `M=XY²`, `C=beta`, and `B=beta*(X+K0)`. For first Pell index n=2, set

```text
k=8M+4, tau=8M²+8M+1,
eta=0, n_zeta=k−1,
h=X+K0, r=(k*beta+1)*h−4M−3.
```

These are natural and the exact graph first root is `Z=beta*tau`; the first residual is zero. Thus the first norm, positive X, odd C and literal beta-divisibility do not alone exclude F=0 at the actual fixed tuple.

The actual main norm gives a much stronger necessary index bound in this extremal-C slice. The pinned [norm-congruence argument](../ordinary13-f-unshift-fixed-positive-gap-norm-congruences/) gives `2n≡R+1 (mod q⁵)` for a natural first-Pell index n. With C=beta=q−1 the literal rank is

```text
R=(q²−q+1)*(q²−1)+MC+q*MF,
R+1−MC=q*(q³−q²+1+MF).
```

Hence `2n≡MC (mod q)`. The fixed low mask is even and `0<MC<q`, while q is a power of two; therefore every nonnegative n satisfying this congruence obeys `n≥MC/2`. Its least base-`2^67` digit is `2^67−2`, so

```text
n ≥ MC/2 ≥ 2^66−1.
```

In particular the n=2 first-norm witness cannot also satisfy the main norm. This excludes only C=beta; it does not address arbitrary positive odd C or establish that an F-probe zero exists or does not exist.

There is an independent, mask-free way to see the n=2 obstruction for `X=q,s=1`. For any eta<k, its main ordinate is in `[Yk,(Y+1)k)`, while its main Pell multiplier is `A=Y*(q+1)+2`. Exact positive-coefficient expansions in `q−2` establish

```text
y_3=4A²−1 < Yk ≤ c < (Y+1)k < 8A³−4A=y_4.
```

The standard Pell descent for discriminant `A²−1` classifies nonnegative solutions by strictly increasing ordinates `y_j`; the interval contains no solution. The pinned `ArithmeticPellClassification.solution_index` source expresses the corresponding all-model theorem, but it is not elaborated or invoked as a checked Lean provider in this audit.

The checker pins the F probe and compact-source facts, reproduces the preceding receipt, verifies the literal field wiring and the q=2+t positive-coefficient gap certificates, and evaluates bounded exact first-root controls. These tests supplement the quantified algebra and Pell argument; they do not give a full graph zero, a zero-preserving map, or an axiom audit.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-f-unshift-compact-first-root-n2-boundary/check.py | cmp - research/ordinary13-f-unshift-compact-first-root-n2-boundary/receipt.json
```
