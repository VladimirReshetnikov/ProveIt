# Conditional same-data reverse-bridge obstruction at coarse ports

The [nine-variable two-norm graph](../ordinary9-shifted-free-aux-two-norm64/README.md) has a symbolic standard-natural zero at the noncompact ports `(beta,K0,MC,MF)=(127,87,54,139)`, obtained by projecting the pinned [coarse-port i-unshift witness](../ordinary13-eta-zeta84-unshift-i-coarse-bounds-zero/README.md). Subject to the standard-natural soundness of the retained source theorem `P72Exact.indices_ordinary` and its imported lemmas, **no zero of the original shifted-zeta 85-row parent can preserve all nine of those first/main input coordinates**. This is not a Lean-checked theorem, an actual compact-port result, or a proof that the parent has no zero with different coordinates.

The existing witness has `q=128`, `L=2172`,

```text
n=L*(2L+1)=9,437,340,
m=n+L=9,439,512,
R=2n−1=18,874,679,
mu=q^4=268,435,456.
```

Its exact graph rank and first/main signed roots satisfy both norm equations, `eta>0`, `k=eta+zeta`, and `zeta>0`. To use the shifted parent convention take `n_zeta=zeta−1`; all nine retained inputs are natural. The pinned witness proof supplies `Y=q³s` with s>0, `X>0`, the first Pell ordinate at n, `k=2n+4*(XY²)*sFirst`, and the actual main ordinate at m. It also has `R≥26`, `R+1<mu` and `(2n)%mu=R+1`. These facts do not depend on the four auxiliary inputs f, i, T and y.

Suppose, for contradiction, that some natural choice of those four inputs completes the original parent at the same nine values. A product-output zero makes all four integer factors units. The first, main and strong factors cannot be −1 modulo 4, as the checker independently exhausts; hence the strong and auxiliary factors are +1. Since c>0 and shifted i≥1, the strong equation yields f>0 and

```text
I² = Delta*(f²−1),       I=i*c².
```

Let `V=f²*(T*c−R)−c` be the actual signed auxiliary ordinate and y the original natural witness. The auxiliary factor equation is

```text
y² − I²*(y²−V²) = 1.
```

Here I>1, so y=0 is impossible. Rearranging gives `y²−1=I²*(y²−V²)`; since y≥1, `y≥|V|`. Therefore `u=y−V` is natural and

```text
absdiff(f²*T*c, f²*R+c) = |V|,
absdiff(f²*T*c+u, f²*R+c) = y.
```

These give the exact strong and auxiliary hypotheses in `P72Exact.indices_ordinary` at the same natural rank R. Together with the stated Pell, window, eta, positivity and coordinate facts, that source theorem concludes `m=R`. The explicit values instead have `m=9,439,512<R=18,874,679`, contradiction.

This is a **conditional source-theorem application**: the packet inspects the exact theorem signature and checks the finite rank arithmetic, unit-factor residues, and bounded controls for the signed-to-absdiff construction. It does not execute Lean or independently validate the transitive theorem providers, axioms, or all quantified witness/growth proofs. The source theorem's standard-natural soundness and the pinned coarse-witness proof are explicit inputs. Nor does this rule out an original-parent zero with different nine coordinates, a different existential witness transport, or any result at the fixed compact tuple.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary9-two-norm-coarse-no-same-data-lift/check.py | cmp - research/ordinary9-two-norm-coarse-no-same-data-lift/receipt.json
```
