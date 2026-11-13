# Independent review of the compact-window partial assignment

The pinned [partial assignment](../../research/p64-qcube72-compact-window-partial-obstruction/README.md) checks out in the stated standard-integer scope. Its actual ports are `(2,1,1,0)`, not the fixed compact44 tuple. In particular its `beta=2` does not have the compact tuple's odd, very large exact beta; only the explicitly listed port-size inequalities are shared.

At the stated positive coordinates, `q=3`, `Y=27`, `X=6`, `C=1`, `R=41` and the transport residual is zero. The independently checked exact Pell intervals give `27k<c<28k`, so `eta=c−27k` and `zeta=28k−c` are positive, their sum is `k`, and `c>2R`. The first Pell norm gives `A0=1`; the main norm and integral positive `h=A` give `M=0`. The strong power's coefficient is divisible by `c²` by its binomial expansion, so its positive `f,i` satisfy `W=0`.

The example meets `MC<beta`, `MF<2 beta`, and `R+1=42<81=q⁴`. It also satisfies the stronger previously used rank window `24≤R` and `R+q³+q+1=72≤81`. The carrier expression is `h+k−R−1≡486+428−41−1≡2 (mod 3)`, so the listed equations and bounds alone do not force the direct carrier congruence.

The auxiliary residual really does fail for the **specified** `T=y=1`: `k≥2j` and the interval give `c>55` and `c>2R`. The positive strong Pell power gives `f≥2`, so

```
V=f²(c−41)−c ≥ 3c−164 > 1,
Na=1+I²(V²−1)>1.
```

Because `A0=1`, the full sum-of-squares output is strictly positive. This is not a full 72 zero. The packet does not rule out different `T,y`, prove anything about actual compact44 zeros, refute existential equivalence or establish a Lean theorem.

The [checker](check.py) pins the author packet, the 72 graph and the independent bounded Pell checker; reproduces the author's output; independently checks the small graph arithmetic, rank bounds and residue; and verifies explicit lower-bound premises. It does not expand the huge Pell witnesses. The mathematical norm and inequality argument above supplies the symbolic conclusion.

```
python3 -I -S -B path/to/p64-qcube72-compact-window-partial-independent/check.py
```

The deterministic result is frozen in `result.json`.
