# Independent review of the full 72-zero carrier obstruction

The [symbolic construction](../../research/p64-qcube72-full-zero-mod-q-obstruction/README.md) was reviewed independently. The pinned 72 graph, exact definitions, bounded Pell premises and changed-port scope check out. No Lean replay or huge witness expansion was performed.

The first and main Pell powers have indices `j=2446738`, `m=4020619`; the retained exact bounded calculation gives `27k<c<28k`, the main quotient `A` integral and positive, and residues `A≡486`, `k≡428`, `m≡184`, `c≡115 (mod 729)`. Positivity follows because `k≥2j>m`, `c>6`, and `g>(n−1)c`. The first norm gives `A0=1`; choosing the 72 input `h=A` makes its main carrier `Ug` and gives `M=0`.

For the strong witness `(f,L)=(g,c)^c_D`, the binomial linear term has coefficient `c²g^(c−1)` and the higher terms contain `c²`, so `i=D L/c²` is a positive integer. Its norm gives `W=0`. With the odd auxiliary Pell exponent `m≡3 (mod 4)`, the real coefficient divided by `I=D L` is positive and the norm gives `Na=1`. The reviewed Chebyshev congruences give `V≡−c (mod f²)` and `V≡−m (mod c)`; since `f²≡1 (mod c)`, both `Q=(c+V)/f²` and `T0=(m+Q)/c` are positive integers.

The exact graph use audit checks that `MC` appears only in the rank mask, `R` only in `cT−R`, and `T` only in `cT`, while `c` depends on neither shifted input. With `J=1`, replacing `MC` by `MC+c` and `T0` by `T0+1` increases `R` and `cT` by exactly `c` and preserves all six residual/output values. The accompanying checker also tests this identity on 160 deterministic integer DAG valuations. The displayed port shift makes `R=m+c`, while the other positive witnesses and transport remain as stated in the construction.

The attempted reverse carrier is then

```
h+k−R−1 ≡ 486+428−184−115−1 ≡ 614 ≡ 2 (mod 3).
```

It is not divisible by `q=3`, hence not by `U=729`. This is a full positive zero of the 72 graph at the stated **changed natural ports** that blocks the direct pointwise inverse. It does not show the 76Y graph has no other zero at these ports, rule out another existence proof, or apply to the fixed compact44 ports.

The [read-only checker](check.py) pins the author graph and packet, reproduces the existing bounded dyadic/rank premises, checks the graph use structure and congruence, and runs its separate finite DAG controls. It neither verifies the universal proof in Lean nor claims full transitive provider provenance.

```
python3 -I -S -B path/to/p64-qcube72-full-zero-mod-q-independent/check.py
```

The frozen output is `result.json`.
