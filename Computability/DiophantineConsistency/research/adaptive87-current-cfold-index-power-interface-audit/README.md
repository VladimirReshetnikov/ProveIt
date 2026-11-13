# Source-interface audit: C-fold indices and power recovery

This audit checks the exact source signatures and algebraic correspondence needed to replay the existing Pell-index and power-recovery arguments on the pinned current2011 88/28 C-fold facts. It is **not** a Lean proof, provider authentication, all-model bridge, or independent recompilation of the cited theorems. The 88/28 graph, current port receipt, preceding orientation/q⁴ result, and each named source are pinned in `result.json`.

Use the candidate packet's positive-integer definitions, and distinguish the two quotients: write `m=X*Y²`, `Y=q³*sY`, and let `w` be the first-Pell recurrence quotient. From the first norm and the positive root tau, `ArithmeticPellFirstNorm.positive_parameter_solution m tau k` has the required parameter `2*(m−1)+1` and gives one first index n with the **same** tau and k. From the oriented main norm, `ArithmeticPellClassification.solution_index a d c` gives one main index p with the **same** d and c. Positivity supplies `m>=1`, `k>0` and `c>0`, so the natural subtraction in the first base is legal and both indices are positive.

`ArithmeticPellCongruences.residue_quotients` with modulus `2m` and first base `2*(m−1)+1` yields

```
k=2*n+4*m*w.
```

With `Y=q³*sY`, q⁴ divides 4m, so `k≡2n (mod q⁴)`. The preceding packet gives `k≡R+1 (mod q⁴)`. Under the checked current-port bounds and `C>0`, the scalar rank-window theorem gives `R+1<q⁴` (and a direct lower bound gives `R>=q³>=26`), hence `(2n) mod q⁴=R+1`.

For `P72Exact.indices_ordinary`, the argument mapping is:

| Source argument or hypothesis | Candidate value or preceding fact |
| --- | --- |
| q, X, Y, k, R | the same graph expressions; q>=47, all indicated inputs positive |
| g, c, a | positive main quotient d, graph c, graph a=Y*(X+1) |
| y0, i', f, T, u, eta | sY=Y/q³ and the corresponding unchanged graph witnesses |
| n, s, mu, m | first index n, first recurrence quotient w, q⁴, main index p |
| first norm/index and k=2n+4*m*w | first classification and recurrence above; source `m` in its first base is graph `X*Y²` |
| R+1<mu and `(2n)%mu=R+1` | rank window and the q⁴ congruences above |
| main norm/index | the same d,c and main index p above |
| strong norm | `I=i*c²`, `I²=Delta*(f²−1)`, with f>=1 |
| auxiliary norm | `Fa=1` with the two absdiffs equal to `|V|` and `|V+u|` |

The last line remains valid if V or V+u is negative: the source's first absdiff arguments are `f²*T*c` and `f²*R+c`, whose signed difference is V; adding the graph's positive u to the first argument gives V+u. The checker verifies the auxiliary ring identity exactly and exercises both negative cases; finite controls do not prove the source theorem. The documented P72 conclusion is `n>=13`, `n<p`, `p=R`, `2n=R+1` for these same witnesses.

For the power step put `r=n−1`. Then `r>=12`, `R=2r+1` and `n=r+1`. Since the first index gives `k=R+1+4*m*w`, set `W=4*X*q*sY*w`; the checker verifies exactly that `4*m*w=U*W`, with `U=Y*q²`. The oriented main carrier then becomes

```
q*(d+H*W)=q*(X+a*c+H*gamma)+H*X.
```

Because `H=3+q*L`, it follows that `q|3X`. The positive X and q>=47 force `X>=16`. The source `ArithmeticPellPowerRecovery.power_bound` now receives the same X,Y,r,k,c,eta,zeta, first index `r+1` and main index `2r+1`, and yields `2^R<Y`.

For the final projection, `projection_quotient a R` applies to the same positive main root d and ordinate c and states `d=2^R+a*c+H*z`. Multiplying the displayed q-balance by L and reducing modulo H gives `3d≡3*(X+a*c) (mod H)`, hence `3X≡3*2^R (mod H)`. Because `X<a`, `2^R<Y<=a`, and `3a<H=4a+3`, both sides are already in `[0,H)`, so integer equality and cancellation of the nonzero integer 3 give `X=2^R`. This does **not** require 3 to be invertible modulo H. Together with `R>=q³` and q>=3, this gives `X>=q²`.

These are fact-level source and mathematical bindings; they still require a separately checked complete Cal argument and, for iPRA, actual graph-to-model casts, indices, signed roots, witnesses and provider/Lean verification. The existing `FreeJ` wrapper theorems that assume a different literal zero must not be applied directly to the C-fold graph.

Reproduce from the DiophantineConsistency directory:

```sh
python3 research/adaptive87-current-cfold-index-power-interface-audit/check.py > /tmp/adaptive87-cfold-index-power-current.json
cmp research/adaptive87-current-cfold-index-power-interface-audit/result.json /tmp/adaptive87-cfold-index-power-current.json
```

The checker authenticates the quoted source statements and graph rows, verifies the auxiliary and scaled-balance identities as free-ring polynomials, and includes bounded signed absdiff controls. It does not run Lean, establish a provider closure, or treat those finite controls as a proof.
