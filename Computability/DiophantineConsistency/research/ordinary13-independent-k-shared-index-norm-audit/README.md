# Independent-k boundary with exactly shared Pell indices

Even imposing the exact scalar index relation `R=2n-1`, first-index decomposition, rank window, and both Pell norms does not by itself force `eta≤k`. The family below has `eta>k` and uses the main Pell index **R itself**, strengthening the previous [independent-main-index boundary](../ordinary13-independent-k-high-index-norm-audit/). It does not supply the candidate graph's actual rank, signed roots, strong factor or auxiliary factor, so it is not a full graph zero.

For any ordinary integers `n≥14` and `q≥2n+2`, set

```
J=1, beta=q-1, X=q, Y=q³, M=X*Y²,
a=X*Y+Y, R=2n-1, mu=q⁴.
```

For any `A≥2`, define `(x₀,y₀)=(1,0)` and

```
xⱼ₊₁=A*xⱼ+(A²-1)*yⱼ,
yⱼ₊₁=xⱼ+A*yⱼ.
```

Take `(tau,y)=(xₙ,yₙ)` for `A=2M+1` and set `k=2y`. Independently take `(g,c)=(x_R,y_R)` for `A=a+2`. Set `eta=c-Y*k`; the growth proof below shows eta is a natural greater than k. Both Pell norms then hold:

```
tau² = 1+M*(M+1)*k²,
g²   = 1+(3+4a+a²)*c².
```

The first recurrence has `yₙ≡n (mod 2M)` and `yₙ≥n`, so there is natural s with `k=2n+4M*s`. With the chosen scalar R and mu, `R≥26`, `R+1<mu`, `(2n) mod mu=R+1`, and `R+q³+q+1≤mu`; see the preceding audit's nonnegative window identity. Also `13≤n<R`.

To prove `c>(Y+1)k`, note that for the recurrence above and every `j≥1`, the identity `A*yⱼ-xⱼ=yⱼ₋₁≥0` yields `yⱼ₊₁≤2A*yⱼ`, while `yⱼ₊₁≥A*yⱼ`. Thus

```
k ≤ 2*(2*(2M+1))^(n-1) ≤ 2*(6*q⁷)^(n-1),
c ≥ (a+2)^(R-1) ≥ q^(8n-8).
```

Also `Y+1≤2q³`. For q≥24 and n≥9,

```
q^(n-4) ≥ 24^(n-4) = 6^(n-4)*4^(n-4)
          > 6^(n-4)*(4*6³) = 4*6^(n-1),
```

because `4⁵=1024>864=4*6³`. Multiplying by the appropriate power of q gives the required strict comparison. Hence `eta=c-Y*k>k`. The stated hypotheses imply q≥30, so all bounds apply.

The actual compact q, with J=1 and `beta=2^(67*8807)-1`, is symbolic and supports every `14≤n≤floor((q-2)/2)`. As q varies, n can be arbitrarily large; for fixed compact q the displayed range is finite. The huge fixed value is not materialized.

The scalar R here is selected as `2n-1`, not proved equal to the candidate's polynomial rank for its actual F, alpha and compact mask ports. The main and first **natural** norms do not bind their signed graph roots; strong and auxiliary factors are also not supplied. These missing constraints could exclude the family. Thus the audit does not establish a child zero with `k<eta`, disprove a witness replacement, or provide any model/Lean/iPRA proof.

The checker verifies the generic Pell invariant and key growth-step identity as exact integer polynomials, pins the recurrence source, and runs small exact controls of all displayed scalar conditions. The induction and uniform inequality above establish the general family. From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-independent-k-shared-index-norm-audit/check.py | cmp - research/ordinary13-independent-k-shared-index-norm-audit/receipt.json
```
