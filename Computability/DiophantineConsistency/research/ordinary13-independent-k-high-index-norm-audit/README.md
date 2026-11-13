# Independent-k boundary with a high first Pell index

The inequality `k≥eta` does not follow merely from the two natural Pell norms and an arbitrarily high first Pell index. More strongly, the family below also meets the **scalar forms** of the first-index decomposition, rank lower bound, congruence and window. The introduced R is a chosen scalar, not the candidate graph's computed rank, and no complete graph zero is claimed.

For any ordinary integers `n≥14` and `q≥2n+2`, let

```
J=1, beta=q-1, X=q, Y=q³, m=X*Y²,
A=2m+1, D=A²-1=4m(m+1).
```

Start `(x₀,y₀)=(1,0)` and use the exact Pell recurrence

```
xⱼ₊₁=A*xⱼ+D*yⱼ,
yⱼ₊₁=xⱼ+A*yⱼ.
```

Set `tau=xₙ` and `k=2yₙ`. The norm is preserved, so `tau²=1+m(m+1)k²`. Since `A≡1` and `D≡0` modulo `2m`, induction gives `yₙ≡n (mod 2m)`. Also `yₙ≥n`. Thus some natural s satisfies `k=2n+4m*s`.

Set the **abstract scalar** `R=2n-1` and `mu=q⁴`. Then `R≥26`, `(2n) mod mu=R+1`, and `R+q³+q+1≤mu`. The last inequality follows from the exact identity

```
q⁴-q³-q-2n = (q-1)*(q³-2) + (q-2n-2),
```

whose right side is nonnegative under the stated q bound.

Independently take `a=X*Y+Y`, `B=a+2`, `E=B²-1`, and the same recurrence with parameters B,E. Put `L=(Y+1)*k+1` and let `(g,c)` be its Lth pair. Its norm is `g²=1+E*c²` and `E=3+4a+a²`. The recurrence has `xⱼ≥1` and `yⱼ≥j` by induction, so `c≥L`. Therefore `eta=c-Y*k` is natural and `eta≥k+1`, while `c=eta+Y*k` holds exactly. This supplies both norms with `k<eta` and the displayed first-index conditions for every such n and q.

For the fixed compact beta, `q=beta+1=2^(67*8807)` supports this construction for every `14≤n≤floor((q-2)/2)`. With q allowed to vary, n is arbitrarily large; for a fixed q, the displayed range is finite. The chosen main index and its Pell coordinates can be enormous and are kept symbolic: the checker never iterates to L or materializes the fixed beta.

The selection `R=2n-1` is not shown to equal the actual candidate graph's rank, and neither the signed first/main graph roots nor the strong and auxiliary factors are supplied. The exact-index theorem's hypotheses are therefore not all met, and this is not a full graph zero, a proof that the compact graph admits `k<eta`, or an existential zero-map counterexample. No Lean or iPRA proof is claimed.

The checker verifies the Pell norm-step and scalar-window identities as exact multivariate integer polynomials, checks the pinned recurrence shape, and runs small first-index and main-recurrence controls. The all-index argument is the induction above, not the finite controls. From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-independent-k-high-index-norm-audit/check.py | cmp - research/ordinary13-independent-k-high-index-norm-audit/receipt.json
```
