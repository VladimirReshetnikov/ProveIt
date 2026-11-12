# Independent source review: eta-natural J positivity

The pinned source in `research/ordinary13-eta-natural-J-positive-model-draft/`
is a conditional, unelaborated graph-level proposal. The author's checker
reproduces. The independent checker evaluates the actual prototype's graph
prefix symbolically over a free commutative ring after setting `n_J=0`, pins
the generated graph and imported interfaces, and checks 5,184 finite sign
instances. Run `python3 -I -S -B check.py | cmp - receipt.json` in this
directory. None of those checks proves the Lean source or its providers.

At `v 0=0`, the actual graph prefix has `b=0`, `q=1`, and `X=v 6`. With
`F=v 1+1`, `alpha=v 2+1`, and natural second port `K0=p 1`, direct
substitution gives the exact signed expression

```
Z = F − (1−F−alpha)*(X+K0).
```

The first two shifts give `F≥1` and `alpha≥1`; the difference-ring embeddings
of `X` and `K0` are nonnegative. Hence `1−F−alpha≤0`, the product with
`X+K0` is nonpositive, and `Z≥F>0`. The source's `hZ` has this orientation
and does not insert the distinct residue-90 `X*Y*q` term. The first signed
norm returned by the exact unit bridge gives `Z²=b²*(...)`; at `b=0`, it
gives `Z²=0`, contradicting `Z>0`. The `signed_norms` result is destructured
in the correct first-conjunct position.

The theorem quantifies `p : Fin 4 → ℕ`, then forms integer constants
`fun j => (p j : ℤ)` and embeds each model-natural port. In particular
`P72Root.cast_port` has the source-level integer-to-difference-ring equality
needed for the first and second port. The `K0≥0` reasoning uses that exact
natural-port specialization; no claim is made for arbitrary signed integer
ports. As a first-factor-only control, `F=alpha=1`, `X=0`, `K0=−1` gives
`Z=0`, so this particular contradiction cannot simply drop the sign premise.
It is not a full prototype zero or a counterexample to another argument.

No mathematical sign or interface mismatch was found in these cuts. The
actual `simp`, cast rewriting, order and `linarith` calls, the imported
factor-unit bridge, and the resulting `#print axioms` have not been checked
by Lean. The port tuple must still be tied to the selected compact coefficients;
the eta-zero contradiction, zero maps, provider authentication, PDF binding,
and internal-iPRA endpoint remain separate obligations.
