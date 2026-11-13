# Independent review: independent-k two-norm positivity

The two-norm argument is valid over the standard integers under its stated port hypotheses `beta>0`, `K0>0`, `MC<beta`, `MF<2*beta`, with all ports and witness inputs nonnegative. It assumes only the candidate's actual first and main residuals vanish. In particular it does not need an eta/k inequality or a chosen Pell index.

At k=0, the first norm gives `B=b*(r±1)`. If `C=q-F-alpha>0`, the shifted positive F and alpha give `0<G≤q²-2`. If `C≤0`, its negative B forces `r=0, B=-b`. With `t=-C≥0` and `d=X+K0≥1`, the exact expressions are `F=b-t*d`, `alpha=1+t*(d+1)` and `G=q+t*(1+q*d)`. Writing `d=1+d0`, `F=1+e`, so `q=2+t*d+e`, the nonnegative slack is

```
q²-2-G = t*(d-1)+t*d*e+3e+e².
```

Thus both branches have `0<G≤q²-2`. The stated strict port bounds then give `0<R+1<q⁴`; the polynomial slack for the resulting rank cap is `(q-1)*(q+2)>0`.

The actual main residual implies `U² | Dstar²`; standard integer square divisibility and `U=q⁵*s` give `q⁵ | H*(R+1)` at k=0. As `q³ | a` and `H=3+4a`, `gcd(H,q⁵)` is either 1 or 3, and in the latter case divides q. Hence `q⁴ | R+1`, contradicting its strict bounds. This reasoning does not cancel 3 modulo q and remains valid when 3 divides q.

The hypotheses do yield a **standard-integer full-zero ⇒ k>0 corollary** at the exact fixed symbolic compact tuple. The independently checked factor syntax and exhaustive modulo-four exclusions show that product-output zero forces each integer factor to +1, hence both residuals vanish. The fixed tuple uses the same beta, K0, MC and MF: beta is positive, the nonnegative kernel contains `rho^30` so K0>0, lowNat is strictly less than beta because its special digit is below the maximal digit, and `MF=beta+highNat<2beta` because all high digits are below the base and the final high digit is zero. These are source-recipe and ordinary integer deductions; the retained compact bound declarations are separately pinned and not assumed to have been replayed in Lean.

The theorem says nothing about `k≥eta` or the child's unrestricted equivalence to the parent. For arbitrary IΣ₁ models, factor-unit extraction, graph bindings, model port casts and inequalities, signed square divisibility and the q-power/gcd argument must all be formalized and compiled with coherent providers. The receipt is not an iPRA proof or PDF binding.

The checker independently certifies both branch slack identities and rank cap, checks the actual fixed tuple and digit recipes, reproduces the four-factor mod-four receipt and the author's audit, and runs bounded gcd controls. The quantified divisibility argument above is mathematical; finite controls do not prove it. From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-independent-k-two-norm-kpositive-independent/check.py | cmp - reviews/ordinary13-independent-k-two-norm-kpositive-independent/receipt.json
```
