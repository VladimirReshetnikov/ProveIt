# Independent source review: natural-80 gamma premises

The [fact-level draft](../../research/ordinary14-natural80-gamma-premises-draft/README.md) states mathematically sufficient premises for its proposed Pell-ordinate and size conclusions in the intended `IΣ₁` arithmetic models. Both receipts reproduce. Neither source statement assumes gamma positivity or a graph zero, and neither has been elaborated in Lean.

`large_ordinate_of_two_norms` explicitly assumes `m>0`, `eta,zeta>0`, `Y>=1`, `k=eta+zeta`, the first norm `tau²=1+m(m+1)k²`, and the main norm `d²=1+((a+1)(a+3))*c²` with `a=X*Y+Y`, `c=eta+Y*k`. The cited main Pell classification gives an ordinate `c=ycoord j a`. If `k=2`, the fact-level `Direct80IndexOne.impossible` can use its parameters `Y` as Y, `S=a+1`, its own `X=0`, and index `j`: `Y<=a+1` follows from `a=XY+Y`, and the recurrence base `(a+1)*(0+1)−1` is a by natural subtraction. Its other explicit premises are the stated positive eta/zeta, their sum 2, `Y>=1`, and the ordinate equality. This excludes `k=2` without a gamma condition.

The first-Pell classification can then supply an index n with `2*ycoord n (2*(m−1)+1)=k`; `m>0` is explicitly required by that source. Index zero would give `k=0`, contradicting positive eta and zeta; index one would give `k=2`, already excluded. Thus `n>=2`, and the separate narrow draft's monotonic recurrence bound yields `8m+4<=k`. All these cited source declarations and the natural-subtraction and recurrence rewrites still require coherent Lean elaboration.

`narrow_inequalities` separately assumes `q>=2`, `q<=X`, `q³<=Y`, `eta>0`, `8*X*Y²+4<=k`, and `R+q³+q+1<=q⁴`. Since `Y>=1`, these imply `q⁴=q*q³<=X*Y<=X*Y²<k`, while the rank bound gives `R+1<=q⁴`; hence `R+1<k`. Also `X<=X*Y²<k<=Y*k<=eta+Y*k`, proving the second conclusion. The assumptions are fact-level: the draft does not derive either norm, the port/rank bounds, or a literal graph valuation from an 80 zero.

The checker pins the draft and five cited source files, verifies the exact signatures and instantiation tokens, and checks the relevant elementary algebra as sparse polynomials. Its finite size controls are not a model proof. The source's tactic scripts, instances, transitive providers and two axiom-report commands remain unexecuted; symbolic coefficient/PDF bindings and the iPRA endpoint remain separate obligations.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural80-gamma-premises-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural80-gamma-premises-independent/result.json
```
