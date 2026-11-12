# Fact-level premises for the natural-80 gamma contradiction

`GammaPremises.lean` proposes **unelaborated source-only** lemmas supplying
two ingredients of the [narrow gamma-zero draft](../ordinary14-natural80-gamma-narrow-draft/).
No Lean build has been run. The checker pins the source and relevant
interfaces, checks that the hypotheses and axiom-print commands appear, and
tests finite numerical size implications. It does not prove the Lean
statements, model semantics, or an iPRA result.

`large_ordinate_of_two_norms` takes positive `m`, `eta`, `zeta`, `Y>=1`,
`k=eta+zeta`, the explicit first Pell norm, and the explicit main Pell norm.
It proposes `8*m+4<=k`. The source obtains a main Pell index via
`ArithmeticPellClassification.solution_index` and invokes
`Direct80IndexOne.impossible` with its parameters `S=a+1` and `X=0`, so its
base `S*(X+1)−1` is the graph's main base `a=XY+Y`. It then obtains the
first-Pell index from `ArithmeticPellFirstNorm.positive_parameter_solution`,
excludes index zero and one using `k>2`, and applies the separate narrow
`first_ordinate_lower` proposal. All norm and positivity hypotheses remain
explicit; no graph zero or gamma positivity is assumed.

`narrow_inequalities` takes explicit bounds `2<=q`, `q<=X`, `q³<=Y`,
`eta>0`, `8*X*Y²+4<=k`, and `R+q³+q+1<=q⁴`. It proposes the two
conclusions `R+1<k` and `X<eta+Y*k` required by the narrow gamma-zero
contradiction. The proof route uses `q⁴<=X*Y<=X*Y²` and the first-Pell
bound. No assumption about gamma appears.

The remaining work includes binding the literal 80 zero to these first and
main norm equations, representing and bounding the selected ports, proving
the signed main magnitude and rank premises, elaborating all proposed
source and dependencies, and completing the iPRA and physical/PDF bindings.
The source's two `#print axioms` commands have not been executed.

An [independent source and mathematical review](../../reviews/ordinary14-natural80-gamma-premises-independent/README.md)
checks the displayed norm hypotheses, index instantiation and inequalities;
it does not derive those hypotheses from the graph or elaborate Lean.

```
python3 -I -S -B research/ordinary14-natural80-gamma-premises-draft/check_source.py > /tmp/natural80-gamma-premises.json
cmp /tmp/natural80-gamma-premises.json research/ordinary14-natural80-gamma-premises-draft/result.json
```
