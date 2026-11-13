# Narrow gamma-zero contradiction: source-only proposal

`GammaZeroNarrow.lean` contains **unelaborated source-only proposals** for
two fact-level pieces of the [natural-80 model route](../ordinary14-natural80-gamma-model-route/).
The files and dependencies have not been compiled, the tactic proofs may
need repair, and resource use is unknown. The checker pins the source and
the two cited existing files, inspects the explicit hypotheses, and runs
small finite arithmetic controls; it does not run Lean or prove the model
statements.

`first_ordinate_lower` assumes `P>0`, `n>=2`, and the first-Pell recurrence
coordinate `2*ycoord n (2*(P−1)+1)=k`, and proposes `8*P+4<=k`. The
coordinate is intended to come from
`ArithmeticPellFirstNorm.positive_parameter_solution`; separately proving
`n>=2` still requires the main-norm/k≠2 argument. Neither is assumed to
follow merely from a graph zero here.

`gamma_zero_impossible` applies the existing
`DirectMainNorm.direct_main_orientation` with its `G` argument set to zero.
It explicitly assumes `U>0`, `Y>=8`, `k>0`, `R+1<k`, `X<eta+Y*k`, and
the exact signed-magnitude main norm. The existing orientation theorem has
no positive-G premise. Given those hypotheses, the proposed source uses its
oriented main quotient, a square comparison, and strict comparison of the
two sides of the balance to derive a contradiction. It neither assumes
gamma positive nor derives any of the displayed hypotheses from the literal
80 graph.

The graph-to-magnitude norm, port representations and rank bound, the
main-norm proof of `k>2`, the recurrence-index binding, the inequalities
`R+1<k` and `X<c`, and all transport and endpoint steps remain separate
obligations. The ambient model is `IΣ₁`; no iPRA derivation or physical
coefficient/PDF binding is established. The included `#print axioms`
commands have not been executed and supply no axiom audit.

An [independent source and mathematical review](../../reviews/ordinary14-natural80-gamma-narrow-independent/README.md)
checks the displayed hypotheses and implications, without elaborating the
proposed proofs or deriving their premises from the graph.

```
python3 -I -S -B research/ordinary14-natural80-gamma-narrow-draft/check_source.py > /tmp/natural80-gamma-narrow.json
cmp /tmp/natural80-gamma-narrow.json research/ordinary14-natural80-gamma-narrow-draft/result.json
```
