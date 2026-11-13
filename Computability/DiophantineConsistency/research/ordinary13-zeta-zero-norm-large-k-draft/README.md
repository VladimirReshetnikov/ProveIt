# Proposed zeta-zero first/main norm large-k lemma

This is an unelaborated fact-level source proposal; it does not establish a
literal graph zero, natural-root extraction, same-index witnesses, model
provider coherence or an iPRA endpoint. It addresses the `zeta=0`, `k=eta`
case with the explicit premise k>0; the simultaneous k=0 boundary is handled
only by a separate conditional main-norm obstruction draft.

For k=2, the main ordinate is `c=k+Y*k=2+2Y`. The graph-shaped parameter
`A=XY+Y+2` satisfies `1<c<2A`, because `2A−c=2XY+2>0`. With the explicit
norm `d²=1+Delta*c²` and `A²=Delta+1`, the separately proposed
`no_main_square` theorem excludes this case. This geometry is different from
the existing eta-natural lemma that assumes positive zeta; no such
assumption is made here.

For positive X,Y,k, the source proposes using the first norm
`tau²=1+m*(m+1)*k²`, m=XY², to exclude k=1 via `two_le_ordinate`. It then
combines k≥2 with the main-square k≠2 result and the source-only first-Pell
descent to get `k≥8XY²+4`. Both square norms, Delta identity and positivity
are explicit inputs. Every imported theorem and tactic remains subject to
Lean and provider validation.

The checker pins the exact source inputs and verifies 9,900 finite k=2 main
square exclusions and 47 bounded Pell solutions. It does not prove the
model result. From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-zeta-zero-norm-large-k-draft/check.py | cmp - research/ordinary13-zeta-zero-norm-large-k-draft/receipt.json
```
