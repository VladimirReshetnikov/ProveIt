# Independent source review: fact-level early-index wrapper

The proposed wrapper uses the actual residue-root **natural norm** as an explicit premise and does not require an equality to original `core.z`. Positivity of X and Y gives `Q=X*Y²>0`; `positive_parameter_solution Q tau k` then supplies the model Pell index n and both requested coordinates. From `Y=q³*s` the source correctly derives `q⁴ | B+1=2Q`, and separately has `2Q | B+1`. Applying `residue_quotients` at these two moduli gives respectively `k=2n+q⁴*(2t)` and `k=2n+4Q*w`.

The rank premise is `q⁴ | magnitude(R+1,k)`. `magnitude_mod` has the orientation `(R+1)%q⁴=k%q⁴`, and the strict rank window reduces its left side to R+1. Substitution of the q⁴ quotient yields `(2n)%q⁴=R+1`; the remainder bound gives the two claimed lower bounds. With `R>=24`, the source's strict inequality yields `n>=13`. These statements do not imply exact `2n=R+1`: the independently checked symbolic first-index control has `2n=R+1+q⁴`, while satisfying the early congruence. It is a partial assignment, not a full graph zero.

The actual graph-to-natural norm, rank-divisibility cut, rank window, compact port representation, imports and provider closure are explicit external premises or obligations; later exact-index and parent bridge steps are absent. Source signatures and finite arithmetic controls were independently checked, and the author's receipt reproduces. No Lean elaboration, axiom report, nonstandard-model theorem or iPRA endpoint has been established by this review.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-residue-first-index-model-independent/check.py | cmp - reviews/ordinary13-residue-first-index-model-independent/result.json
python3 -I -S -B research/ordinary13-residue-first-index-model-draft/check.py | cmp - research/ordinary13-residue-first-index-model-draft/receipt.json
```
