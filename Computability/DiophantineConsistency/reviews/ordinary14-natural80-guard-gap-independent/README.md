# Independent source review: natural-80 guard gap

The [source draft](../../research/ordinary14-natural80-guard-gap-draft/README.md) proposes a mathematically sufficient guard argument for `F+alpha<q` at the partially shifted 74 valuation of an 80 zero. Its displayed hypotheses require represented positive beta and K0, but no positivity of gamma, f, r or y. Both source receipts reproduce; the proposed Lean theorem and its dependencies remain unelaborated.

The partial valuation maps the natural-80 F and h inputs to successors in the 74 valuation, so `F>=1` and `h>=1`, independently of gamma. The proposed J-positivity client uses the represented positive K and the original zero; the 74 guard-unit client then needs represented positive beta and positive J, w and s. The inspected signatures have no all-slots-positive premise. The separate `strict_of_zero` source does have such a premise and is not used in this proposed gap argument.

The independent checker compares the literal 74 graph to the pinned JSON, verifies the selected guard field and its relevant rows, and checks the ring identity

```
guard = C*(X+K)+(q−F)−b*h
      = C*(X+K)+1−F−b*(h−1),   q=1+b.
```

Here `b` and `X+K` are nonnegative embedded model values, and the two shifted coordinates give `F,h>=1`. If `C<=0`, every term on the second line is nonpositive, so the guard is at most zero. That contradicts the proposed guard unit `guard=1`; hence `C=q−F−alpha>0`, and order reflection gives `F+alpha<q`. Beta positivity is required by the cited unit extractor, while strict K positivity is used by the cited J proof. No gamma positivity is hidden in these displayed signatures or this arithmetic implication.

The source's casts, literal guard rewrite, partial model transport, ring-order tactic steps, model instances and imported unit client are not checked by Lean. The selected symbolic port representations and positivity, rank bounds for MC/MF, provider and axiom closure, iPRA derivability and coefficient/PDF binding remain separate obligations. The single `#print axioms` command is unexecuted.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural80-guard-gap-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural80-guard-gap-independent/result.json
```
