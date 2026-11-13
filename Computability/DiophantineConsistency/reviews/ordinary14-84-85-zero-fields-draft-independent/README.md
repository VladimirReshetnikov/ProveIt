# Independent source review: 84/85 zero fields

The draft separately starts from each graph's own `InternalZero` and applies
the existing source interface for evaluation in the model difference ring.
Each literal output has the same association as the five-squares source
lemma. The fields are listed in the correct order and the third is `aux-1`;
therefore the conclusion is that aux evaluates to one, not zero. The draft
does not assume positivity or claim natural-norm extraction.

The independent checker pins the graph, difference-ring and five-square source
interfaces, replays the author receipt, and checks the shifted-auxiliary zero
condition on 3,125 finite tuples. These controls are not an arbitrary-model
proof. No Lean elaboration, source/object provider compatibility, natural Pell
or carrier extraction, external file binding, or iPRA endpoint follows.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-84-85-zero-fields-draft-independent/check.py > /tmp/zero-fields8485-independent.json
cmp /tmp/zero-fields8485-independent.json reviews/ordinary14-84-85-zero-fields-draft-independent/result.json
```
