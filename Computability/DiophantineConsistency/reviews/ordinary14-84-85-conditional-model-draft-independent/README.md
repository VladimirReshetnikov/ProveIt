# Independent source review: conditional positive 84/85 maps

The proposed maps use the required opposite slot changes: `w → q*w` and
`gamma → gamma-w` in the 84-to-85 direction, and `X → w`,
`gamma → gamma+w` in the other direction. The first explicitly assumes
`w<gamma`, which justifies both positivity and `P72Root.ι_tsub`; the second
explicitly assumes `q | X`, and positivity of `X` forces its quotient `w` to
be positive. The ring identity is used in the correct output-rewrite direction
in each implication, under the explicit beta-port cast assumption.

The checker pins the reviewed source, ring client and cast interface, replays
the author receipt, and independently compares the literal fields for 300
positive examples in each direction, including independently chosen divisible
85 inputs. Finite controls are not model proofs. Lean elaboration, ring
provider compatibility and the derivation of the strict and divisibility
premises from graph zeros remain open; no unconditional graph equivalence or
iPRA endpoint is established here.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-84-85-conditional-model-draft-independent/check.py > /tmp/conditional84-85-independent.json
cmp /tmp/conditional84-85-independent.json reviews/ordinary14-84-85-conditional-model-draft-independent/result.json
```
