# Independent source review: 85/86 q-cubed quotient fact

The proposed fact represents the signed root by the natural pair
`(M*P+b*Y,M*r)`, converts its squared difference to a magnitude square and
uses the positive-scale quotient lemma. Since Q=q³ divides M, the resulting
magnitude is divisible by Q; the pair congruence yields `Q | bY`. For
`q=1+b`, the displayed Bezout certificate gives a unit for b modulo Q, so
`Q | Y`. Positive Y and D make the two natural quotients s and tau positive.
The argument does not choose the sign of the original root.

The checker pins the source interfaces and author receipt and independently
tests both signs and the zero-radicand boundary on finite inputs. This is a
fact-level source review only: graph field extraction and witness transfer,
Lean elaboration, provider compatibility, external-file binding and iPRA
remain open.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-85-86-quotient-facts-draft-independent/check.py > /tmp/qcube-quotient-independent.json
cmp /tmp/qcube-quotient-independent.json reviews/ordinary14-85-86-quotient-facts-draft-independent/result.json
```
