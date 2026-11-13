# Independent source review: conditional arithmetic 84/85 client

The 84-to-85 source passes all arguments of the gamma-growth lemma in the
stated order, including both exact Pell coordinates, `R≥3`, positive scale
and ordinate, `X=q*w`, first-index equality and subtraction-free carrier
balance. Its resulting strict bound is passed to the conditional positive
map, together with the source graph zero and port and positivity assumptions.
The reverse direction passes the Mersenne exponent bound, exact representation,
power identity and `q | 3X` to the cancellation lemma before invoking the
conditional map on the 85 graph zero.

This is source/interface review only. The checker pins the composition and
reviewed interfaces and replays the author and three independent dependency
receipts. None of these source packets has been elaborated in Lean. The
arithmetic hypotheses are not derived here from graph zeros, and no provider
compatibility, file binding or iPRA endpoint is established.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-84-85-arithmetic-client-draft-independent/check.py > /tmp/arithmetic84-85-independent.json
cmp /tmp/arithmetic84-85-independent.json reviews/ordinary14-84-85-arithmetic-client-draft-independent/result.json
```
