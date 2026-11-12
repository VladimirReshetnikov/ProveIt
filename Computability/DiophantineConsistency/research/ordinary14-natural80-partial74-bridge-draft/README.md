# Natural 80 to partially shifted 74: source proposal

`Natural80Partial74.lean` proposes an **unelaborated source-only** ring and
model bridge between the literal [80/107 natural graph](../ordinary14-natural-forced-gamma80-lean-draft/)
and the positive-74 graph. None of its source rewrites, imported drafts, or
model steps has been compiled in this packet. The checker pins the source
and three JSON graphs, verifies the 82-to-80 two-gate edit, and checks 300
finite signed modular evaluations of the proposed composed transport; it
does not run Lean or establish the unbounded identity or a model theorem.

Over a ring, the proposed 80-to-82 identity subtracts one from slots 0 and
12, corresponding to J and gamma. Composing with the existing proposed
82-to-86 and 86-to-74 ring bridges yields a natural-model valuation for the
74 graph that leaves slots

```
0=J, 3=f, 8=r, 11=y, 12=gamma
```

unchanged and increments the other nine slots. This includes the increment
of the 74 guard quotient h; it is essential to the guard identity. The
proposed `InternalZero` equivalence uses this related valuation, not the
same valuation. It has no beta, K0, sign, or positivity premise because it
is only an algebraic transport, if elaborated.

In particular, a hypothetical natural 80 zero with `gamma=0` would be
carried to a 74 zero whose gamma slot is still zero. This is the interface
needed for the [gamma-zero model route](../ordinary14-natural80-gamma-model-route/);
it does not itself force J, gamma, or any other coordinate positive, bind
literal factors to main-norm hypotheses, establish an iPRA derivation, or
link symbolic ports to physical bytes or the PDF. The two `#print axioms`
commands have not been executed.

An [independent source and mathematical review](../../reviews/ordinary14-natural80-partial74-bridge-independent/README.md)
checks the literal graph cuts and related valuation without establishing a
Lean theorem or unrestricted zero-existence equivalence.

```
python3 -I -S -B research/ordinary14-natural80-partial74-bridge-draft/check_source.py > /tmp/natural80-partial74.json
cmp /tmp/natural80-partial74.json research/ordinary14-natural80-partial74-bridge-draft/result.json
```
