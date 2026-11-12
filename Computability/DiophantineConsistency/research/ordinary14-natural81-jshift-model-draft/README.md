# Natural 81-to-82 J shift: source proposal

`Natural81JShift.lean` is an **unelaborated source-only proposal** for a
ring and model bridge from the [natural-81 graph](../ordinary14-natural-forcedj81-lean-draft/)
to the [natural-82 graph](../ordinary14-natural-forced82-lean-draft/). Its
graph imports, proof scripts, tactic behavior, and resource needs are
unverified. The checker pins the graphs and source, verifies the literal
gate edit, and exercises finite signed ring and guard controls; it does not
run Lean or prove the model assertions.

For arbitrary commutative-ring valuations and integer ports, the proposed
identity compares the 81 output at `v` with the 82 output at a valuation
whose slot 0 is `v 0−1` and whose other slots are unchanged. It does not
claim pointwise equality at the same valuation. The model proposal relates
two natural valuations using a successor at slot 0, proves the intended
conditional `InternalZero` equivalence, and proposes the corresponding
existential transport by incrementing in one direction and taking the
predecessor in the other.

The crucial zero-to-predecessor step explicitly assumes a model element
`κ` satisfying `(p 1 : DiffRing V) = ι κ` and `0 < κ`. At a hypothetical
81 zero with `J=0`, the proposed guard cut evaluates to

```
−(ι(n_F)+ι(n_alpha)+1)*(ι(n_w)+1+ι(κ))−ι(n_F) <= −2.
```

The output product equals one. Discreteness of the difference ring implies
that no product involving a factor at most −2 can equal one, yielding
`J>0`. This proof does not need to exclude −1 for any other factor. The
unbounded source proof and its associated ring simplifications remain to be
elaborated; the finite controls are not substitutes.

The model assumptions are `ORingStructure` and `𝗜𝚺₁`. Supplying the
selected symbolic port's representation and positivity, elaborating all
dependencies, proving an iPRA endpoint, and binding symbolic ports to
physical bytes or the PDF are separate tasks.

An [independent source and mathematical review](../../reviews/ordinary14-natural81-jshift-model-independent/README.md)
checks the graph edit, guard contradiction and valuation directions; it does
not elaborate the model statements.

```
python3 -I -S -B research/ordinary14-natural81-jshift-model-draft/check_source.py > /tmp/natural81-jshift.json
cmp /tmp/natural81-jshift.json research/ordinary14-natural81-jshift-model-draft/result.json
```
