# Proposed forward norm extraction and positive shear

This is an **unelaborated source-only ordered-ring client** for the forward
direction of the current2011 71/60 → 72/46 shear. It proposes deriving the
strict inequality `V<y_parent` from the actual 71/60 ring value zero,
positive inputs, positive beta, the existing `FreshCarrierSpheres.Facts`,
and the explicit signed `2*rank<c` premise. Its separate literal-evaluator
corollary uses the checked 71/60 `eval_expression` interface. No new Lean
theorem, model-natural witness, graph zero bridge or iPRA endpoint has been
checked here.

Write `d=Carrier65.core p v`, `I=d.i*d.c²`,
`A=d.delta*(d.f²−1)`, and `U=FreshCarrierSpheres.auxiliary d`. The pinned
checked 71/60 source defines

```
value71 = d.P² + U² + (d.Q*d.W−1)² + (I²−A)² − 2.
```

The existing `first_ne_zero`, `auxiliary_ne_zero` and `square_ge_one`
give `d.P²>=1` and `U²>=1`. At `value71=0`, nonnegativity forces
`U²=1` and `I²−A=0`. Therefore `A=I²`; rewriting U as the corresponding
square-coefficient norm lets `square_aux_ne_neg_one` exclude U=−1, so
`sq_one` gives U=1. This is the same extraction used inside the checked
`OrdinarySphere7160Generic.zero_iff94` proof, isolated here for reuse.

Positive i and the existing `c_pos` give I>0, hence A=I²>0 and A>=1 by
model-ring discreteness. Positive f gives f>=1; f=1 would make A=0, so
discreteness gives f>=2. The inputs also give y>=1, T>=1 and c>=1. Given
the explicit signed half-bound, the separately proposed
[`ShearOrderDraft.graph_carrier_ne_one`](../current2011-shear-v-not-one-order-draft/README.md)
rules out `V=1`; its `positive_shear` order lemma then gives `V<y_parent`
from U=1. No `f² mod c` premise is used.

The pinned 71/60 literal evaluator asserts that its expression evaluates
to its `value71`; the latter has the same definition as the generic value.
The draft proposes a corollary accepting this literal evaluation zero.
It does not independently elaborate their definitional identification.

The signed half-bound remains an explicit premise. A separate
[current-port cast draft](../current2011-shear-current-port-cast-draft/README.md)
proposes deriving it from the actual shifted parent zero, but that draft and
its predecessors are also uncompiled. Strict positivity of `y_parent−V`
in the difference ring must be represented by a model-natural positive
witness; then the literal child shear identity, same-valuation non-y
coordinates and zero must be proved. The separate reverse magnitude
construction and final same-no-zero/iPRA clients remain required.

[`ForwardNormOrder.lean.src`](ForwardNormOrder.lean.src) imports inert local
predecessor name `ShearOrder` as if materialized. Its tactic steps, implicit
arguments, literal-value change and import/provider choices are untested.
The read-only checker pins and checks interface markers and source structure;
it is not a Lean parser or proof checker.

```
python3 -I -S -B research/current2011-shear-forward-norm-order-draft/check.py > /tmp/shear-forward-norm.json
cmp /tmp/shear-forward-norm.json research/current2011-shear-forward-norm-order-draft/result.json
```

No Lean/build or staging operation is performed.
