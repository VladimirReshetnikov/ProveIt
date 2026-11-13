# Natural 80 J positivity: source-only proposal

`Natural80JPos.lean` adapts the unelaborated
[81 J-shift guard proof](../ordinary14-natural81-jshift-model-draft/) to
the literal [80 graph](../ordinary14-natural-forced-gamma80-lean-draft/).
It proposes that an 80 `InternalZero` has `J>0` when port 1 is represented
by a strictly positive model element `κ`. There is no positive-beta or
positive-gamma premise. The model environment is `IΣ₁`.

The source proposes an exact ring guard cut at `J=0`, the bound
`guard<=−2` using `κ>0`, and the contradiction with a product of integer
factors equal to one, using discreteness of the difference ring. All Lean
source and dependencies are **unelaborated**; the included `#print axioms`
has not been executed. The checker pins the source and graph, inspects the
explicit strict represented-K0 premise, and exercises 300 finite guard
controls. It does not establish the model assertion, an iPRA derivation, or
symbolic-to-physical coefficient/PDF binding.

An [independent source and mathematical review](../../reviews/ordinary14-natural80-jpos-model-independent/README.md)
checks the graph guard and the discrete unit argument without elaborating the
proposed theorem.

```
python3 -I -S -B research/ordinary14-natural80-jpos-model-draft/check_source.py > /tmp/natural80-jpos.json
cmp /tmp/natural80-jpos.json research/ordinary14-natural80-jpos-model-draft/result.json
```
