# Natural 80 guard gap: source-only proposal

`Natural80GuardGap.lean` proposes deriving `F+alpha<q` at the partially
shifted 74 valuation of a natural-80 zero. The source explicitly assumes
beta and K0 are represented by model elements, `beta>0`, and `K0>0`; it
does not assume gamma, f, r, or y positive. It uses the proposed 80 J
positivity and partial transport, the 74 guard unit, and the existing
source-only literal guard evaluation. The key contradiction is that if
`C=q−F−alpha<=0`, then

```
C*(X+K0)+(q−F)−b*h <= 0,
```

because `F>=1`, `h>=1`, and `q=1+b`, whereas the guard unit equals one.
The inequality and transport are proposed in the difference ring, with
the final comparison reflected back to the model.

This is **unelaborated source only**; its imported drafts, tactics, and
model interfaces have not been checked by Lean. The checker pins the source
and graph, samples finite inputs, and constructs 72 guard-unit instances to
exercise the implication. These finite tests do not prove the unbounded
model statement, any iPRA derivation, or symbolic-to-physical coefficient
or PDF binding. The `#print axioms` command has not been executed.

An [independent source and mathematical review](../../reviews/ordinary14-natural80-guard-gap-independent/README.md)
checks the guard identity and stated assumptions without elaborating Lean.

```
python3 -I -S -B research/ordinary14-natural80-guard-gap-draft/check_source.py > /tmp/natural80-guard-gap.json
cmp /tmp/natural80-guard-gap.json research/ordinary14-natural80-guard-gap-draft/result.json
```
