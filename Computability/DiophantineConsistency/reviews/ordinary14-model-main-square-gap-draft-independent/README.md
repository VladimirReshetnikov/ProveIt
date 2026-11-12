# Independent source review: model main-square gap

**Source review passes; not elaborated.** Under the proposed natural-model
assumptions `A>0`, `1<c<2A`, `A²=Delta+1`, and
`d²=1+Delta c²`, let `n=Ac`. Exact expansion gives

```
d²−(n−1)² = c(2A−c) > 0,
n²−d² = c²−1 > 0.
```

Since `Ac≥1`, the predecessor `t=Ac−1` is a natural model element and
`P72Root.ι_tsub` has the needed cast hypothesis. The ordered-ring comparison
and the source `ι_lt_ι` transport these inequalities to the model naturals,
where they give both `t<d` and `d<Ac=t+1`, contradicting discreteness.
The proposed graph-shaped specialization uses positivity and `eta+zeta=2`
to derive `eta=zeta=1`; then `c=2Y+1` satisfies `1<c<2(XY+Y+2)`.
Both the Delta identity and the natural main-square equation are explicit
premises, not hidden graph facts.

The checker pins the proposed source and referenced ordered-model interfaces,
verifies both gap identities exactly in a sparse integer polynomial ring,
replays the author inventory, and independently checks finite generic and
graph-shaped controls plus the strict-bound boundary cases. These checks do
not elaborate Lean. In particular `nlinarith`, cast simplification, proof
reduction, source/object provider compatibility, graph main-scale quotient
extraction, and the iPRA endpoint remain unverified. No Lean process is run.

From `Computability/DiophantineConsistency`, run:

```
python3 -I -S -B reviews/ordinary14-model-main-square-gap-draft-independent/check.py
```

Compare stdout with `result.json`.
