# Eta-natural first/main norm large-ordinate client

`EtaNaturalNormLargeK.lean.src` is an **unelaborated source-only proposal**
for natural parameters in an arbitrary `IΣ₁` model. It explicitly assumes
`X>0`, `Y>0`, `zeta>0`, an arbitrary natural `eta`, a natural `Delta`, and
natural roots `tau,d` satisfying

```
k = eta+zeta,  m = X*Y²,  A = X*Y+Y+2,  c = eta+Y*k
A² = Delta+1
 tau² = 1+m*(m+1)*k²
 d² = 1+Delta*c².
```

Under these assumptions it proposes both `k>2` and `k≥8*X*Y²+4`. It does
not assume positive `eta`, so the interface includes `eta=0`; `zeta>0` is
still a necessary explicit premise of this client. It does not establish any
of these assumptions for an equation zero.

The first norm and `k>0` give `k≥2` via the pinned model-source theorem
`ArithmeticPellFirstNorm.two_le_ordinate`, with the positive predecessor
`m−1` used only after proving `m>0`. For the remaining case `k=2`,
`zeta≥1` gives `eta≤1`; therefore `c=eta+2Y` satisfies `1<c<2A`. The
separately pinned research draft `ModelMainSquareGapDraft.no_main_square`
excludes a square between `(A*c−1)²` and `(A*c)²` under the displayed
main norm. This argument covers both eta-zero and positive-eta cases without
presuming eta positive. Finally, the pinned unelaborated source draft
`AuxRootBoundsModelDraft.first_ordinate_large` supplies the large lower bound
from `k>2` and the explicit first norm.

`MainSquareGap` and `AuxRootBounds` in the imports are names of proposed
research-source providers, not built modules. The gap draft itself imports
`Compact44.P72Root`, and both drafts have transitive provider requirements;
none was rebuilt or checked here. This packet does not establish exact graph
residuals, root extraction and orientation, beta or port representation,
coordinate zero maps, or any internal iPRA theorem. In particular, a natural
main square root `d` is an **assumption**, not the output of a graph
argument. Lean parsing, types and proof terms remain unchecked.

The proof closely adapts `two_ordinate_impossible` from the pinned gap draft,
but keeps `eta≤1` instead of deriving `eta=1`. The source receipt records
the pins and 912 exact integer gap controls over both `eta=0,zeta=2` and
`eta=zeta=1`, together with 999 first-norm `k=1` controls. These finite
controls can catch arithmetic mistakes but are not the model proof.

From this directory, reproduce the receipt with

```
python3 -I -S -B check.py > /tmp/eta-natural-norm-k.json
cmp result.json /tmp/eta-natural-norm-k.json
```
