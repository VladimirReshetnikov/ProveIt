# Independent source-flow review: positive 83 gamma calibration

This reviews the graph/witness flow of
`research/ordinary13-positive83-gamma-calibration-model-draft/`. No Lean,
build, staging, full import resolution or provider replay was performed.
The receipt pins the source and direct interfaces and reproduces the author's
receipt.

`calibration_of_root` begins with a positive 83 zero and an **explicit**
positive replacement for position 8 that zeros the 81 first residual. It uses
the proposed 83→81 non-first transport and then the proposed 81→85 forward
image. The compact wrapper obtains that replacement via
`Positive83CrossRootDraft.reverse`, whose inspected source calls the
83-root helper directly. This displayed proof path does not invoke
`zero83_to84`, `gamma_of_calibration`, or the gamma cut it is constructing.
The file imports `Positive83To84Bridge` to state its target, so this is a
bounded source-flow finding, not a claim of a complete resolved import DAG
or authenticated provider closure. The cross-root module also imports its
forward client; all such draft modules still have to be built coherently.

The receipt independently compares the actual 83 and 85 graph fields after
the replacement and predecessor/forward image. Additive free-ring
normalization verifies equality of q, X, Y, U, the signed rank row, k, c,
Delta and the three non-first residual fields, with the replacement r treated
as a distinct independent variable. In particular, no equality between the
original and replacement r is assumed. The natural `rank83` equality in the
source is a model-natural expression; the separate cast of a truncated rank
to the signed graph row depends on the gap/representation source facts.

The source obtains n and w together from `compact_early_index` for the **same
85 valuation**, and passes that exact n/w pair and its hypotheses to
`Positive81ExactMainDraft.exact_and_main`. The latter proposes a single
oriented main root with both its Pell coordinates and its no-extra-term
carrier balance. The client retains that main and n/w when constructing
`R,W,main` for `GammaCalibration`; it does not substitute an unrelated
root or assume the original 83 first root equals the replacement first root.
The exact polynomial identity checked for the W conversion is

```
Y=q³*s, U=Y*q², W=4*X*q*s*w
    imply 4*(X*Y²)*w=U*W.
```

The assembled result has exactly the source type's existential R/W/main,
`R≥3`, same-main x/y coordinates, k decomposition and carrier balance.
`calibrationCut` has no explicit additional cut because it imports the
separate reverse-root proposal; that entire root/model proof is still an
unelaborated dependency. This source does not discharge the independent
84-side `DivCut`, the positive-84 parent bridge, graph/provider/axiom
validation, or a physical PDF/ZFC binding. The symbolic and source-flow
checks do not validate the Lean tactics or model theorems.

Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-positive83-gamma-calibration-flow-independent/check.py
```
