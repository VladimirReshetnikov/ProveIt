# Independent review: 84 main, strong and auxiliary witnesses

The graph's main root has the actual `X*Y*q` term: with `U=Y*q²`, `a=XY+Y`, `H=3+4a` and represented rank R, its proposed positive/negative parts are `P=U*(X+a*c)+H*(U*gamma+X*Y*q+R+1)` and `N=H*k`. The first-carrier gap supplies the natural rank representation before this root is rewritten. The source uses the literal main residual to obtain a signed-pair norm, the pinned positive-parts lemma to orient the same P−N root, and the scaled-norm and Pell-classification interfaces to produce one natural `main` and one m with both `xcoord m a=main` and `ycoord m a=c`. That same main is used in the balance equation.

The literal strong and direct auxiliary fields use the same valuation, c, discriminant and represented rank. The graph's separately proposed large-k source feeds the geometry interface `1<c` and `0<Delta<c³`. The strong norm then supplies the strict inequalities used by the direct-auxiliary adapter; that adapter provides a natural offset u and exactly the absolute-difference equation required by `MainStrongAux`. The composition keeps the same m/main pair from the main proof and the same graph tuple for strong and auxiliary facts. Its direct interfaces require no `q ∣ X` or 84-to-83 transport; this is a bounded source-dependency finding, not an authenticated transitive provider audit.

The final proposed `divCut` composes the separately proposed rank-window and main/strong/aux cuts, so it has no extra explicit graph-cut parameter. This is not a completed Lean proof: source terms, graph-expression rewriting, model order and casts, imported axioms and providers all need checking. It establishes no iPRA or PDF endpoint on its own.

The checker pins the relevant source interfaces, verifies key graph rows and same-witness call sites, and reproduces the author's receipt. From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-positive84-main-strong-aux-same-witness-independent/check.py | cmp - reviews/ordinary13-positive84-main-strong-aux-same-witness-independent/receipt.json
```
