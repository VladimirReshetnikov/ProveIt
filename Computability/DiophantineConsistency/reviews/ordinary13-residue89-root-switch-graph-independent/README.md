# Independent source review: 89 graph root-switch client

The pinned 89 graph's coordinate 8 occurs only in its first root: `Z=b*(ell+k+r-k*Bt)-Bt`, with `ell=(X*Y*Y)*k`. Its first residual is `Z²-b²*(1+ell*(ell+k))`; independent dependency tracing confirms that `A1`, `Fam`, `g72`, and the parameters b, ell, k and Bt do not depend on r. The source's `putR` changes exactly that coordinate, and its proposed first-update and three unchanged-residual statements reflect this wiring.

The proposed replacement proof retains the original valuation when r>0. At r=0 it applies the separately reviewed signed/natural extraction with b>0 and k>=2, obtains a positive replacement that preserves the first-root square, and rebuilds the zero from all four residuals. This is an existential positive-r replacement; it does not assert original r>0. The source's J=0 branch uses represented natural ports, including nonnegative K0. For its symbolic compact client, J positivity and `CompactFixedBeta.bounds` supply positive b; K is an arbitrary standard natural, and no K upper bound appears in this local root switch.

The final bridge still explicitly assumes `PolynomialBridge` for the positive-shifted 82 parent and inherits the separate 90-to-82 gamma/model chain. Symbolic ports are not yet identified with authenticated fixed kernel bytes or the current PDF, and the source graph identities, sign extraction, tactics, providers and axiom reports remain unelaborated. The author receipt reproduces; no Lean or iPRA endpoint has been established.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-residue89-root-switch-graph-independent/check.py | cmp - reviews/ordinary13-residue89-root-switch-graph-independent/result.json
python3 -I -S -B research/ordinary13-residue89-root-switch-graph-draft/check.py | cmp - research/ordinary13-residue89-root-switch-graph-draft/receipt.json
```
