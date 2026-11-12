# AQ17/94 conditional model-transfer draft

This packet transcribes the positive 17-variable, 94-operation, degree-20
graph to an inert Lean literal and eight ordered residuals, and proposes a
model transfer directly to AQ20/104. **No declaration here has been Lean
elaborated.** The graph maps of AQ17, AQ20 and AQ22 are all retained as
explicit premises for the native and standard endpoint drafts. The separate
111-operation natural JSON is not Lean-proved equal to `positiveShift` of the
literal.

Projection removes AQ20 slots 14, 15 and 19. Extension restores the
ell-variable as `(X*Y)*(Y*(eta+zeta))`, the squared-c variable as
`(eta+Y*(eta+zeta))²`, and delta as `3+4*(X*Y+Y)+(X*Y+Y)²`. The proposed
positive-model proof uses only positivity of the retained variables; the local
model maps require no port sign condition. The preceding AQ20 transfer still
requires the exact representation and strict positivity of beta, as described
in its [model draft](../adaptive-aq20-substituted104-model-draft/).

The source's graph obligations remain open: their discharge needs eight
model-ring residual identities, three vanishing binding identities, recovery
of the three parent bindings from a parent zero, and the resulting zero maps.
The external graph checks compare AQ17/94 to AQ17/95 and then AQ17/95 to
AQ20/104 as exact integer-polynomial residual identities; these checks do not
elaborate the directly composed model transfer. AQ22 quotient extraction,
current-port provider ancestry and the historical parent endpoint likewise
remain inherited boundaries. This does not prove an iPRA endpoint or an
untranslated consistency equivalence for the new graph.

From `Computability/DiophantineConsistency`, run:

```
python3 -I -S -B research/adaptive-aq17-factored94-model-draft/check.py | cmp - research/adaptive-aq17-factored94-model-draft/receipt.json
```

This read-only check pins the sources, reconstructs the literal and residual
sum, and reruns both external graph checkers. It does not invoke Lean, stage
artifacts or authenticate compiled providers.
