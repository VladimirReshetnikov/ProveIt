# Retaining early coordinates during positive-witness extensions

The fixed-port auxiliary witness proof needs its signed V expression to survive
all subsequent equation transformations. The three coordinate-preserving
extensions are proved in `Lean/DiophantineConsistency/AdaptivePreserveCoordinates16.lean`.
Each is a strengthened form of an existing positive extension with the same
witness and hypotheses, now recording the parent projection equality.
See the [focused replay](../../reviews/adaptive-preserve-coordinates16-replay/README.md)
for verification scope and the inherited historical ancestry.
