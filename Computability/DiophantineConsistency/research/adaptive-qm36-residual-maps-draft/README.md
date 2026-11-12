# Proposed QM36 represented-beta graph zero maps

This inert Lean source proposes to discharge the graph obligations in the
[conditional QM36 transfer](../adaptive-qm36-conditional-model-draft/README.md).
Every residual comparison, coordinate proof and `#print axioms` command is
unelaborated; no Lean or staging was performed.

The draft compares 25 unchanged residuals, shows the two old product residuals
at indices 11 and 26 vanish under extension, and proposes the exact identity

```text
parent dDifference = child dDifference + H*combinedEquality,
H = 3 + 4*(productVariable2 + Y).
```

The child's combined residual is index 11. Parent zero projection uses the
parent product-slot recovery lemmas and their explicit hypothesis equating
port zero's difference-ring cast to the image of `beta : V`; it does not
assume strict beta positivity. Given the separate sum-of-squares zero lemmas,
the source assembles all 28 parent or 27 child residual zeros. The older QM37
and QM38 model steps remain inherited dependencies.

The read-only checker verifies the named residual index mapping, the precise
represented-beta interface and the independent external exact-residual
observation. It does not check the Lean proof, resource behavior, providers or
axioms. Reproduce from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/adaptive-qm36-residual-maps-draft/check_source.py | cmp - Computability/DiophantineConsistency/research/adaptive-qm36-residual-maps-draft/source-result.json
```
