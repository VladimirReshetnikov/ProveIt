# Sign28 sextic syntax and sign28-to-sign31 bridge draft

This packet is **source only**. No Lean invocation, elaboration, or theorem check has been performed here. Neither zero-set direction is proved, and no sign28 iPRA endpoint or Jones reduction is claimed. The input JSON is the independently audited external 28-witness sextic candidate, not a Lean-verified model binding.

`generate.py` generates `SharingSeed28Sextic.lean` from `../nine-sharing-sign28-sextic-candidate/seed.json`, and `check.py` independently parses the restricted source expressions and compares all 19 residual ASTs with that JSON. The result reports maximum residual syntactic degree three; this is not a Lean degree theorem. No numeric port or external JSON-to-Lean semantics proof is supplied. The `NineFreshJones` import supplies existing expression syntax, not application of its quartic reduction.

`SharingSeed28BridgeDraft.lean` proposes natural-model lift/drop and two **open propositions**, not theorems. The sign28 valuation is `Fin 29` including distinguished coordinate 0, and the sign31 valuation is `Fin 32`. The eliminated original sign31 coordinates are 16, 23 and 30: the lift inserts `(v 9 + 1) * (beta * (v 1 + 1) + 1)`, `(v 18 + (v 11 + 1))^2`, and `(v 27)^2` there, respectively, copying all other coordinates in order. Drop removes those three positions. Both preserve coordinate 0 and use one symbolic port tuple. The explicit port-0 cast equates the integer beta port in the difference ring with the natural-model beta needed for the X-coordinate lift.

`check_bridge.py` checks source-text mappings and independently substitutes the indicated lift AST into each original sign31 residual. All 19 surviving external AST rows match the sign28 candidate exactly, and all three removed defining rows become syntactic zero. This is an external AST check, not a Lean semantic theorem. The three inserted expressions depend only on surviving new coordinates, so no extra ordering assumption is used in this lift.

A formal bridge first needs audited Lean sign28 syntax and generic square-sum decomposition. Forward: verify the three removed residual zeros and all 19 surviving row evaluations under the lift and explicit beta cast, then assemble sign31 residual zeros. Backward: extract the three removed residual zeros from an old sign31 zero, use injectivity of the natural embedding to recover original coordinates 16, 23 and 30, establish `lift beta (drop v) = v`, transfer 19 row zeros and assemble the sign28 square sum. The already checked sign31/sign32 bridge can then be composed, preserving coordinate 0; any later current-source or direct iPRA endpoint still needs its own guarded Lean checks. No results for the separately proposed 27/26 candidates are asserted.

For source-only replay in a temporary copy preserving the relative candidate and draft paths, run from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/nine-sharing-sign28-sextic-lean-draft/generate.py
python3 -I -S -B research/nine-sharing-sign28-sextic-lean-draft/check.py
python3 -I -S -B research/nine-sharing-sign28-sextic-lean-draft/check_bridge.py
```

The generator refuses an existing output: remove only the copied `SharingSeed28Sextic.lean` in the temporary copy before replay. The scripts write outputs; do not overwrite frozen originals.

The [independent source audit](../../reviews/nine-sharing-sign28-sextic-lean-draft-frontier-independent/README.md) passed; no Lean compilation or model bridge is claimed.
