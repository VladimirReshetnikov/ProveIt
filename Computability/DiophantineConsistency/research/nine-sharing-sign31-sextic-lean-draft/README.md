# Sign31 sextic syntax and sign31-to-sign32 bridge draft

This packet is **source only**. No Lean invocation, elaboration, or theorem check has been performed here. Neither zero-set direction is proved, and no sign31 iPRA endpoint or Jones reduction is claimed. The input JSON is the independently audited external 31-witness sextic candidate, not a Lean-verified model binding.

`generate.py` generates `SharingSeed31Sextic.lean` from `../nine-sharing-sign31-sextic-candidate/seed.json`, and `check.py` independently parses its restricted source expressions and compares all 22 residual ASTs against that JSON. `result.json` records the source-only check and maximum residual syntactic degree three; this is not a Lean degree theorem. No numeric port or external JSON-to-Lean semantics proof is supplied. The `NineFreshJones` import provides existing expression syntax, not application of its quartic reduction.

`SharingSeed31BridgeDraft.lean` proposes natural-model lift/drop and two **open propositions**, not theorems. The sign31 valuation has `Fin 32` including distinguished coordinate 0; the sign32 valuation has `Fin 33`. The lift copies old coordinates 0–26, inserts `(v 5 + 1)^2` as old coordinate 27, and moves new coordinates 27–31 to old 28–32. Drop removes old coordinate 27. Both retain one symbolic port tuple and the distinguished coordinate. Unlike the earlier q² elimination, this f² insertion depends only on natural coordinates; the draft targets need no beta-port cast. `check_bridge.py` records a source-text check only.

For a formal bridge, first establish sign31 square-sum decomposition using the existing index-polymorphic `SharingSign33Squares.squareSum_zero_iff`. For the forward direction, prove the removed f² residual zero on the lift and connect each of the 22 surviving residual evaluations: 20 are reindexed copies, while `V` and `scaled_Ns` substitute the inserted square. Then assemble the 23 old residuals. For the reverse direction, derive old coordinate 27 equals `(v 5 + 1)^2` from the old f² residual using injectivity of the natural embedding, prove `lift (drop v) = v` under old seed zero, transfer all 22 residual zeros back, and assemble the new square sum. Checked sign32/sign33 equivalence can then be composed while preserving coordinate 0; that later composition retains any beta cast required by the sign32/sign33 theorem. All of these Lean steps, their providers and resource fit remain untested. The separately proposed 28-witness reductions are not included.

For source-only replay in a temporary copy preserving the relative candidate and draft paths, run from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/nine-sharing-sign31-sextic-lean-draft/generate.py
python3 -I -S -B research/nine-sharing-sign31-sextic-lean-draft/check.py
python3 -I -S -B research/nine-sharing-sign31-sextic-lean-draft/check_bridge.py
```

The generator refuses an existing output: remove only the copied `SharingSeed31Sextic.lean` in the temporary copy before replay. The scripts write outputs; do not overwrite the frozen originals.

The [independent source audit](../../reviews/nine-sharing-sign31-sextic-lean-draft-frontier-independent/README.md) passed; no Lean compilation or model bridge is claimed.
