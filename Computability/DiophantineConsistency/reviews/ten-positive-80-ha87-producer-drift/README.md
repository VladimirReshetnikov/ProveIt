# Four HA87 author records and eleven additional dependency drifts

The final selected 80 closure has four objects whose SHA-256 hashes match
successful HA87 full author-state records. `check.py` compares each record's
recorded dependency hashes with the final selected closure. All four records
have discrepancies, eleven in total:

- `ArithmeticNegativeNorms`: `Foundation.FirstOrder.Arithmetic.IOpen.Basic`.
- `ArithmeticCarrierSoundness2011`: `ArithmeticSignedPairs`,
  `ArithmeticPellFirstIndex`, and `CurrentEquationSyntax2011`.
- `ArithmeticCarrierRadix2011`: `ArithmeticPellPowerRecovery` and
  `ArithmeticRadixAlignment`.
- `ArithmeticWindowInterface`: `ArithmeticMaskConstants`,
  `ArithmeticMaskPopulation`, `ArithmeticSaturation`, `ArithmeticWindowBits`,
  and `ArithmeticWindowCarry`.

The exact recorded and final hashes, full final selected paths, source-record
data, author search path and state records are in `observations/attempt01.json`,
SHA-256 `2fea027c10bbc9e29f822c61196fba17f98e8f5d13664eade14ba54f2df79e42`.
The author state records dependency names and hashes, not an exact historical
path for each dependency, so this packet does not invent those paths. The
Foundation difference concerns an outside package object: matching or
rebuilding project objects alone does not authenticate its package-transitive
ancestry.

Byte identity with the author outputs does not prove that those records are
the unique historical producers of the selected files, and the comparison
does not show a theorem is unsound. Adding these four recorded-drift modules
to the earlier seven seeds yields 127 reverse-reachable modules in the
captured selected graph. This is still only a plan: more historical drift can
enlarge it, and no rebuild or external JSON/PDF binding is asserted here.
