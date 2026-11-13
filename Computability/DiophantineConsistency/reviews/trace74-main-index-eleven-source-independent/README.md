# Independent source review: same-witness main index ≥11

Source-only PASS `f5e80e9ffa257adc0a4ae66f22d29651f568c11c481437d61a77f0554f75312e`; no Lean replay. For same p/v under beta≥15, positive valuation, actual 74 zero, q≥64, supplied first-coordinate n≥7, strict monotonicity identifies the first-index window witness with n. Window n<r<2n gives r≥8; parity excludes 8 and 10, accepted n≥7/r9 graph exclusion removes 9; hence r≥11. The returned r is the same odd window witness with r<2n and c=y_r. No general graph-zero exclusion, guard or iPRA endpoint. Elaboration and provider compatibility remain untested.

Author revised source to `84e18e76d44fe9a5d2d23547c14fd4b155f901e83827809dc8a2755db10d42e7` before launch, retaining `n<r` in the existential conclusion and returning the already synchronized hnr witness. Source-only PASS applies to these latest bytes; all earlier assumptions and scope unchanged.
