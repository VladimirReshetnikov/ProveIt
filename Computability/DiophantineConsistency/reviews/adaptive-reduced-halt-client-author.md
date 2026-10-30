# Actual 87-gate zero implies machine halt

`ArithmeticAdaptiveHaltReduced2011.reduced_zero_halts` proves in every model of IΣ₁ that a zero of the maintained 87-gate `naturalExpression87` gives a bound `N` and a represented machine halting time `t < N`. It applies the checked `current_natural_zero_iff` to translate the 87-gate zero to the actual natural-expression zero and then applies `natural_zero_halts`. No window or halt is assumed.

Private author build `/tmp/adaptive-reduced-halt-client-nicj6ts5` **PASS**, Lean exit 0 with empty log; object SHA-256 `07750391500c686578dc47bfff96ae40732d1416ba2ebae96212fdfbba082c3e`. Complete CellWindow/prefix/provider and reduced-provider provenance audits passed before and after compilation. The provider uses the separately replayed compatibility WangTable; the historical original comparison object has no established current-source provenance and no canonical provider was replaced.

The 13-file `adaptive-reduced-halt-client-author-evidence/FILES.json` manifest has SHA-256 `5cbfaebb1a247b49315ff05cc463a74e523725d00631f8f944624a32a3863c19`. Reproduce with `python3 Computability/DiophantineConsistency/research/wang-chunk-full/build_reduced_halt.py` using the recorded private providers; set `HALT_PROVIDER` to an independently replayed natural-halt provider for peer validation. The earlier successful exploratory probe is preserved at `/tmp/adaptive-reduced-halt-probe-qg4ov9mq`.

This is an all-model IΣ₁ soundness direction for the 87-gate expression, not a Lean proof of HA proof existence. The converse obtained so far is conditional on an explicitly enriched Assembly witness; its current-source direct construction is being rebuilt separately.
