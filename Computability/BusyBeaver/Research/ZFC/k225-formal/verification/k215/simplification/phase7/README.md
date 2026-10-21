# Seventh K215 proof-simplification checkpoint

The dominated-implication proof now uses two applications of a pointwise lifting lemma instead of an auxiliary proof relation and deduction theorem. The exact 215-state machine, numerical calculus and ZFC consistency endpoints are unchanged.

| Maintained source | Before | After |
|---|---:|---:|
| `DomRho8.lean` | 517 lines / 30,114 bytes | 454 lines / 26,770 bytes |
| Its source producer | 33,767 bytes | 31,667 bytes |

If `T` proves `a → b`, the existing guarded schemas derive `(x → a) → (x → b)` for any natural code `x`. Applying this lifting rule twice to the existing composition instance yields the unrestricted rho8 row. The argument keeps exactly the original truth, modus-ponens and dominated-row hypotheses, over arbitrary natural codes.

The change removes the private proof relation, its soundness and discharge lemmas, two unused basis aliases, and the obsolete distribution derivation. The removed public helper `distribution` has no maintained caller; its seven supporting schemas are private. Seven retained public statements are exact, and `lift_right` is the only new public theorem. The original theorem and derivation remain available in phase six and Git history. The source and producer credit the pointwise proposal from `b07002a86b` / upstream `dc411f558f` and retain the inherited ProveIt, Source 149 and CD230 attribution.

## Verification

The complete 187-module primary closure passes: two modules freshly compiled and 185 reused after exact source, dependency, object and log checks. `KCodeDom` was rebuilt against the new proof and produced the same object bytes as before, so downstream modules retain valid bindings. Both unchanged typed endpoint clients pass; their ten reports use only `propext`, `Classical.choice` and `Quot.sound`. There are zero audit warnings and 22 inherited project linter warnings. Separate post-audit reviews rehash every current and predecessor provider, the toolchain and both audit objects.

The 15 legacy modules also retain their direct-dependency hashes. A fresh five-client audit passes against all 202 current providers, with five named standard-axiom reports and zero warnings. Its complete 45-module dependency set includes the changed proof, so the historical audit was rerun. The [legacy evidence](legacy/README.md) records the current providers and fresh audit separately from the reused module proofs.

The isolated candidate check also passes with zero warnings and five reports using only `propext` and `Quot.sound`. Three source-generation routes reproduce the exact source; four malformed-input controls are rejected. The producer accepts the two exact reviewed LF/CRLF template byte strings without changing them. Its generic direct and explicit-plan routes remain byte-identical.

The [primary evidence](lean/README.md) references the exact [phase-six packet](../phase6/README.md) rather than duplicating its ancestry. Sources, raw compiler output, failed attempts where present, producer controls, independent reviews and all provider bindings are retained; compiled objects are excluded. This is an incremental check, not a fresh compilation of all project modules. The maintained [fresh build driver](../../lean/README.md) remains the full-rebuild route.

This checkpoint adopts the independently reviewed pointwise component. It does not complete the separate mathematical reconciliation of all batch-209/210 reports. Decoder framing and primitive/return integration remain future proof-shortening work. No new Rocq compilation, smaller machine, minimum-state bound or internal-PA endpoint is claimed.
