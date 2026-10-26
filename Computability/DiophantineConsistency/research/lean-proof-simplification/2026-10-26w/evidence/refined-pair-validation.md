# Validation status: NOT compiler-validated

The new `core_eq` and replacement `value_eq` are proposed Lean source, supported by an ordinary mathematical proof. They were **not reached by the compiler** in this session. Do not treat them as checked Lean results.

The existing Mathlib modules needed for `MvPolynomial.expand` were compiled successfully into a private cache. Replaying the existing `Diophantine.Common.SignInvariantPolynomial` dependency then stalled under shared cgroup memory pressure, with the process spending prolonged periods on page faults. The first attempt used the exact pinned source; the second changed only its umbrella tactic import, retaining all declarations and proof bodies. Both were stopped; no proof error was observed. The modified `RefinedPair` module itself was not compiled.

## Preserved evidence

- `sources/original/` contains exact copies of the three upstream HTP source dependencies. Their Git blob hashes match connector fetches from commit `553a5f7a463cbaab8800ff8148fef0bc5a9e1b22`.
- `sources/validation/` and `sources/import-only-validation.patch` show the sole validation import adjustment. This is not part of the proposed production patch.
- `static_checks.json` confirms that the executable `value` definition and both pre-existing public theorem headers are unchanged, and no `sorry`, `admit`, or `axiom` tokens were inserted. Static checks do not establish elaboration.
- `validation_status.json` distinguishes line counts and evidence levels.

## Measurements

The primary production patch preserves the original `pairSigns` definition and `prod_signs` proof byte-for-byte. The original whole module has83 physical lines; the proposed whole module has86, an increase of3. The old `value_eq` proof body has16 physical lines; its proposed replacement has3. The new `core_eq` proof body has7 physical lines, and its declaration including statement has12. All additional statements, namespace openings, comments and axiom-print commands are charged in the86-line whole-file count. No net source-size reduction is claimed.

The principal benefit is a stronger formal-polynomial theorem and simpler mathematical prerequisites. The direct `Mathlib.Analysis.Complex.Polynomial.Basic` import and both uses of `IsAlgClosed.exists_pow_nat_eq` disappear. This does not claim elimination of all complex-number imports transitively or elimination of `Classical.choice` from the eventual axiom list.

No compilation-time, memory, or kernel-term reduction is claimed. An earlier combined variant included an unrelated finite-equivalence cleanup; that variant is optional and is not the primary proposal.

## Replay in a normal checkout

At the pinned repository commit with its Lean 4.32.0 environment and dependencies installed, inspect and apply `refined-pair-algebraic.patch`, then run:

```bash
lake build DiophantineConsistency.RefinedPair
```

The production patch changes only `Computability/DiophantineConsistency/Lean/DiophantineConsistency/RefinedPair.lean`; the upstream validation import adjustment should not be applied. Resolve any elaboration errors before adopting the patch, and inspect the emitted axiom reports. Rebuild its actual downstream users before merging a source change.
