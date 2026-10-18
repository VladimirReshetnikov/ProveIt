# Simultaneous internal substitution

`ValidatorEnvironmentSubstitution254` proves an exact encoding identity for simultaneous substitution in arbitrary models of IΣ₁. Formula codes, term vectors, dimensions and indices range over the internal model. The `Matches` premise says that each replacement term has the label assigned to its source slot; vector typing is a separate premise. The theorem permits repeated labels and needs no freshness, injectivity or equality of environment lengths.

The two-slot clients instantiate arbitrary typed terms, bound variables in either order, repeated bound variables, and free variables including the fallback label. This resolves the ordered-slot syntax needed by the native GIC matrix. It does not yet prove native GIC introduction into `CProv`, alpha conversion, the other native axiom branches, or the PA consistency endpoint.

Root's first actual source/audit check passed nine axiom probes and eleven typed callers with zero warnings. Source compilation took 17.842 seconds and the audit 2.257 seconds, under a shared 120-second budget, one thread, 4096 MiB and default proof limits. All nine reports use only `propext`, `Quot.sound` and `Classical.choice`. The guard checked 61 inputs, 15 project providers, four external source/object pairs and two toolchain objects, and recorded the fresh source object before the audit.

The historical environment-label parent supplies legacy pre-audit hash evidence; it lacks a historical first-provider capture. Its exact Foundation overlay and four external pairs are retained without claiming that the entire dependency namespace or cache was independently attested. No dependency build, download, compiler-version query or proof replay occurred in the publication step. Compiled objects remain prerequisites at their recorded paths and are excluded from the text history.

The source is [ValidatorEnvironmentSubstitution254.lean](../../../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorEnvironmentSubstitution254.lean). The [audit](validator_environment_substitution254_audit.lean), [guard](check_validator_environment_substitution254.py), [raw actual record](results/validator-environment-substitution254-verification.json), [boundary](results/validator-environment-substitution254-boundary.json), [author-disclosed evidence review](results/validator-environment-substitution254-review.json), [exact text history](results/validator-environment-substitution254-history.json) and [publication metadata](results/validator-environment-substitution254-publication.json) preserve this first-attempt PASS. Opening authored the source, audit, guard and packaging; root independently read and executed the proof check. Separately attributed peer receipts remain in the history.

From the repository root, with the recorded prerequisite objects available:

```sh
python Computability/BusyBeaver/Research/ZFC/check_validator_environment_substitution254.py --prepare-only --output /tmp/validator-substitution254-prepared
```

Omit `--prepare-only` and choose a fresh output directory for an actual source/audit check. The [maintained-default preparation](results/validator-environment-substitution254-prepared.json) passed after installation; it checked paths and providers without compiling again.
