# Fixed-label native GIC matrix congruence

The [checked source](Lean/ZFCinPA/ValidatorNativeGicCongruence254.lean) proves matrix congruence for the literal validator GIC circuit in every internal model of IΣ₁. If `CProv` proves both implications between arbitrary matrix values `p` and `q`, it proves both implications between `internalGic a b c p` and `internalGic a b c q`. The three labels stay fixed; this finite congruence theorem needs no freshness premise.

Applying the result to double-negation padding removes padding from the matrix while keeping the existential witness label `pad p`. The [literal introduction theorem](validator_native_gic254.md) then gives

```text
CProv (wal 3 (internalGic 1 3 (pad p) p))
```

for every internal `p`, including zero. The audit also checks coincident-label congruence. The witness label is not changed to `p`. Identifying the configurable Foundation body with this literal circuit, alpha transport, arbitrary universal closure and internal derivation translation remain separate R2 obligations. This unit supplies no full native-theory translation or PA consistency endpoint.

The [actual record](results/validator-native-gic-congruence254-verification.json) passed eight probes and eleven typed callers with zero warnings. Source elaboration took 2.51841 seconds and the audit 2.13346 seconds under one shared 120-second budget, `-j1 -M4096` and default proof limits. All eight reports use only `propext`, `Classical.choice` and `Quot.sound`. The guard recorded the fresh source object and its first-provider identity before the audit, then rechecked every selected input and fresh object. No compiler-version query, download or dependency build was performed.

This is the unit's first recorded actual attempt. Its source, audit and executed guard are unchanged. The [history](results/validator-native-gic-congruence254-history.json) preserves the source-only readiness statement, preparation, actual logs, source snapshots and reviews. Earlier failure and repair evidence belongs to the already published [parent introduction history](results/validator-native-gic254-history.json), not to an invented failed congruence run.

The exact boundary has 22 project source/object pairs, three direct external pairs plus the inherited `Foundation.FirstOrder.Arithmetic.HFS.Seq` pair, and Init/Omega. The run records 84 inputs and 28 first providers. The immediate NativeGic parent has a modern shared budget and pre-audit capture. The older [QuantifierCore evidence](validator_quantifier_core254.md) retains its per-command 120-second limits, recorded compiler-version query and absence of the modern first-provider capture. Supplied dependency objects are selected and hashed; the whole cache is not independently attested or rebuilt.

Drop authored the source, audit and original guard. Reflection supplied the [source/guard peer review](results/validator-native-gic-congruence254-history.json). Opening reviewed the existing actual evidence independently of this unit's authorship and prepared its publication proposal; Opening authored related earlier NativeGic/Slots units. Root read and executed the successful check. The [actual review](results/validator-native-gic-congruence254-review.json) records these roles.

The maintained guard changes four path defaults only. Root validated its installed defaults from this directory using the exact historical cached dependencies, without compiling:

```sh
python3 -B check_validator_native_gic_congruence254.py --prepare-only --output /tmp/validator-native-gic-congruence254-maintained-prepared
```

The [separate preparation](results/validator-native-gic-congruence254-maintained-preparation.json) reached `PREPARED_NOT_BUILT` with empty command and fresh-module lists, 84 unchanged inputs, the exact 22/4/2 provider boundary and unchanged source/audit/boundary hashes. The [installation review](results/validator-native-gic-congruence254-installation.json) connects that result to the [publication packet](results/validator-native-gic-congruence254-publication.json), whose historical pending status is preserved. The command still requires the recorded historical dependencies; it is not a clean-checkout rebuild procedure.
