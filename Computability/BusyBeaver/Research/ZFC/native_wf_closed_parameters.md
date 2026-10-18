# Closed native quotient parameters

[NativeWFClosedParameters](../../../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/NativeWFClosedParameters.lean) proves `InternalInterpretation.Good` for three explicit closed formula codes in every model of IΣ₁. The formulas come from the existing quotient and well-founded-part definitions: the translated well-founded domain, quotient equality, and quotient membership. [RawFormQuotation](raw_form_quotation.md) performs the conversion and explicit closure; the [interpretation core](internal_interpretation_core.md) supplies the parameter interface.

The domain code has arity one; equality and membership have arity two. All three are fixed by internal free-variable shift. The paired parameter selects equality at relation code zero and membership at every other internal relation code, so its `Good` proof covers arbitrary internal relation codes. The three quoted formulas themselves are fixed finite syntax objects.

This unit proves syntactic `Good` only. It does not identify the parameter with the earlier unclosed draft or `NativeInterp.PN`, prove semantic interpretation or domain nonemptiness, transport arbitrary internal native axioms, or close native R3 or the PA machine comparison.

The second actual run passed seven axiom probes and ten typed callers with zero warnings, taking 2.373 seconds for the source and 1.967 seconds for the audit. All seven reports use only `propext`, `Classical.choice`, and `Quot.sound`. The [verification](results/native-wf-closed-parameters-verification.json) records 81 inputs, raw logs, and the source-object and first-provider captures saved before audit. The [independent review](results/native-wf-closed-parameters-review.json) checks those bindings and the preserved failure lineage.

The first run failed in the domain-arity proof because the helper returned arity `↑1` while the statement used model numeral `1`; the audit was not reached and no fresh object was accepted. The successor changes only that proof to simplify `Nat.cast_one` and unfold `domainCode`. Its guard changes only the source hash and default source path. Statements, audit, boundary, and proof limits remain unchanged. Both preparations, both attempts, the exact repair, earlier source/guard reviews, and an unexecuted guard-drafting correction are retained in [history](results/native-wf-closed-parameters-history.json). No failure has been replaced by the successful record.

The [boundary](results/native-wf-closed-parameters-boundary.json) selects 27 project providers from the checked core, quotation, and binary-endpoint records, with three direct external boundaries, five retained external source/object pairs, and Init/Omega. It uses the successful core and quotation source snapshots; the old core's superseded maintained-source input remains historical metadata. It does not revalidate the binary parent's complete 851-project closure. Existing cached objects and the historical Foundation namespace overlay are required, and the whole cache is not independently attested. The quotation parent retains its two style warnings; this unit has none.

[Publication metadata](results/native-wf-closed-parameters-publication.json) records nine mapped artifacts. Root authored the parameter and audit and executed the checks; separate agents authored the guard and reviewed the source, boundary, and actual evidence. The actual-evidence reviewer subsequently prepared this publication writer, so that writer's author check is not an independent packaging review. The writer performs metadata checks and stages files only; it does not compile or install them.

The maintained [guard](check_native_wf_closed_parameters.py) changes only five path defaults; the boundary remains byte-identical. Its parent paths retain the original recorded locations unless the explicit evidence options below are supplied. Neither the artifact package nor the command supplies a clean-checkout dependency build or distributes compiled caches.

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_native_wf_closed_parameters.py \
  --repo "$PWD" \
  --dependency-root /path/to/the/recorded/dependency-root \
  --core-evidence Computability/BusyBeaver/Research/ZFC/results/internal-interpretation-core-verification.json \
  --quotation-evidence Computability/BusyBeaver/Research/ZFC/results/raw-form-quotation-verification.json \
  --binary-evidence Computability/BusyBeaver/Research/ZFC/results/routing245-binary-verification.json \
  --output /tmp/fresh-native-wf-closed-parameters-preparation \
  --prepare-only
```

Preparation invokes no compiler or version query. A fresh normal run checks source then audit with default proof limits, one thread, 4,096 MiB, and a shared 120-second deadline. No dependency rebuild is performed.
