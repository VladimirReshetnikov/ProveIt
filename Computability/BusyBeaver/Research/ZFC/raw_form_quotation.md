# Closed raw-form quotation

[RawFormQuotation](../../../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/RawFormQuotation.lean) gives a small syntax conversion and quotation interface. Its local `toVar` and eight-constructor `translate` follow `ZFCinPA.Translation`; its closure and quotation proofs follow the syntax-only part of `ZFCinPA.NativeInterp`. Those attribution sources are preserved in the publication history. The new module imports only `ZFCinPA.Instances` and `FirstOrder.Fol`.

`closed k φ` first translates the raw formula with `k + 1` bound slots, then replaces every free variable by the newest bound variable, `#0`. The result is explicitly a closed semisentence. For every such finite syntax object and every model of IΣ₁, its quotation has the displayed arity and is fixed by internal free-variable shift. `quote_closed` states exactly which embedded closed formula is quoted. These theorems assert no equality with the original unclosed quotation, semantic interpretation, domain nonemptiness, interpreted axiom transport or native R3 consistency result.

The first actual run passed all five axiom probes and eight typed callers in 2.100 seconds for the source and 1.903 seconds for the audit. It retained **two style warnings** (`linter.unnecessarySimpa`), one at source line 63 and one at audit line 42. The checked source and audit were preserved without a cosmetic replay. All five reports use only `propext`, `Classical.choice` and `Quot.sound`. The [raw verification](results/raw-form-quotation-verification.json) binds 32 inputs and includes both logs and the source-object/first-provider captures saved before audit; the [independent review](results/raw-form-quotation-review.json) retains the warning counts and exact scope.

The selected boundary contains two project providers: `Instances` from the relativization refresh and `Fol` from the checked binary endpoint's provider set. Five external source/object pairs and Init/Omega are pinned; two external modules are direct imports. The historical namespace overlay and existing caches remain prerequisites. The older refresh lacks the newer first-provider capture, and the check does not revalidate all 851 project providers of the binary parent. Those limitations remain explicit in the [boundary](results/raw-form-quotation-boundary.json).

[History](results/raw-form-quotation-history.json) preserves source, audit, guard, preparation, actual output, source inventories, original attribution snapshots and reviews without compiled objects. [Publication metadata](results/raw-form-quotation-publication.json) records the nine mapped files and separate source, guard, review, execution and packaging roles. The maintained [guard](check_raw_form_quotation.py) changes only its five path defaults; the boundary, proof inputs and execution logic are unchanged.

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_raw_form_quotation.py \
  --repo "$PWD" \
  --dependency-root /path/to/the/recorded/dependency-root \
  --output /tmp/fresh-raw-form-quotation-preparation \
  --prepare-only
```

Preparation invokes no compiler or version query. A fresh normal run checks source then audit with default proof limits, one thread, 4,096 MiB and a shared 120-second deadline. It requires the recorded cached providers and performs no dependency rebuild.
