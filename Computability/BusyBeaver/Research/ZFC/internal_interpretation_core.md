# Represented interpretation core with defined atoms

[InternalInterpretation](../../../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/InternalInterpretation.lean) checks a generic interpretation of internal set-language syntax in every model of IΣ₁. A parameter `P = ⟪d, ⟪a₌, a∈⟫⟫` supplies a one-variable domain formula and two-variable meanings for equality and membership. `Good P` requires their arities and shift invariance. The represented Σ₁ function `interp P` replaces atoms by substitution into those meanings and guards quantifiers by the domain.

The laws cover arbitrary internal formula codes: typing, negation, shift, substitution and `free`. `derivable_iSet` transports arbitrary internal derivations, retaining finitely many domain side formulas. For shift-fixed theorem codes, `provable_interp` discharges them when the target theory proves domain nonemptiness and the interpreted source axioms. `provable_falsum_of_interp` then transports refutations. The checked set-language adapter supplies the closed-term premise; the domain and axiom hypotheses remain explicit. This core does not construct a native quotient parameter or discharge the native R3 interpretation obligations.

The merged 609-line source imported `LGlueCodes` only to use its relation-arity lemma. The checked 620-line successor imports the existing set-relativization modules and copies that literal arity proof privately. Its seven call sites change names; every public declaration and the other proof bodies are unchanged. The [original source](internal-interpretation-core/original/InternalInterpretation.lean) and [supplied seven-probe audit](internal-interpretation-core/original/InternalInterpretationAudit.lean) are retained exactly.

The [expanded audit](internal_interpretation_core_audit.lean) keeps the seven probes and adds thirteen typed clients, including `Good`, all-internal substitution and derivation transport, and falsum transport with the term premise discharged. The first actual source/audit run passed in 29.064 and 2.399 seconds with zero warnings and only `propext`, `Classical.choice` and `Quot.sound`. [The verification record](results/internal-interpretation-core-verification.json) records all 42 inputs, raw output and the source-object/first-provider captures saved before audit. [The independent review](results/internal-interpretation-core-review.json) is separate from the source/guard author and root execution.

The exact boundary reuses three project providers from the [relativization refresh](internal_relativization_refresh.md), three direct Foundation boundaries, two inherited discovery anchors, and Init/Omega. The historical Foundation namespace overlay and cached libraries remain required; the whole dependency cache is not independently attested. The refresh parent lacks the newer explicit first-provider capture, a limitation retained in the records.

[The history](results/internal-interpretation-core-history.json) preserves the original and reduced sources, supplied and expanded audits, both draft guards, the pre-execution probe-list correction, preparation, actual logs and reviews. The initial guard was corrected during source review and was never invoked. [Publication metadata](results/internal-interpretation-core-publication.json) records the source/guard author's later packaging role and the exact file mapping.

The maintained [guard](check_internal_interpretation_core.py) uses a [portable boundary](results/internal-interpretation-core-boundary.json). Its original-source descriptor points to the retained historical snapshot, so installing the reduced source does not invalidate that check. Only maintained defaults, six repository-relative descriptor fields and the corresponding boundary hash change; selected source/audit bytes, provider pairs and proof execution logic remain the same.

The raw PASS also records the old source at its former maintained path. Publication records that single historical input's exact rebinding to the original snapshot; it does not rewrite the raw record. A downstream provenance check must use that explicit rebinding when validating the historical input after installation. The selected reduced source, its captured object and its snapshots retain their original identities.

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_internal_interpretation_core.py \
  --repo "$PWD" \
  --dependency-root /path/to/the/recorded/dependency-root \
  --output /tmp/fresh-internal-interpretation-preparation \
  --prepare-only
```

Preparation invokes no compiler or version query. Omitting `--prepare-only` in a fresh output directory checks the source and audit sequentially with default proof limits, one thread, 4,096 MiB and a shared 120-second deadline. Replay depends on the recorded cached providers; no dependency rebuild is claimed.
