# Actual ZF schema callbacks for open templates

`OpenSchemaTemplates.lean` supplies actual internal ZF proof carriers for translated Separation and globally total functional Replacement, including finite universal closure of the ordinary source parameters. Internal predicate interpretations may retain arbitrary additional internal free parameters. It also supplies the translated ordinary lifted-ZF-axiom callback from actual `Theory.lMap` membership.

The source skeletons preserve native equality and set membership. Separation uses `z=#0,y=#1,x=#2`. Replacement uses matrix substitutions `[#1,#0]` in its functional premise, `[#2,#0]` in uniqueness, and `[#0,#1]` in the image clause; the bounded image witness has `x in X` at slots 0/3. The endpoint is functional Replacement under a globally totality/uniqueness premise, not arbitrary nonfunctional Collection.

The translation identities use the exact existing substitution laws. Each schema proof invokes the checked internal ZF schema constructor for every finite buffer required by `closeTemplate`. This closes the ordinary source free-variable range without assuming the internal predicate matrices are free-variable-free or shift-fixed. Source syntax, parameter ranges and this proof construction remain externally finite; no arbitrary internal source-proof transport follows from this module alone.

The first complete check is run3: 5 ordered axiom probes, 5 generic callers, standard axioms only, and one retained unused-simp warning in Separation normalization (zero audit warnings). Source compilation took 2.233 s and the audit 1.819 s. The guarded check reused 18 exact project prerequisites and 7 external boundaries, checking 64 inputs and the fresh object before/after. No dependency was rebuilt or downloaded.

The history retains the initial unbuilt preflight and both failed source attempts. Run1 needed explicit negation/bound-variable/vector normalization and had attempted to eliminate an external axiom-membership existential directly into a Type-valued proof. Applying `TProof.byAxm` first leaves a membership proposition where that elimination is valid. Run2's remaining literal relation/vector equalities were closed by the final normalization steps. All hypotheses, binder indices and conclusions remain unchanged. The one final style warning is preserved without a cleanup replay.

The maintained-default preflight is separately recorded as UNBUILT. Its portable checker is byte-identical to the final executed driver and verifies the actual first providers, including Init/Omega, against the pinned existing Foundation/Mathlib build:

```bash
python3 Logic/Interpretability/ZFCinPA/check_open_schema_templates.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/Proofs \
  --output /outside/Proofs/open-schema-check
```

Default prerequisite evidence is read from the maintained Closure and OpenSchemaAxioms result files; explicit evidence/cache overrides are available. Add `--prepare-only` for metadata validation. This callback module adds no numerical proof-search, internal L2, binary-machine or consistency endpoint.
