# Ternary source templates and child-packet composition

`PA194SourceTernaryTemplate` constructs, for each fixed typed source semiproposition with three bound slots, one fixed parameter-free Σ₁ graph for capture-avoiding simultaneous substitution of three model-valued term codes. It proves graph correctness, total unique definability, output arity preservation for valid inputs, and exact quotation agreement for standard typed terms. All statements hold in every arithmetic IΣ₁ model and allow nonstandard term codes; the template itself is fixed typed syntax. The theorem is generic and does not by itself identify the fixed addition or multiplication formulas.

`PA194PAeqParameterCompose` defines a Σ₁-definable binder update selecting an arbitrary result index and proves scope preservation under the explicit hypothesis `i < n+1`. Updating the unary-child packet once more yields exactly `binaryParameters param i`; choosing `i = 0` yields `childParameters`. This is an environment-composition prerequisite for a two-binder arithmetic-term translation, not a recursive translator or a proof compiler. No PA model assumption is used. The tree encoding, actual dispatcher, semantic interpretation, arithmetic axioms, and internal proof compilation remain separate work.

The single-output audit rebuilds these two source modules and a nine-report audit top against the separately source-replayed parameter, ordinal, and template baselines, plus retained source overlays and prebuilt Foundation/workspace dependencies. It is not a clean workspace build. From the repository root, using a fresh unused output directory:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-template-compose.sh "$PWD" NEW_EMPTY_OUTPUT \
 /dev/shm/pa194-paeq-ordinal-params-replay /dev/shm/pa194-paeq-ordinal-values-replay \
 /dev/shm/pa194-source-template-replay /dev/shm/pa194-uniform-fully-closed-replay \
 /dev/shm/pa194-uniform-closure-replay /dev/shm/pa194-fully-closed-replay \
 /dev/shm/pa194-model-separation-full-replay /dev/shm/pa194-model-separation-seeded-replay \
 /dev/shm/pa194-model-closure-definability-replay /dev/shm/pa194-model-closure-replay \
 /dev/shm/pa194-general-separation-replay /dev/shm/pa194-ranked-open-separation-replay-v3 \
 /dev/shm/pa194-closed-sep-theory-replay /dev/shm/pa194-uniform-sep-combined-replay \
 /dev/shm/pa194-standard-no-free-replay /dev/shm/pa194-closed-sep-classifier-replay \
 /dev/shm/pa194-generic-sim-replay /dev/shm/pa194-adjunctive-sim-v2-replay \
 /dev/shm/pa194-shift-interface-replay /dev/shm/pa194-unrestricted-existential-v2-replay \
 /dev/shm/pa194-qf-ranked-existential-audit /dev/shm/pa194-adjunctive-admission-audit \
 /dev/shm/pa194-general-shift-replay /dev/shm/pa194-general-reverse-shift-replay \
 /dev/shm/pa194-unrestricted-all-replay /dev/shm/pa194-general-freshness-audit \
 /dev/shm/pa194-observational-general-audit /dev/shm/pa194-full-one-level-audit
```
The original audit output is `/dev/shm/pa194-paeq-template-compose-replay`; the command exited zero and its top audit reports nine declarations, all without `sorryAx`.
