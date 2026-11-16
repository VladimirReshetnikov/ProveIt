`scope_translate` proves output formula scope for the actual recursively defined PAeq-term translator in every arithmetic IΣ₁ model. Given a model-valued valid source term `t`, bound arity `s`, target arity `n`, packet `param`, and hypotheses `IsSemiterm PA194PAeq.language s t`, `ParametersValid s n param`, and `t < len (nth param 1)`, the result `translate param t` is a source semiformula of arity `n`. This includes nonstandard `t`, arities and packet codes. The packet's free-term vector may have arbitrary length independent of `s`; the displayed inequality is a conservative sufficient bound guaranteeing access to every free index in `t`.

The proof establishes that the universal packet property is Π₁-definable, then uses Foundation's `IsUTerm.induction 𝚷` available from IΣ₁. Its recursive cases use the checked constructor equations, strict child-code bounds, and validity and length preservation of shifted packets. The theorem does not establish semantic correctness, arbitrary PAeq formula translation, axiom derivations, or a PA proof compiler, and does not remove the free-vector bound. No PA model assumption is used.

The audit rebuilds this source and a three-report audit top against `/dev/shm/pa194-term-dispatcher-repo`, the parent agent's repository-sourced replay of the dispatcher, then the independently replayed term-tree and retained baseline overlays. Foundation and remaining workspace dependencies are prebuilt; this is not a clean whole-workspace build. From the repository root, using a fresh unused output directory:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-term-scope.sh "$PWD" NEW_EMPTY_OUTPUT \
 /dev/shm/pa194-term-dispatcher-repo /dev/shm/pa194-paeq-term-formula-tree-repo \
 /dev/shm/pa194-term-formula-paeq-baseline \
 /dev/shm/pa194-multiplication-code-repo /dev/shm/pa194-addition-code-repo \
 /dev/shm/pa194-paeq-template-compose-repo \
 /dev/shm/pa194-paeq-ordinal-params-replay \
 /dev/shm/pa194-paeq-ordinal-values-replay \
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
The original output `/dev/shm/pa194-term-scope-replay` passed with three clean axiom reports.
