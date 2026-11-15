`PA194PAeqBindTerm` supplies a fixed Σ₁ `Language.TermRec` construction that binds source free variable zero at an arbitrary model-valued depth, lowers every other free index by one, leaves bound variables fixed, and recurses through arbitrary PAeq function applications. Its model-level constructor equations and term-vector entry equation hold for every arithmetic IΣ₁ model, including nonstandard well-formed term codes. The construction does not assume PA.

`bindTerm_scope` is proved by Π₁ structural induction: if the original term is scoped at arity `n` and binding depth `k ≤ n`, the output is scoped at `n+1`. This extends the prior SourceL binder, which only handles variable-only terms, to PAeq terms with nested successor, addition and multiplication. These are prerequisites for a PAeq parameter-closure implementation, not a formula binder, universal-closure classifier, typed-quotation identity or proof of `ordinaryPAeq.Δ₁`.

The single-output audit rebuilds these two source modules and an eight-report top against the separately source-replayed PAeq term-tree and language baselines and retained overlays. Foundation and other workspace dependencies are prebuilt; this is not a clean whole-workspace build. From the repository root, using a fresh unused output directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-bind-term.sh "$PWD" NEW_EMPTY_OUTPUT \
 /dev/shm/pa194-paeq-term-formula-tree-repo /dev/shm/pa194-term-formula-paeq-baseline \
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
The original output `/dev/shm/pa194-paeq-bind-term-replay` passed with eight clean axiom reports.
