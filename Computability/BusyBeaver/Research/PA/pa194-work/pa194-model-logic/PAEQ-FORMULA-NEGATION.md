`translateFormula_neg` proves that the numeric PAeq-to-source formula translator commutes exactly with coded syntactic negation. For every arithmetic IΣ₁ model, arbitrary internally valid (possibly nonstandard) formula `p`, arities `s,n` and packet `param`, it assumes `IsSemiformula PA194PAeq.language s p`, `ParametersValid s n param`, and both `p < len (nth param 1)` and `neg PA194PAeq.language p < len (nth param 1)`. Under these hypotheses `translateFormula param (neg PA194PAeq.language p) = neg SourceL (translateFormula param p)`.

The proof is Π₁ structural induction over model-valued source formulas, using the source-replayed scope theorem to justify target negation and the source/target quantified guard equations. Both environment-length bounds are material: the code of the negation can be larger than the original code, and this theorem does not derive the second from the first. The result is a syntax identity useful for logical proof rules; it does not itself produce a source-calculus derivation, prove arbitrary translated axioms, or establish proof-code compilation. No full-PA model assumption is used.

The single-output audit rebuilds the module and a two-report top against the parent agent's repository-source-replayed formula dispatcher and retained overlays. Foundation and other workspace dependencies are prebuilt; this is not a clean whole-workspace build. From the repository root, using a fresh unused output directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-formula-negation.sh "$PWD" NEW_EMPTY_OUTPUT \
 /dev/shm/pa194-formula-dispatcher-repo /dev/shm/pa194-term-scope-repo \
 /dev/shm/pa194-term-dispatcher-repo \
 /dev/shm/pa194-paeq-term-formula-tree-repo \
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
The original output `/dev/shm/pa194-formula-negation-replay` passed with two clean axiom reports.
