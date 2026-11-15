# Tagged PAeq term-to-formula tree

`termTree` is an exploratory, fixed Σ₁-definable encoding of PAeq term codes into relational-source formula trees. It uses Foundation's parameter-unchanged `Language.TermRec`, and its graph is total in every arithmetic IΣ₁ model. Bound and free source variables use distinct positive/negative dummy relational atoms. Zero maps to truth; successor uses a truth-tagged conjunction and a universal marker; addition and multiplication use different Boolean tags with two nested marker paths. Invalid input codes use Foundation's recursor fallback.

`termTree_bvar`, `termTree_fvar`, `termTree_func`, and `termTreeVec_nth` prove exact constructor and child-vector equations for all appropriate internal codes. `termTree_valid` uses internal Σ₁ structural induction and the PAeq function inventory to show every internally valid PAeq term, including a nonstandard term, maps to a well-formed relational formula tree. No full PA model assumption is used.

The encoding is an intermediate structural device. Its prospective interpreter would use formula-recursion binder parameter changes to select the unary/binary child packets, while treating marker nodes as transparent. This replay does not construct that interpreter, prove dispatch separation or recursive interpretation equations, show ordinal semantics, supply PA axioms, or establish a PA proof compiler. The dummy relational formulas are not asserted to be the interpretation outputs.

The incremental checker rebuilds the tree module and its six-report audit top in a fresh output against a separately source-built PAeq-language baseline (four modules), the independently replayed ordinal parameter/value and generic-template modules, and retained compiler overlays. The PAeq baseline was built from the current repository sources in order `PA194PAeqSyntax`, `PA194PAeqTermBlueprint`, `PA194PAeqTermCode`, `PA194PAeqLanguage`; it and Foundation/other workspace dependencies are retained, not rebuilt by this incremental checker. This is not a clean whole-workspace build. Reproduce from the repo with an unused `NEW_EMPTY_OUTPUT`:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-paeq-term-formula-tree.sh "$PWD" NEW_EMPTY_OUTPUT \
 /dev/shm/pa194-term-formula-paeq-baseline /dev/shm/pa194-paeq-ordinal-params-replay \
 /dev/shm/pa194-paeq-ordinal-values-replay /dev/shm/pa194-source-template-replay \
 /dev/shm/pa194-uniform-fully-closed-replay /dev/shm/pa194-uniform-closure-replay \
 /dev/shm/pa194-fully-closed-replay /dev/shm/pa194-model-separation-full-replay \
 /dev/shm/pa194-model-separation-seeded-replay /dev/shm/pa194-model-closure-definability-replay \
 /dev/shm/pa194-model-closure-replay /dev/shm/pa194-general-separation-replay \
 /dev/shm/pa194-ranked-open-separation-replay-v3 /dev/shm/pa194-closed-sep-theory-replay \
 /dev/shm/pa194-uniform-sep-combined-replay /dev/shm/pa194-standard-no-free-replay \
 /dev/shm/pa194-closed-sep-classifier-replay /dev/shm/pa194-generic-sim-replay \
 /dev/shm/pa194-adjunctive-sim-v2-replay /dev/shm/pa194-shift-interface-replay \
 /dev/shm/pa194-unrestricted-existential-v2-replay /dev/shm/pa194-qf-ranked-existential-audit \
 /dev/shm/pa194-adjunctive-admission-audit /dev/shm/pa194-general-shift-replay \
 /dev/shm/pa194-general-reverse-shift-replay /dev/shm/pa194-unrestricted-all-replay \
 /dev/shm/pa194-general-freshness-audit /dev/shm/pa194-observational-general-audit \
 /dev/shm/pa194-full-one-level-audit
```
