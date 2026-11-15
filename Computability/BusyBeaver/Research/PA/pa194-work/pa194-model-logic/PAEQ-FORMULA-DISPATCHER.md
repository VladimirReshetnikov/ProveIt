`PA194AtomicPAeq` ports the upstream ordinal order-isomorphism formula syntax and constructs a fixed parameter-free Σ₁ graph for the positive PAeq equality atom. It combines two actual term translations under two existential binders with the isomorphism formula. Its scope theorem requires a valid packet, internally scoped left and right source terms, and each term code below the free-vector length.

`PA194FormulaDispatcher` supplies an actual fixed Σ₁ `UformulaRec1` construction for PAeq formula codes. Its atom cases call that equality translation and its syntactic negation; Boolean cases preserve the corresponding constructors; quantified cases add the ordinal-domain guard. The child-packet update prepends the newly bound variable and shifts both environments, and is proved to preserve packet validity from source/target arities `s,n` to `s+1,n+1`.

`PA194FormulaDispatcherEquations` proves constructor equations for atoms, truth, falsity, conjunction, disjunction, universal and existential quantification. Atom laws require internally valid relation and argument vector; connective/quantifier laws require internally valid children. `PA194FormulaScope` proves by Π₁ structural induction that for any valid model-valued PAeq formula `p`, a packet valid at source arity `s` and target arity `n`, and `p < len (nth param 1)`, the translated formula is scoped at `n`. This conservative free-vector bound covers every internal term occurrence. The results hold uniformly in arbitrary arithmetic IΣ₁ models, including nonstandard syntax; they do not assume a model of full PA.

These are code construction and scope theorems. The upstream isomorphism syntax was ported but its arithmetic interpretation, exact correspondence to the existing typed translation, axiom derivations, PA proof-code transformation, and the final iPRA consistency implication are not established. The source replay uses the independently replayed term-scope module, the repository-source-replayed term dispatcher, retained source overlays and prebuilt Foundation/workspace dependencies; it is not a clean whole-workspace build. From the repository root, using a fresh unused output directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-formula-dispatcher.sh "$PWD" NEW_EMPTY_OUTPUT \
 /dev/shm/pa194-term-scope-repo /dev/shm/pa194-term-dispatcher-repo \
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
The original output `/dev/shm/pa194-formula-dispatcher-replay` passed with seventeen clean axiom reports.
