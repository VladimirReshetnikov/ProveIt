`PA194TermDispatcher` combines the source-replayed tagged PAeq-term tree with an actual Foundation `UformulaRec1.Construction`. Its fixed parameter-free Σ₁ graph defines `translate param t` in every arithmetic IΣ₁ model, with no full PA assumption. The input packet stores bound- and free-term vectors and a result term. The dispatcher uses the actual variable, zero and successor clauses and the separately audited fixed addition/multiplication trace templates. Its binary clause has two existential value witnesses and receives the two child translations under two binders.

`PA194TermDispatcherEquations` proves exact equations for all six term constructors: bound and free variables and zero unconditionally; successor assuming `IsUTerm` for its child; addition and multiplication assuming `IsUTerm` for both children. These premises cover arbitrary model-valued (including nonstandard) terms. The successor child receives `childParameters`; binary children receive `binaryParameters param 1` and `binaryParameters param 0`. The proof checks that the marker for binary left child differs from the truth tag, so successor dispatch cannot collide. It also proves the quantified-marker equations using the composition of shifted packets. `binaryValue_valid` separately proves output scope under explicit result-term validity and child-formula validity at target arity increased twice. These equations concern the translator's coded syntax; they do not yet prove total scope preservation for arbitrary valid source terms.

The remaining compiler obligations include an internal nonstandard-term scope/correspondence induction that controls shifted environments and free-variable vector bounds; source formulas and arithmetic equality (which the upstream typed interpretation represents by order isomorphism), quantifiers and substitutions; derivations of the arithmetic and induction axioms in the source theory; and compilation of model-valued PA proof codes. The recorded equations do not establish interpretation semantics or any consistency implication. A naive induction with an unbounded universal quantifier over packets is not automatically Σ₁ and cannot be passed to the available IΣ₁ induction theorem.

The audit rebuilds the three listed source modules and a twelve-report top in one output against the independently source-replayed term-tree, PAeq, multiplication, addition, generic-template and parameter baselines and retained overlays. Foundation and remaining workspace dependencies are prebuilt; this is not a clean whole-workspace build. From the repository root, using a fresh unused output directory:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-term-dispatcher.sh "$PWD" NEW_EMPTY_OUTPUT \
 /dev/shm/pa194-paeq-term-formula-tree-repo /dev/shm/pa194-term-formula-paeq-baseline \
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
The original audit output is `/dev/shm/pa194-term-dispatcher-replay`; the top audit reports twelve declarations without `sorryAx`.
