# One explicitly coded parameterized separation leaf

`PA194AtomicParameterSeparation.atomicParameter_opening` proves in every PRA model with an IΣ₁ arithmetic reduct the concrete inverse-opening equality

```text
free SourceL (sepRoot (bvar 0 ∈ bvar 3))
  = sepRoot (bvar 0 ∈ fvar 0).
```

The term notation denotes the exact source relation and variable codes in the Lean source. The source-opening trace crosses separation's three binders, so index 3 is the one additional parameter. The proof uses the model-length qVec trace and includes nonstandard models. `atomicParameter_axiom` combines the equality with `simRuleSeparation_closedOnce_ranked` to derive the numerical target axiom implication for the actual universally closed source formula `∀(sepRoot (bvar 0 ∈ bvar 3))`. Its only premises are source sequent validity, membership of this formula in the sequent, and `SeedAdmission` at that actual axiom node. It does not assume an inverse-opening equation or separate admission at a fictitious open axiom node.

The general helper `simRuleSeparation_closedOnce_ranked` accepts any φ and p but still requires the explicit equation `free SourceL p = sepRoot φ`. Thus the result establishes this single atomic closed separation instance, not a general parameterized separation scheme, PA interpretation, native iPRA result, or consistency equivalence.

The independent replay exited 0 in `/tmp/pa194-atomic-parameter-separation-replay-v2.log`. It rebuilt both sources and an audit top in one fresh output; the audit also imports the earlier conditional one-parameter module to check for duplicate declarations. An initial combined replay failed on duplicate local instance names; the corrected source uses distinct names, and the successful replay is the v2 run. All four axiom reports list `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. Three selected source-built prerequisite objects and source files are hashed before and after; other prerequisite and workspace/foundation objects remain prebuilt and their full transitive source closure is not authenticated. This is not a whole-workspace clean build.

From the repository root, with a fresh output path:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-atomic-parameter-separation.sh "$PWD" /dev/shm/pa194-one-parameter-separation-replay /dev/shm/pa194-ranked-open-separation-replay-v3 /dev/shm/pa194-unrestricted-all-replay /dev/shm/pa194-adjunctive-admission-audit /dev/shm/pa194-full-one-level-audit /dev/shm/pa194-atomic-parameter-separation-replay-v2
```
