# Bounded formulas and primitive-recursive witnesses in candidate PRA

This note concerns the first-order **candidate** theory `PRA` defined in this directory. The Σ₀ characteristic compiler and bounded-witness theorem have passed an 82-module source-current author rebuild and two isolated replays with matching sources, objects and complete logs. The independent root replay is `/tmp/pra-bounded-newest-independent-2eqcdk_c`; Foundation and Mathlib remain inherited boundaries. None of the results in this note is an internal HA proof or a PA/HA conservation theorem.

After those builds, an upstream merge changed `PRAExhaustion`, `PRANonzero`,
and `PRAPeanoMinusBasic`. A subsequent 92-module dependency-aware rebuild and
two independent replays passed with matching sources, objects and full logs.
Their parent and Foundation/Mathlib qualifications remain explicit.
A later upstream merge changed `PRAAddOne`, several bounded-search and
order-witness modules, and `PRASubReconstruct`; the recorded 92-module runs
cover the preceding snapshot. A later 108-module dependency-aware refresh
passed two independent replays, matching all source, object and full-log
hashes. A further merge changed bounded-formula and characteristic modules;
their affected 68-module graph has since passed an author rebuild and two
independent replays. Foundation and Mathlib remain inherited boundaries.

A bounded search code already provided its recursion equations and two open-induction invariants. `PRABoundedSearchBound` proves in arbitrary candidate-PRA equality models that its output is below or equal to the input bound. `PRABoundedSearchFreeze` proves, using open induction, that once search finds a counterexample, the output remains fixed at all later inputs. Consequently `PRABoundedSearchUniversal` proves that equality of the search output and its input characterizes the absence of counterexamples below the bound. Composing search with the equality-characteristic code gives a fixed primitive-recursive Boolean code. `PRA_proves_universalBitSentence` and `PRA_proves_universalCorrectSentence` are closed candidate-PRA proofs of its bitness and of its exact bounded-universal meaning.

`PRABoundedCharacteristic` lifts the construction to an arbitrary predicate for which candidate PRA already proves a Boolean characteristic and its correctness. `PRABoundedTermCharacteristic` substitutes an arbitrary Foundation term for the bound and proves that the resulting formula is exactly the ordinary bounded universal `∀x < t, φ`. `PRABoundedExistential` uses Boolean complement and De Morgan duality for `∃x < t, φ`; `PRABoundedBoolean` supplies conjunction and disjunction. The proofs work in arbitrary models of candidate PRA and then use first-order completeness in the classical Lean metatheory to obtain closed candidate-PRA proofs.

`PRABoundedFormula` gives a compositional bounded-formula syntax, proves every Foundation `Hierarchy 𝚺 0` semisentence has a representation in it, and proves `PRA_proves_boundedBooleanCharacteristic`: for such a semisentence there is an arity-matched PR code whose Boolean range and exact formula correctness are both provable in candidate PRA. An explicit bounded-existential check exercises the actual Foundation hierarchy constructor.

`PRABoundedWitness.PRA_boundedWitness` combines that result with the existing Herbrand witness theorem for open matrices. From a candidate-PRA proof of `∀⁰* ∃⁰ φ` with `φ` in Foundation Σ₀, it derives the existence of a fixed PR witness code and a candidate-PRA proof of the actual bounded matrix at that witness. Free inputs remain separate code arguments. This is an existence theorem in Lean, with classical soundness/completeness and choice; it does not claim an effective proof transformer, an identification with a standard PRA presentation, or witnessing for PA or HA proofs. The missing Parsons/Σ₁-rule comparison is separate.

The same characteristic construction also yields `PRABoundedInduction.PRA_proves_boundedInduction`: for any candidate-language Σ₀ formula with one induction variable and arbitrary free parameters, candidate PRA proves the universally closed successor-induction axiom. The proof packs the finitely many parameters, compiles the resulting Σ₀ formula, and applies the candidate's open induction to the resulting characteristic equation. This is bounded induction, not Σ₁ induction; focused independent replays passed against the accepted current provider.

`PRAPrimitiveRecursionInduction.PRA_proves_recursiveSentence` separately proves a closed candidate-PRA sentence expressing primitive-recursive witness iteration from a coded base and successor step, with arbitrary parameters. This is one ingredient toward the induction-counterexample argument; it does not provide the required interactive ∃∀∃ Herbrand extraction. Focused independent replays passed against the accepted current provider.

`PRAInductionCounterexample.PRA_proves_counterexampleSentence` uses that
recursive witness to prove a closed candidate-PRA counterexample-defeat
sentence for the explicitly coded predicate and base, target and update
functions. It is an ingredient, not a conservation theorem; interactive
Herbrand extraction and elimination of the resulting disjunction remain.
