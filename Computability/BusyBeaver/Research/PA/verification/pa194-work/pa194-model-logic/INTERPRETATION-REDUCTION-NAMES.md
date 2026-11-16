# Conditional guarded interpretation from naming facts

`PA194GuardedInterpretationReductionNames.lean` combines the four-case Interpretation/refutation reduction with `PA194TermNames.termFacts_of_nameFacts`. Both the Interpretation and refutation transport are conditional on `NameFacts` (the seventeen guarded one-layer naming facts), the four typed fixed axiom suppliers for addition/multiplication congruence and successor, and a translated closed-induction supplier for every internally valid arity-one PAeq property, including nonstandard codes. The naming fields are not discharged here.

From the repository root, using a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-interpretation-reduction-names.sh "$PWD" /dev/shm/pa194-interpretation-reduction-names-repo-NEW-new
```

The checker compiles the module and its two axiom reports, rejecting `sorryAx`. It retains the independently source-replayed four-case wrapper and the repository-replayed `/dev/shm/pa194-term-names-repo`, together with the retained overlays enumerated in the checker; Foundation and package objects are prebuilt. The result is model-uniform for candidate PRA + classical IΣ₁, not an object-theory native iPRA theorem. Physical synchronization remains separate.
