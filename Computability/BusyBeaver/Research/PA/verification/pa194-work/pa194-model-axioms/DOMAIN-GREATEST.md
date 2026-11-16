# Greatest-element existence for a nonzero ordinal

The three modules construct a fixed pure-logic proof of `∀a. domain(a) → (¬zero(a) → greatestExists(a))`, kernel-check its universal closure, quote it into every covered candidate PRA model with IΣ₁ arithmetic reduct, and specialize it at any model-valued index. `greatestExistsTemplate` is the exact source-language existential predicate from the ordinal minimum-bad construction.

`domainGreatestAtProof` consumes a contextual proof of the fixed universal theorem plus contextual proofs of domain(a) and ¬zero(a), and constructs a contextual proof of greatestExists(a). Its fixed parameter-free Σ₁ graph computes exactly the output internal proof code, including for nonstandard indices, contexts and proofs. `domainGreatestAtFromLogic` supplies the fixed theorem model-by-model via Lean choice, leaving the domain and nonzero proofs as hypotheses; no uniform graph is claimed for that selection. The proof of the existential witness branch, full minimum-bad contradiction, ordinal induction sequent and native iPRA equivalence remain open.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-domain-greatest.sh "$PWD" /dev/shm/pa194-domain-greatest-repo
```

The checker rebuilds all three sources in one output against prebuilt dependencies, verifies direct hashes, checks 13 axiom reports and rejects `sorryAx`; the reports list only `propext`, `Classical.choice`, and `Quot.sound`.
