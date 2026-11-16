# Successor preserves existence of a term value, conditional on ordinal successor totality

`PA194SuccValueSchema.succValueImplication` proves, in every Δ₁ source theory, internal provability of `¬succTotalCode ∨ (¬∃v valBody(s)[v] ∨ ∃w valBody(succ s)[w])` for every internally valid arity-zero PAeq term `s`, including nonstandard codes. Here `succTotalCode` is the explicit source sentence that every ordinal-domain representative has a domain successor. It is an explicit hypothesis in the implication, not discharged by this theorem.

The proof factors the arbitrary value formula as `domain ∧ r` using the separately repository-replayed Σ₁ term-induction theorem, then instantiates a fixed valid three-predicate first-order schema. The code identity handles the successor relation at both bound-variable orders and exactly matches `valBody_succ`. It assumes no naming field or source axiom beyond the displayed successor-totality antecedent.

From the repository root with a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-succ-value-implication.sh "$PWD" /dev/shm/pa194-succ-value-implication-repo
```

The checker recompiles all four sources, requires one clean axiom report each, and rejects `sorryAx`. It retains repository-built value-domain and revised name-forms/Schematic objects, together with other prebuilt overlays enumerated in the script, including Foundation. This is a model-uniform IΣ₁ theorem, not yet a full-source totality proof, `NameFacts.eSucc`, or native iPRA equivalence.
