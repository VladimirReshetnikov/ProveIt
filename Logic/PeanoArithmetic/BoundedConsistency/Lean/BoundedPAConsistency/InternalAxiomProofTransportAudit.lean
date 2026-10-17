import BoundedPAConsistency.InternalAxiomProofTransport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.InternalAxiomProofTransport
open scoped LO.FirstOrder.Arithmetic
#print axioms LeanProofs.BoundedPAConsistency.InternalAxiomProofTransport.derivable_of_axioms_provable
#print axioms LeanProofs.BoundedPAConsistency.InternalAxiomProofTransport.provable_of_axioms_provable
#print axioms LeanProofs.BoundedPAConsistency.InternalAxiomProofTransport.provable_iff_of_mutual_axiom_provability
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {T U : Theory L} [T.Δ₁] [U.Δ₁]
example (hAx : ∀ p : V, IsFormula L p → p ∈ T.Δ₁Class → Provable U p)
    {d : V} (hd : Derivation T d) : Derivable U (fstIdx d) :=
  derivable_of_axioms_provable hAx hd
example (hAx : ∀ p : V, IsFormula L p → p ∈ T.Δ₁Class → Provable U p)
    {p : V} (hp : Provable T p) : Provable U p :=
  provable_of_axioms_provable hAx hp
example (hAx : ∀ p : V, IsFormula L p → p ∈ T.Δ₁Class → Provable U p)
    {s : V} (hs : Derivable T s) : Derivable U s := by
  obtain ⟨d, hd⟩ := hs
  rw [← hd.1]
  exact derivable_of_axioms_provable hAx hd.2
example (hAx : ∀ p : V, IsFormula L p → p ∈ T.Δ₁Class → Provable U p)
    (hCon : ¬ Provable U (^⊥ : V)) : ¬ Provable T (^⊥ : V) :=
  fun hp => hCon (provable_of_axioms_provable hAx hp)
example (hTU : ∀ p : V, IsFormula L p → p ∈ T.Δ₁Class → Provable U p)
    (hUT : ∀ p : V, IsFormula L p → p ∈ U.Δ₁Class → Provable T p) (p : V) :
    Provable T p ↔ Provable U p :=
  provable_iff_of_mutual_axiom_provability hTU hUT p
example (hTU : ∀ p : V, IsFormula L p → p ∈ T.Δ₁Class → Provable U p)
    (hUT : ∀ p : V, IsFormula L p → p ∈ U.Δ₁Class → Provable T p) :
    (¬ Provable T (^⊥ : V)) ↔ ¬ Provable U (^⊥ : V) :=
  not_congr (provable_iff_of_mutual_axiom_provability hTU hUT _)

example (hAx : ∀ p : V, p ∈ T.Δ₁Class → Provable U p)
    {p : V} (hp : Provable T p) : Provable U p :=
  provable_of_axioms_provable (fun p _ h => hAx p h) hp
