import ConciseIPRA.NativeBiInterpretation

/-!
# Sequent-polymorphic contracts for iPRA

Source-oriented candidate against ProveIt commit
`7fa3ba48e8f62e8018ed954faaa48b908217eaf1`.

A `Contract A phi` is a context-polymorphic proof transformer.  The main
result is an exact equivalence with the ordinary sequent `A ⊢[PRAAx] phi`.
No new object rule, axiom, or semantic soundness oracle is introduced.

This file contains no placeholder.  It was not compiled in the artifact
runtime because Lean was unavailable there; kernel-checked status is not
claimed until it builds in the pinned repository.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA.KIFCS

open Syn
open scoped Fm

/-- A proof interface independent of the ambient context that supplies it. -/
def Contract {n : Nat} (A : List (Fm PTm n)) (phi : Fm PTm n) : Prop :=
  ∀ Delta : List (Fm PTm n),
    (∀ psi, psi ∈ A → Delta ⊢[PRAAx] psi) →
    Delta ⊢[PRAAx] phi

namespace Contract

variable {n m : Nat}
variable {A B : List (Fm PTm n)}
variable {phi psi chi : Fm PTm n}

/-- Simultaneous cut turns an ordinary sequent into a contract. -/
theorem ofPrf (h : A ⊢[PRAAx] phi) : Contract A phi :=
  fun _Delta supply => h.trans supply

/-- Instantiate a contract at its own assumption context. -/
theorem toPrf (c : Contract A phi) : A ⊢[PRAAx] phi :=
  c A (fun theta htheta => Prf.hyp htheta)

/-- Contracts are exactly ordinary sequents. -/
theorem iff_prf : Contract A phi ↔ (A ⊢[PRAAx] phi) :=
  ⟨toPrf, ofPrf⟩

/-- Every listed assumption is available as a contract conclusion. -/
theorem hyp (hphi : phi ∈ A) : Contract A phi :=
  fun _Delta supply => supply phi hphi

/-- More available assumptions can only help. -/
theorem weaken (c : Contract A phi) (hAB : A ⊆ B) : Contract B phi :=
  fun Delta supply => c Delta (fun theta htheta => supply theta (hAB htheta))

/-- Simultaneously replace every required input by a contract from `B`. -/
theorem trans (c : Contract A phi)
    (supplyA : ∀ theta, theta ∈ A → Contract B theta) : Contract B phi :=
  fun Delta supplyB =>
    c Delta (fun theta htheta => supplyA theta htheta Delta supplyB)

/-- Apply a simultaneous term substitution to an open contract. -/
theorem subst (c : Contract A phi) (sigma : Fin n → PTm m) :
    Contract (A.map (fun theta => theta.subst sigma)) (phi.subst sigma) :=
  ofPrf ((toPrf c).subst sigma)

/-- A closed ordinary theorem is a contract with no required input. -/
theorem ofNil (h : ([] : List (Fm PTm n)) ⊢[PRAAx] phi) : Contract [] phi :=
  ofPrf h

/-- Pair two conclusions with conjunction introduction. -/
theorem andI (left : Contract A phi) (right : Contract A psi) :
    Contract A (phi ⋏ psi) :=
  fun Delta supply => Prf.andI (left Delta supply) (right Delta supply)

/-- Eliminate the left component of a conjunction contract. -/
theorem andE1 (pair : Contract A (phi ⋏ psi)) : Contract A phi :=
  fun Delta supply => Prf.andE₁ (pair Delta supply)

/-- Eliminate the right component of a conjunction contract. -/
theorem andE2 (pair : Contract A (phi ⋏ psi)) : Contract A psi :=
  fun Delta supply => Prf.andE₂ (pair Delta supply)

/-- Exact transfer to the checked native scalar calculus. -/
theorem iff_native :
    Contract A phi ↔ NPrf (A.map NFm.ofPRA) (NFm.ofPRA phi) :=
  iff_prf.trans pra_iff_native

end Contract

end LeanProofs.ConciseIPRA.KIFCS
