import PA194PAeqND
import Foundation.FirstOrder.Basic.Calculus2
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unnecessarySeqFocus false
namespace PA194PAeq.ND
open LO LO.FirstOrder
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩

noncomputable def singleTheoryProof {T : Theory language} {φ ψ : Sentence language}
    (d : Proof [(φ : Proposition language)] (ψ : Proposition language)) (hφ : φ ∈ T) : T.Proof ψ := by
  let e := Derivation.toDerivation2 T d
  have h : T ⟹₂ insert (ψ : Proposition language) (∼Sequent.embed [φ]).toFinset := by
    refine Derivation2.cast e ?_
    ext p
    simp [Sequent.embed, Semiformula.neg_eq]
  exact Theory.Proof2.toProof (Derivation2.cutManyProof [φ] (by simpa using hφ) h)

#print axioms singleTheoryProof
end PA194PAeq.ND
