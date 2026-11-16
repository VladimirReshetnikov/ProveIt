import PA194PAeqInductionBodySupplier
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.InductionReopen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqBind
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta

theorem close_provable {p : V} (hp : IsSemiformula language 0 p)
    (h : Provable ordinaryPAeq p) : Provable ordinaryPAeq (closeOne p) := by
  let T := ordinaryPAeq.internalize V
  let a : Formula V language := ⟨p, hp⟩
  let body : Semiformula V language 1 := ⟨bindFormula 0 p, by
    simpa using bindFormula_scope hp.isUFormula 0 0 (le_refl _) hp⟩
  have h' : T ⊢ a := (TProvable.iff_provable).2 h
  have heq : body.free = a := by
    apply Semiformula.ext
    simpa [body,a] using openingInverse p hp
  have hbody : T ⊢ body.free := by simpa [heq] using h'
  have hall : T ⊢ ∀⁰ body := TProof.all! hbody
  have hc : T ⊢ (⟨closeOne p,closeOne_scope hp⟩ : Formula V language) := by
    convert hall using 1
    ext
    rfl
  exact (TProvable.iff_provable).1 hc

theorem close_iterated_provable (n p : V) (hp : IsSemiformula language 0 p)
    (h : Provable ordinaryPAeq p) : Provable ordinaryPAeq (close n p) := by
  haveI : 𝚺₁-Function₂ (close : V → V → V) := close_defined.to_definable
  have hi : ∀ i : V, Provable ordinaryPAeq (close i p) := by
    intro i
    induction i using ISigma1.sigma1_succ_induction with
    | hP => definability
    | zero => simpa using h
    | succ i ih =>
      rw [close_succ]
      exact close_provable (close_scope i hp) ih
  exact hi n
#print axioms close_provable
#print axioms close_iterated_provable
end PA194PAeq.InductionReopen
