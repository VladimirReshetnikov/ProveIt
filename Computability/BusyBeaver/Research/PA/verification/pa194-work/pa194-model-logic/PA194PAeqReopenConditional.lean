import PA194PAeqInductionAddOne
import PA194PAeqInductionAxiomProof
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.InductionReopen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqBind
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta

/-- The exact remaining numeric compatibility between PAeq binding and Foundation opening. -/
def OpeningInverse : Prop := ∀ p : V, IsSemiformula language 0 p →
  LO.FirstOrder.Arithmetic.Bootstrapping.free language (bindFormula 0 p) = p

theorem reopen (hopen : OpeningInverse (V := V)) (p : V)
    (hp : IsSemiformula language 0 p) (h : Provable ordinaryPAeq (closeOne p)) :
    Provable ordinaryPAeq p := by
  let T := ordinaryPAeq.internalize V
  let a : Formula V language := ⟨p, hp⟩
  let b : Formula V language := ⟨closeOne p, closeOne_scope hp⟩
  have h' : T ⊢ b := (TProvable.iff_provable).2 h
  have hb : IsSemiformula language 1 (bindFormula 0 p) := by
    simpa using bindFormula_scope hp.isUFormula 0 0 (le_refl _) hp
  let body : Semiformula V language 1 := ⟨bindFormula 0 p, by simpa using hb⟩
  have hall : T ⊢! ∀⁰ body := by
    convert h'.get using 1
    ext
    rfl
  have hshift : T ⊢! ∀⁰ body.shift := by simpa using TProof.shift hall
  have hfree : T ⊢! body.free := TProof.specialize hshift (Semiterm.fvar 0)
  have heq : body.free = a := by
    apply Semiformula.ext
    simpa [body,a] using hopen p hp
  have hres : T ⊢ a := ⟨heq ▸ hfree⟩
  exact (TProvable.iff_provable).1 hres

theorem reopen_iterated (hopen : OpeningInverse (V := V)) (n p : V)
    (hp : IsSemiformula language 0 p) (h : Provable ordinaryPAeq (close n p)) :
    Provable ordinaryPAeq p := by
  haveI : 𝚺₁-Function₂ (close : V → V → V) := close_defined.to_definable
  have hdef : 𝚺₁-Predicate (fun i : V => i ≤ n → Provable ordinaryPAeq (close (n-i) p)) := by
    definability
  have hi : ∀ i : V, i ≤ n → Provable ordinaryPAeq (close (n-i) p) := by
    intro i
    induction i using ISigma1.sigma1_succ_induction with
    | hP => exact hdef
    | zero => simpa [close_zero] using h
    | succ i ih =>
      intro hle
      have hil : i ≤ n := le_trans (by simp) hle
      have hlt : i < n := lt_of_lt_of_le (lt_add_one i) hle
      have old := ih hil
      have heq : n-(i+1)+1 = n-i := by simpa using sub_succ_add_succ hlt (0 : V)
      rw [← heq, close_succ] at old
      exact reopen hopen _ (close_scope (n-(i+1)) hp) old
  simpa [close_zero] using hi n (le_refl n)

theorem primitiveBody (hopen : OpeningInverse (V := V)) {p : V}
    (hp : IsSemiformula language 1 p) : Provable ordinaryPAeq (inductionBody p) := by
  have h : Provable ordinaryPAeq (closedInduction p) := ⟨closedInductionProof p, closedInductionProof_valid hp⟩
  exact reopen_iterated hopen (formulaFreeBound (inductionBody p)) (inductionBody p)
    (inductionBody_scope hp) (by simpa [closedInduction,fullyClose] using h)

theorem addOneBody (hopen : OpeningInverse (V := V)) {p : V}
    (hp : IsSemiformula language 1 p) : Provable ordinaryPAeq (inductionBodyAddOne p) :=
  InductionAddOne.addOneBody_provable hp (primitiveBody hopen hp)
theorem arithmeticInductionBody (hopen : OpeningInverse (V := V)) (param : V)
    {p : V} (hp : IsSemiformula ℒₒᵣ 1 p) :
    Provable ordinaryPAeq (PA194PAeqTermBlueprint.formulaCode param (indBodyVal p)) := by
  rw [formulaCode_indBodyVal param hp]
  exact addOneBody hopen (PA194PAeqTermBlueprint.formulaCode_valid param hp)
#print axioms arithmeticInductionBody
#print axioms reopen
#print axioms reopen_iterated
#print axioms primitiveBody
#print axioms addOneBody
end PA194PAeq.InductionReopen
