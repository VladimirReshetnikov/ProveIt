import PA194PAeqMulRightOneProof
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.OneLeSucc
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeq.AddOne
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩

def prop : Semiproposition language 1 := eq (succ zero) (succ (.bvar 0)) ⋎ less (succ zero) (succ (.bvar 0))
def axioms : List Fm := [addZero,addSucc,reflexivity,transitivity,succCongruence,inductionFormula prop]
noncomputable def base : ND.Proof axioms (eq (succ zero) (succ zero) ⋎ less (succ zero) (succ zero)) :=
  ND.orLeft (MulRightOne.reflAt (succ zero) (by simp [axioms]))
noncomputable def stepAt (x : Tm) : ND.Proof ((eq (succ zero) (succ x) ⋎ less (succ zero) (succ x)) :: axioms)
    (eq (succ zero) (succ (succ x)) ⋎ less (succ zero) (succ (succ x))) := by
  let Δ := (eq (succ zero) (succ x) ⋎ less (succ zero) (succ x)) :: axioms
  have h1 := addSuccAt zero (succ x) (Γ := Δ) (by simp [Δ,axioms])
  have h2 := succCongrAt _ _ (Γ := Δ) (by simp [Δ,axioms]) (addZeroAt (succ x) (by simp [Δ,axioms]))
  have h : ND.Proof Δ (eq (add (succ zero) (succ x)) (succ (succ x))) :=
    transAt _ _ _ (by simp [Δ,axioms]) h1 h2
  have hl : ND.Proof Δ (less (succ zero) (succ (succ x))) := by
    let P : Semiproposition language 1 := eq (add (Rew.bShift (succ zero)) (succ (.bvar 0))) (Rew.bShift (succ (succ x)))
    change ND.Proof Δ (∃⁰ P)
    apply ND.exsIntro P x
    simpa [P,eq,add,succ,zero,Semiformula.rewAux,Rew.subst,Rew.func,emptyFn,substShift] using h
  exact ND.orRight hl

theorem axioms_shift : ND.shifted axioms = axioms := by
  have h1 : addZero.freeVariables = ∅ := by decide
  have h2 : addSucc.freeVariables = ∅ := by decide
  have h3 : reflexivity.freeVariables = ∅ := by decide
  have h4 : transitivity.freeVariables = ∅ := by decide
  have h5 : succCongruence.freeVariables = ∅ := by decide
  have h6 : (inductionFormula prop).freeVariables = ∅ := by decide
  simp [ND.shifted,axioms,shift_id _ h1,shift_id _ h2,shift_id _ h3,shift_id _ h4,shift_id _ h5,shift_id _ h6]
noncomputable def inductionStep : ND.Proof axioms
    (.all (implies prop (Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop))) := by
  apply ND.allIntro
  rw [axioms_shift]
  change ND.Proof axioms ((prop 🡒 Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop).free)
  have d := ND.impIntro (stepAt (.fvar 0))
  convert d using 1
  simp [prop,less,implies,Semiformula.free,Rewriting.free,Semiformula.imp_eq,Semiformula.neg_eq,
    Semiformula.neg,Semiformula.rewAux,Rew.free,Rew.subst,Rew.func,Rew.q,eq,add,succ,zero,emptyFn,substShift,Rewriting.app,Semiformula.rew]
  constructor
  · constructor
    all_goals change Semiformula.rewAux _ _ = _
    all_goals simp [Semiformula.rewAux,Rew.func,Rew.q,emptyFn]
    all_goals rfl
  · constructor
    all_goals change Semiformula.rewAux _ _ = _
    all_goals simp [Semiformula.rewAux,Rew.func,Rew.q,emptyFn]
    all_goals rfl
noncomputable def proof : ND.Proof axioms (.all prop) := by
  have ind : ND.Proof axioms (inductionFormula prop) := ND.assumption (by simp [axioms])
  change ND.Proof axioms
    ((Semiformula.rewAux (Rew.subst ![zero]) prop) 🡒
      ((.all (prop 🡒 Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop)) 🡒 .all prop)) at ind
  have b : ND.Proof axioms (Semiformula.rewAux (Rew.subst ![zero]) prop) := by
    convert base using 1
    simp [prop,less,eq,add,succ,zero,Semiformula.rewAux,Rew.subst,Rew.func,Rew.q,emptyFn,Rewriting.app,Semiformula.rew]
    all_goals repeat' constructor <;> rfl
  have st : ND.Proof axioms (.all (prop 🡒 Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop)) := inductionStep
  exact ND.mp st (ND.mp b ind)
#print axioms proof
#print axioms inductionStep
end PA194PAeq.OneLeSucc
