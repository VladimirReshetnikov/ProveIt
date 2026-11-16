import PA194PAeqMulRightOneProof
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.ZeroLe
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeq.AddOne
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩

def prop : Semiproposition language 1 := eq zero (.bvar 0) ⋎ less zero (.bvar 0)
def axioms : List Fm := [addZero,reflexivity,inductionFormula prop]
noncomputable def base : ND.Proof axioms (eq zero zero ⋎ less zero zero) :=
  ND.orLeft (MulRightOne.reflAt zero (by simp [axioms]))
noncomputable def stepAt (x : Tm) : ND.Proof ((eq zero x ⋎ less zero x) :: axioms)
    (eq zero (succ x) ⋎ less zero (succ x)) := by
  let Δ := (eq zero x ⋎ less zero x) :: axioms
  have h : ND.Proof Δ (eq (add zero (succ x)) (succ x)) := addZeroAt (succ x) (by simp [Δ,axioms])
  have hl : ND.Proof Δ (less zero (succ x)) := by
    let P : Semiproposition language 1 := eq (add (Rew.bShift zero) (succ (.bvar 0))) (Rew.bShift (succ x))
    change ND.Proof Δ (∃⁰ P)
    apply ND.exsIntro P x
    simpa [P,eq,add,succ,zero,Semiformula.rewAux,Rew.subst,Rew.func,emptyFn,substShift] using h
  exact ND.orRight hl

theorem axioms_shift : ND.shifted axioms = axioms := by
  have h1 : addZero.freeVariables = ∅ := by decide
  have h2 : reflexivity.freeVariables = ∅ := by decide
  have h3 : (inductionFormula prop).freeVariables = ∅ := by decide
  simp [ND.shifted,axioms,shift_id _ h1,shift_id _ h2,shift_id _ h3]
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
def resultSentence : Sentence language := (Semiformula.all prop).univCl
noncomputable def theoryProof : ordinaryPAeq.Proof resultSentence := by
  apply ND.listTheoryProof (A := [addZero.univCl,reflexivity.univCl,(inductionFormula prop).univCl])
  · have h1 : addZero.freeVariables = ∅ := by decide
    have h2 : reflexivity.freeVariables = ∅ := by decide
    have h3 : (inductionFormula prop).freeVariables = ∅ := by decide
    have h4 : (Semiformula.all prop).freeVariables = ∅ := by decide
    simpa [axioms,resultSentence,coe_closed _ h1,coe_closed _ h2,coe_closed _ h3,coe_closed _ h4] using proof
  · intro φ hφ
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hφ
    rcases hφ with rfl | rfl | rfl
    · exact ⟨addZero,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨reflexivity,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨inductionFormula prop,.induction prop,rfl⟩

theorem source_formula : PA194PAeq.formula
    (Rewriting.emb PeanoMinus.Axiom.zeroLe : ArithmeticSemiformula ℕ 0) =
    (Rewriting.emb resultSentence : Semiproposition language 0) := by
  change _ = (resultSentence : Proposition language)
  unfold resultSentence
  rw [coe_closed _ (by decide)]
  rfl
#print axioms theoryProof
#print axioms source_formula
end PA194PAeq.ZeroLe
