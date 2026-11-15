import PA194PAeqAddRightZeroProof
import PA194PAeqAddRightSuccProof
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.AddComm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeq.AddOne PA194PAeq.EqRelExt
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩

def prop : Semiproposition language 1 := .all (eq (add (.bvar 1) (.bvar 0)) (add (.bvar 0) (.bvar 1)))
def axioms : List Fm := AddRightZero.axioms ++ AddRightSucc.axioms ++ [inductionFormula prop]

noncomputable def rightZeroAt (y : Tm) : ND.Proof axioms (eq (add y zero) y) := by
  have h : ND.Proof axioms (.all AddRightZero.prop) :=
    ND.weaken AddRightZero.addRightZeroProof (by intro p hp; simp [axioms,hp])
  have e := ND.allElim _ y h
  simpa [AddRightZero.prop,eq,add,zero,Semiformula.rewAux,Rew.subst,Rew.func,emptyFn] using e

noncomputable def rightSuccAt (y x : Tm) : ND.Proof axioms (eq (add y (succ x)) (succ (add y x))) := by
  have h : ND.Proof axioms (.all AddRightSucc.prop) :=
    ND.weaken AddRightSucc.proof (by intro p hp; simp [axioms,hp])
  have h1 := ND.allElim _ y h
  have h2 := ND.allElim _ x h1
  simpa [AddRightSucc.prop,eq,add,succ,Semiformula.rewAux,Rew.subst,Rew.func,Rew.q,emptyFn,substShift] using h2

noncomputable def ihAt (x y : Tm) {Γ : List Fm} (h : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![x]) prop)) :
    ND.Proof Γ (eq (add x y) (add y x)) := by
  have e := ND.allElim _ y h
  simpa [prop,eq,add,Semiformula.rewAux,Rew.subst,Rew.func,Rew.q,emptyFn,substShift] using e

noncomputable def baseAt (y : Tm) : ND.Proof axioms (eq (add zero y) (add y zero)) := by
  have h1 := addZeroAt y (Γ := axioms) (by simp [axioms,AddRightZero.axioms])
  have h2 := symmAt _ _ (Γ := axioms) (by simp [axioms,AddRightSucc.axioms]) (rightZeroAt y)
  exact transAt _ _ _ (by simp [axioms,AddRightZero.axioms]) h1 h2

noncomputable def stepAt (x y : Tm) : ND.Proof ((Semiformula.rewAux (Rew.subst ![x]) prop)::axioms)
    (eq (add (succ x) y) (add y (succ x))) := by
  let Δ := (Semiformula.rewAux (Rew.subst ![x]) prop)::axioms
  have ih : ND.Proof Δ (eq (add x y) (add y x)) := ihAt x y (ND.assumption (by simp [Δ]))
  have h1 := addSuccAt x y (Γ := Δ) (by simp [Δ,axioms,AddRightZero.axioms])
  have h2 := succCongrAt _ _ (Γ := Δ) (by simp [Δ,axioms,AddRightZero.axioms]) ih
  have hr : ND.Proof Δ (eq (add y (succ x)) (succ (add y x))) :=
    ND.weaken (rightSuccAt y x) (by intro p hp; simp [Δ,hp])
  have h3 := symmAt _ _ (Γ := Δ) (by simp [Δ,axioms,AddRightSucc.axioms]) hr
  exact transAt _ _ _ (by simp [Δ,axioms,AddRightZero.axioms]) h1
    (transAt _ _ _ (by simp [Δ,axioms,AddRightZero.axioms]) h2 h3)
theorem axioms_shift : ND.shifted axioms = axioms := by
  have h : (inductionFormula prop).freeVariables = ∅ := by decide
  change ND.shifted (AddRightZero.axioms ++ AddRightSucc.axioms ++ [inductionFormula prop]) = _
  simp only [ND.shifted,List.map_append,List.map_cons,List.map_nil]
  change ND.shifted AddRightZero.axioms ++ ND.shifted AddRightSucc.axioms ++ [(inductionFormula prop).shift] = _
  rw [AddRightZero.axioms_shift,AddRightSucc.axioms_shift,shift_id _ h]
  rfl

noncomputable def base : ND.Proof axioms (Semiformula.rewAux (Rew.subst ![zero]) prop) := by
  change ND.Proof axioms (.all _)
  apply ND.allIntro
  have h := baseAt (.fvar 0)
  rw [axioms_shift]
  convert h using 1
  simp [prop,eq,add,succ,zero,Semiformula.free,Rewriting.free,Semiformula.rewAux,
    Rew.free,Rew.subst,Rew.func,Rew.q,emptyFn]
  all_goals rfl

noncomputable def inductionStep : ND.Proof axioms
    (.all (implies prop (Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop))) := by
  apply ND.allIntro
  rw [axioms_shift]
  change ND.Proof axioms ((prop 🡒 Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop).free)
  change ND.Proof axioms (prop.free 🡒 (Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop).free)
  apply ND.impIntro
  change ND.Proof _ (.all _)
  apply ND.allIntro
  have h := stepAt (.fvar 1) (.fvar 0)
  convert h using 1
  simp [ND.shifted,axioms_shift,prop,eq,add,succ,zero,Semiformula.free,Rewriting.free,
    Semiformula.shift,Rewriting.shift,Semiformula.rewAux,Rew.free,Rew.shift,Rew.map,Rew.subst,Rew.func,Rew.q,emptyFn]
  constructor
  · change Semiformula.rewAux _ (Semiformula.rewAux _ _) = _
    simp [Semiformula.rewAux,Rew.q,Rew.func,Rew.free,Rew.shift,Rew.map,emptyFn]
    all_goals rfl
  · exact axioms_shift
  case e'_2 =>
    change Semiformula.rewAux _ (Semiformula.rewAux _ _) = _
    simp [eq,add,succ,Semiformula.rewAux,Rew.q,Rew.func,Rew.free,Rew.subst,emptyFn]
    all_goals rfl

noncomputable def proof : ND.Proof axioms (.all prop) := by
  have ind : ND.Proof axioms (inductionFormula prop) := ND.assumption (by simp [axioms])
  change ND.Proof axioms
    ((Semiformula.rewAux (Rew.subst ![zero]) prop) 🡒
      ((.all (prop 🡒 Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop)) 🡒 .all prop)) at ind
  have st : ND.Proof axioms (.all (prop 🡒 Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop)) := inductionStep
  exact ND.mp st (ND.mp base ind)
def resultSentence : Sentence language := (Semiformula.all prop).univCl

def assumptions : List (Sentence language) :=
  [addZero.univCl,addSucc.univCl,transitivity.univCl,succCongruence.univCl,
   (inductionFormula AddRightZero.prop).univCl,
   addZero.univCl,addSucc.univCl,symmetry.univCl,transitivity.univCl,succCongruence.univCl,
   (inductionFormula AddRightSucc.prop).univCl,(inductionFormula prop).univCl]

noncomputable def theoryProof : ordinaryPAeq.Proof resultSentence := by
  apply ND.listTheoryProof (A := assumptions)
  · have h1 : addZero.freeVariables = ∅ := by decide
    have h2 : addSucc.freeVariables = ∅ := by decide
    have h3 : transitivity.freeVariables = ∅ := by decide
    have h4 : succCongruence.freeVariables = ∅ := by decide
    have h5 : (inductionFormula AddRightZero.prop).freeVariables = ∅ := by decide
    have h6 : symmetry.freeVariables = ∅ := by decide
    have h7 : (inductionFormula AddRightSucc.prop).freeVariables = ∅ := by decide
    have h8 : (inductionFormula prop).freeVariables = ∅ := by decide
    have h9 : (Semiformula.all prop).freeVariables = ∅ := by decide
    simpa [assumptions,axioms,AddRightZero.axioms,AddRightSucc.axioms,resultSentence,
      coe_closed _ h1,coe_closed _ h2,coe_closed _ h3,coe_closed _ h4,coe_closed _ h5,
      coe_closed _ h6,coe_closed _ h7,coe_closed _ h8,coe_closed _ h9] using proof
  · intro φ hφ
    simp only [assumptions,List.mem_cons,List.not_mem_nil,or_false] at hφ
    rcases hφ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨addZero,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨addSucc,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨transitivity,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨succCongruence,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨inductionFormula AddRightZero.prop,.induction AddRightZero.prop,rfl⟩
    · exact ⟨addZero,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨addSucc,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨symmetry,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨transitivity,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨succCongruence,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨inductionFormula AddRightSucc.prop,.induction AddRightSucc.prop,rfl⟩
    · exact ⟨inductionFormula prop,.induction prop,rfl⟩

theorem source_formula : PA194PAeq.formula
    (Rewriting.emb PeanoMinus.Axiom.addComm : ArithmeticSemiformula ℕ 0) =
    (Rewriting.emb resultSentence : Semiproposition language 0) := by
  change _ = (resultSentence : Proposition language)
  unfold resultSentence
  rw [coe_closed _ (by decide)]
  rfl
#print axioms source_formula
#print axioms theoryProof
#print axioms proof
#print axioms inductionStep
#print axioms baseAt
#print axioms stepAt
end PA194PAeq.AddComm
