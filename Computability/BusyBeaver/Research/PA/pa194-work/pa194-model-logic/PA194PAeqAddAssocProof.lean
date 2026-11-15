import PA194PAeqEqRelExt
import PA194PAeqAddCongrAtTyped
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.AddAssoc
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeq.AddOne PA194PAeq.AddCongrTyped PA194PAeq.EqRelExt
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩
variable {Γ : List Fm}

def prop : Semiproposition language 1 := .all (.all
  (eq (add (add (.bvar 2) (.bvar 1)) (.bvar 0)) (add (.bvar 2) (add (.bvar 1) (.bvar 0)))))
def axioms : List Fm := [addZero,addSucc,addCongruence,reflexivity,symmetry,transitivity,succCongruence,inductionFormula prop]

noncomputable def reflAt (t : Tm) (h : reflexivity ∈ Γ) : ND.Proof Γ (eq t t) := by
  have d : ND.Proof Γ reflexivity := ND.assumption h
  have e := ND.allElim _ t d
  simpa [reflexivity,eq,Semiformula.rewAux,Rew.subst,Rew.func,emptyFn] using e

noncomputable def ihAt (x y z : Tm) (h : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![x]) prop)) :
    ND.Proof Γ (eq (add (add x y) z) (add x (add y z))) := by
  have h1 := ND.allElim _ y h
  have h2 := ND.allElim _ z h1
  simpa [prop,eq,add,Semiformula.rewAux,Rew.subst,Rew.func,Rew.q,emptyFn,substShift,substShiftTwice] using h2

noncomputable def baseAt (y z : Tm) : ND.Proof axioms
    (eq (add (add zero y) z) (add zero (add y z))) := by
  have h1 : ND.Proof axioms (eq (add (add zero y) z) (add y z)) :=
    addCongrAt (add zero y) y z z (by simp [axioms]) (addZeroAt y (by simp [axioms])) (reflAt z (by simp [axioms]))
  have h2 : ND.Proof axioms (eq (add y z) (add zero (add y z))) :=
    symmAt _ _ (by simp [axioms]) (addZeroAt (add y z) (by simp [axioms]))
  exact transAt _ _ _ (by simp [axioms]) h1 h2

noncomputable def stepAt (x y z : Tm) : ND.Proof ((Semiformula.rewAux (Rew.subst ![x]) prop)::axioms)
    (eq (add (add (succ x) y) z) (add (succ x) (add y z))) := by
  let Δ := (Semiformula.rewAux (Rew.subst ![x]) prop)::axioms
  have ih : ND.Proof Δ (eq (add (add x y) z) (add x (add y z))) :=
    ihAt x y z (ND.assumption (by simp [Δ]))
  have h1 : ND.Proof Δ (eq (add (add (succ x) y) z) (add (succ (add x y)) z)) :=
    addCongrAt (add (succ x) y) (succ (add x y)) z z (by simp [Δ,axioms])
      (addSuccAt x y (by simp [Δ,axioms])) (reflAt z (by simp [Δ,axioms]))
  have h2 : ND.Proof Δ (eq (add (succ (add x y)) z) (succ (add (add x y) z))) :=
    addSuccAt (add x y) z (by simp [Δ,axioms])
  have h3 : ND.Proof Δ (eq (succ (add (add x y) z)) (succ (add x (add y z)))) :=
    succCongrAt _ _ (by simp [Δ,axioms]) ih
  have h4 : ND.Proof Δ (eq (succ (add x (add y z))) (add (succ x) (add y z))) :=
    symmAt _ _ (by simp [Δ,axioms]) (addSuccAt x (add y z) (by simp [Δ,axioms]))
  exact transAt _ _ _ (by simp [Δ,axioms]) h1
    (transAt _ _ _ (by simp [Δ,axioms]) h2 (transAt _ _ _ (by simp [Δ,axioms]) h3 h4))
theorem axioms_shift : ND.shifted axioms = axioms := by
  have h1 : addZero.freeVariables = ∅ := by decide
  have h2 : addSucc.freeVariables = ∅ := by decide
  have h3 : addCongruence.freeVariables = ∅ := by decide
  have h4 : reflexivity.freeVariables = ∅ := by decide
  have h5 : symmetry.freeVariables = ∅ := by decide
  have h6 : transitivity.freeVariables = ∅ := by decide
  have h7 : succCongruence.freeVariables = ∅ := by decide
  have h8 : (inductionFormula prop).freeVariables = ∅ := by decide
  simp [ND.shifted,axioms,shift_id _ h1,shift_id _ h2,shift_id _ h3,shift_id _ h4,
    shift_id _ h5,shift_id _ h6,shift_id _ h7,shift_id _ h8]

noncomputable def base : ND.Proof axioms (Semiformula.rewAux (Rew.subst ![zero]) prop) := by
  change ND.Proof axioms (.all _)
  apply ND.allIntro
  change ND.Proof _ (.all _)
  apply ND.allIntro
  have h := baseAt (.fvar 1) (.fvar 0)
  rw [axioms_shift,axioms_shift]
  convert h using 1
  simp [prop,eq,add,zero,Semiformula.free,Rewriting.free,Semiformula.rewAux,
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
  change ND.Proof _ (.all _)
  apply ND.allIntro
  have h := stepAt (.fvar 2) (.fvar 1) (.fvar 0)
  convert h using 1
  simp [ND.shifted,axioms_shift,prop,eq,add,succ,zero,Semiformula.free,Rewriting.free,
    Semiformula.shift,Rewriting.shift,Semiformula.rewAux,Rew.free,Rew.shift,Rew.map,Rew.subst,Rew.func,Rew.q,emptyFn]
  constructor
  · change Semiformula.rewAux _ (Semiformula.rewAux _ (Semiformula.rewAux _ _)) = _
    simp [Semiformula.rewAux,Rew.q,Rew.func,Rew.free,Rew.shift,Rew.map,emptyFn]
    all_goals rfl
  · change ND.shifted (ND.shifted axioms) = axioms
    rw [axioms_shift,axioms_shift]
  case e'_2 =>
    change Semiformula.rewAux _ (Semiformula.rewAux _ (Semiformula.rewAux _ _)) = _
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

def assumptions : List (Sentence language) := [addZero.univCl,addSucc.univCl,addCongruence.univCl,
  reflexivity.univCl,symmetry.univCl,transitivity.univCl,succCongruence.univCl,(inductionFormula prop).univCl]

noncomputable def theoryProof : ordinaryPAeq.Proof resultSentence := by
  apply ND.listTheoryProof (A := assumptions)
  · have h1 : addZero.freeVariables = ∅ := by decide
    have h2 : addSucc.freeVariables = ∅ := by decide
    have h3 : addCongruence.freeVariables = ∅ := by decide
    have h4 : reflexivity.freeVariables = ∅ := by decide
    have h5 : symmetry.freeVariables = ∅ := by decide
    have h6 : transitivity.freeVariables = ∅ := by decide
    have h7 : succCongruence.freeVariables = ∅ := by decide
    have h8 : (inductionFormula prop).freeVariables = ∅ := by decide
    have h9 : (Semiformula.all prop).freeVariables = ∅ := by decide
    simpa [assumptions,axioms,resultSentence,coe_closed _ h1,coe_closed _ h2,coe_closed _ h3,
      coe_closed _ h4,coe_closed _ h5,coe_closed _ h6,coe_closed _ h7,coe_closed _ h8,coe_closed _ h9] using proof
  · intro φ hφ
    simp only [assumptions,List.mem_cons,List.not_mem_nil,or_false] at hφ
    rcases hφ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨addZero,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨addSucc,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨addCongruence,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨reflexivity,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨symmetry,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨transitivity,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨succCongruence,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨inductionFormula prop,.induction prop,rfl⟩

theorem source_formula : PA194PAeq.formula
    (Rewriting.emb PeanoMinus.Axiom.addAssoc : ArithmeticSemiformula ℕ 0) =
    (Rewriting.emb resultSentence : Semiproposition language 0) := by
  change _ = (resultSentence : Proposition language)
  unfold resultSentence
  rw [coe_closed _ (by decide)]
  rfl
#print axioms source_formula
#print axioms theoryProof
#print axioms inductionStep
#print axioms baseAt
#print axioms stepAt
end PA194PAeq.AddAssoc
