import PA194PAeqNDList
import PA194PAeqNDShift
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.AddOne
open LO LO.FirstOrder
open scoped LO.FirstOrder
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩

abbrev Tm := SyntacticSemiterm language 0
abbrev Fm := Proposition language
variable {Γ : List Fm}

theorem emptyFn {A : Type} (f : Fin 0 → A) : f = Fin.elim0 := by
  funext i; exact Fin.elim0 i

theorem substShift (s t : Tm) : (Rew.bind ![s] Semiterm.fvar) (Rew.bShift t) = t := by
  change Rew.subst ![s] (Rew.bShift t) = t
  simp

theorem substShiftTwice (s t u : Tm) :
    (Rew.bind ![u] Semiterm.fvar)
      ((Rew.bind (#0 :> Rew.bShift ∘ (Rew.bind ![t] Semiterm.fvar) ∘ Semiterm.bvar)
        (Rew.bShift ∘ (Rew.bind ![t] Semiterm.fvar) ∘ Semiterm.fvar))
        (Rew.bShift (Rew.bShift s))) = s := by
  change Rew.subst ![u] ((Rew.subst ![t]).q (Rew.bShift (Rew.bShift s))) = s
  simp

noncomputable def addZeroAt (t : Tm) (h : addZero ∈ Γ) : ND.Proof Γ (eq (add zero t) t) := by
  have d : ND.Proof Γ addZero := ND.assumption h
  have e := ND.allElim _ t d
  simpa [addZero,eq,add,zero,Semiformula.rewAux,Rew.subst,Rew.func, emptyFn] using e

noncomputable def addSuccAt (s t : Tm) (h : addSucc ∈ Γ) :
    ND.Proof Γ (eq (add (succ s) t) (succ (add s t))) := by
  have d : ND.Proof Γ addSucc := ND.assumption h
  have d1 := ND.allElim _ t d
  have d2 := ND.allElim _ s d1
  simpa [addSucc,eq,add,succ,Semiformula.rewAux,Rew.subst,Rew.func, Rew.q, emptyFn, substShift] using d2

noncomputable def succCongrAt (s t : Tm) (h : succCongruence ∈ Γ)
    (d : ND.Proof Γ (eq s t)) : ND.Proof Γ (eq (succ s) (succ t)) := by
  have a : ND.Proof Γ succCongruence := ND.assumption h
  have a1 := ND.allElim _ t a
  have a2 := ND.allElim _ s a1
  have h' : ND.Proof Γ (eq s t 🡒 eq (succ s) (succ t)) := by
    simpa [succCongruence,implies,Semiformula.imp_eq,eq,succ,Semiformula.neg_eq,Semiformula.neg,Semiformula.rewAux,Rew.subst,Rew.func,Rew.q,emptyFn,substShift] using a2
  exact ND.mp d h'

noncomputable def transAt (s t u : Tm) (h : transitivity ∈ Γ)
    (d : ND.Proof Γ (eq s t)) (e : ND.Proof Γ (eq t u)) : ND.Proof Γ (eq s u) := by
  have a : ND.Proof Γ transitivity := ND.assumption h
  have a1 := ND.allElim _ s a
  have a2 := ND.allElim _ t a1
  have a3 := ND.allElim _ u a2
  have h' : ND.Proof Γ (eq s t 🡒 (eq t u 🡒 eq s u)) := by
    simpa [transitivity,implies,Semiformula.imp_eq,eq,Semiformula.neg_eq,Semiformula.neg,Semiformula.rewAux,Rew.subst,Rew.func,Rew.q,emptyFn,substShift,substShiftTwice] using a3
  exact ND.mp e (ND.mp d h')

def prop : Semiproposition language 1 := eq (add (.bvar 0) (succ zero)) (succ (.bvar 0))

def axioms : List Fm := [addZero, addSucc, transitivity, succCongruence, inductionFormula prop]

noncomputable def base : ND.Proof axioms (eq (add zero (succ zero)) (succ zero)) :=
  addZeroAt (succ zero) (by simp [axioms])

noncomputable def stepAt (x : Tm) : ND.Proof ((eq (add x (succ zero)) (succ x)) :: axioms)
    (eq (add (succ x) (succ zero)) (succ (succ x))) := by
  let Δ := (eq (add x (succ zero)) (succ x)) :: axioms
  have h1 : ND.Proof Δ (eq (add (succ x) (succ zero)) (succ (add x (succ zero)))) :=
    addSuccAt x (succ zero) (by simp [Δ, axioms])
  have ih : ND.Proof Δ (eq (add x (succ zero)) (succ x)) := ND.assumption (by simp [Δ])
  have h2 : ND.Proof Δ (eq (succ (add x (succ zero))) (succ (succ x))) :=
    succCongrAt _ _ (by simp [Δ, axioms]) ih
  exact transAt _ _ _ (by simp [Δ, axioms]) h1 h2

theorem shift_id (p : Fm) (hp : p.freeVariables = ∅) : p.shift = p := by
  apply Semiformula.rew_eq_self_of
  · intro i; exact Fin.elim0 i
  · intro i hi; exact False.elim (by simpa [Semiformula.FVar?,hp] using hi)

theorem axioms_shift : ND.shifted axioms = axioms := by
  have h1 : addZero.freeVariables = ∅ := by decide
  have h2 : addSucc.freeVariables = ∅ := by decide
  have h3 : transitivity.freeVariables = ∅ := by decide
  have h4 : succCongruence.freeVariables = ∅ := by decide
  have h5 : (inductionFormula prop).freeVariables = ∅ := by decide
  simp [ND.shifted, axioms, shift_id _ h1, shift_id _ h2, shift_id _ h3, shift_id _ h4, shift_id _ h5]

noncomputable def inductionStep : ND.Proof axioms
    (.all (implies prop (Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop))) := by
  apply ND.allIntro
  rw [axioms_shift]
  change ND.Proof axioms ((prop 🡒 Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop).free)
  have d := ND.impIntro (stepAt (.fvar 0))
  simpa [prop, implies, Semiformula.free, Semiformula.imp_eq, eq, add, succ, zero,
    Semiformula.neg_eq, Semiformula.neg, Rewriting.free, Semiformula.rewAux, Rew.free, Rew.subst, Rew.func,
    Rew.q, emptyFn, substShift] using d

noncomputable def addOneProof : ND.Proof axioms (.all prop) := by
  have ind : ND.Proof axioms (inductionFormula prop) := ND.assumption (by simp [axioms])
  change ND.Proof axioms
    ((Semiformula.rewAux (Rew.subst ![zero]) prop) 🡒
      ((.all (prop 🡒 Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop)) 🡒 .all prop)) at ind
  have b : ND.Proof axioms (Semiformula.rewAux (Rew.subst ![zero]) prop) := by
    simpa [prop,eq,add,succ,zero,Semiformula.rewAux,Rew.subst,Rew.func,emptyFn] using base
  have st : ND.Proof axioms (.all (prop 🡒 Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop)) := by
    exact inductionStep
  exact ND.mp st (ND.mp b ind)

def resultSentence : Sentence language := (Semiformula.all prop).univCl

theorem coe_closed (p : Fm) (hp : p.freeVariables = ∅) : (p.univCl : Fm) = p := by
  rw [Semiformula.coe_univCl_eq_univCl']
  exact Semiformula.univCl'_eq_self_of _ hp

def assumptions : List (Sentence language) :=
  [addZero.univCl, addSucc.univCl, transitivity.univCl, succCongruence.univCl,
    (inductionFormula prop).univCl]

noncomputable def addOneTheoryProof : ordinaryPAeq.Proof resultSentence := by
  apply ND.listTheoryProof (A := assumptions)
  · have h1 : addZero.freeVariables = ∅ := by decide
    have h2 : addSucc.freeVariables = ∅ := by decide
    have h3 : transitivity.freeVariables = ∅ := by decide
    have h4 : succCongruence.freeVariables = ∅ := by decide
    have h5 : (inductionFormula prop).freeVariables = ∅ := by decide
    have h6 : (Semiformula.all prop).freeVariables = ∅ := by decide
    simpa [assumptions, axioms, resultSentence, coe_closed _ h1, coe_closed _ h2,
      coe_closed _ h3, coe_closed _ h4, coe_closed _ h5, coe_closed _ h6] using addOneProof
  · intro φ hφ
    simp only [assumptions, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl | rfl | rfl | rfl
    · exact ⟨addZero, .fixed _ (by simp [fixedAxioms]), rfl⟩
    · exact ⟨addSucc, .fixed _ (by simp [fixedAxioms]), rfl⟩
    · exact ⟨transitivity, .fixed _ (by simp [fixedAxioms]), rfl⟩
    · exact ⟨succCongruence, .fixed _ (by simp [fixedAxioms]), rfl⟩
    · exact ⟨inductionFormula prop, .induction prop, rfl⟩

#print axioms addOneTheoryProof
#print axioms addOneProof
#print axioms inductionStep
#print axioms base
#print axioms stepAt
#print axioms succCongrAt
#print axioms transAt
#print axioms addSuccAt
#print axioms addZeroAt
end PA194PAeq.AddOne
