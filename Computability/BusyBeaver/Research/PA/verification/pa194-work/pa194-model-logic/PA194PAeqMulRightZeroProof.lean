import PA194PAeqAddOneProof
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.MulRightZero
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194PAeq.AddOne
variable {Γ : List Fm}
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩
noncomputable def mulZeroAt (t : Tm) (h : mulZero ∈ Γ) : ND.Proof Γ (eq (mul zero t) zero) := by
  have d : ND.Proof Γ mulZero := ND.assumption h
  have e := ND.allElim _ t d
  simpa [mulZero,eq,mul,zero,Semiformula.rewAux,Rew.subst,Rew.func,emptyFn] using e

noncomputable def mulSuccAt (s t : Tm) (h : mulSucc ∈ Γ) :
    ND.Proof Γ (eq (mul (succ s) t) (add t (mul s t))) := by
  have d : ND.Proof Γ mulSucc := ND.assumption h
  have d1 := ND.allElim _ s d
  have d2 := ND.allElim _ t d1
  simpa [mulSucc,eq,mul,add,succ,Semiformula.rewAux,Rew.subst,Rew.func,Rew.q,emptyFn,substShift] using d2

def prop : Semiproposition language 1 := eq (mul (.bvar 0) zero) zero

def axioms : List Fm := [mulZero, mulSucc, addZero, transitivity, inductionFormula prop]

noncomputable def base : ND.Proof axioms (eq (mul zero zero) zero) :=
  mulZeroAt zero (by simp [axioms])

noncomputable def stepAt (x : Tm) : ND.Proof ((eq (mul x zero) zero) :: axioms)
    (eq (mul (succ x) zero) zero) := by
  let Δ := (eq (mul x zero) zero) :: axioms
  have h1 : ND.Proof Δ (eq (mul (succ x) zero) (add zero (mul x zero))) :=
    mulSuccAt x zero (by simp [Δ, axioms])
  have h2 : ND.Proof Δ (eq (add zero (mul x zero)) (mul x zero)) :=
    addZeroAt (mul x zero) (by simp [Δ, axioms])
  have ih : ND.Proof Δ (eq (mul x zero) zero) := ND.assumption (by simp [Δ])
  exact transAt _ _ _ (by simp [Δ, axioms]) h1 (transAt _ _ _ (by simp [Δ, axioms]) h2 ih)

theorem shift_id (p : Fm) (hp : p.freeVariables = ∅) : p.shift = p := by
  apply Semiformula.rew_eq_self_of
  · intro i; exact Fin.elim0 i
  · intro i hi; exact False.elim (by simpa [Semiformula.FVar?,hp] using hi)

theorem axioms_shift : ND.shifted axioms = axioms := by
  have h1 : mulZero.freeVariables = ∅ := by decide
  have h2 : mulSucc.freeVariables = ∅ := by decide
  have h3 : addZero.freeVariables = ∅ := by decide
  have h4 : transitivity.freeVariables = ∅ := by decide
  have h5 : (inductionFormula prop).freeVariables = ∅ := by decide
  simp [ND.shifted, axioms, shift_id _ h1, shift_id _ h2, shift_id _ h3, shift_id _ h4, shift_id _ h5]

noncomputable def inductionStep : ND.Proof axioms
    (.all (implies prop (Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop))) := by
  apply ND.allIntro
  rw [axioms_shift]
  change ND.Proof axioms ((prop 🡒 Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop).free)
  have d := ND.impIntro (stepAt (.fvar 0))
  simpa [prop, implies, Semiformula.free, Semiformula.imp_eq, eq, mul, add, succ, zero,
    Semiformula.neg_eq, Semiformula.neg, Rewriting.free, Semiformula.rewAux, Rew.free, Rew.subst, Rew.func,
    Rew.q, emptyFn, substShift] using d

noncomputable def mulRightZeroProof : ND.Proof axioms (.all prop) := by
  have ind : ND.Proof axioms (inductionFormula prop) := ND.assumption (by simp [axioms])
  change ND.Proof axioms
    ((Semiformula.rewAux (Rew.subst ![zero]) prop) 🡒
      ((.all (prop 🡒 Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop)) 🡒 .all prop)) at ind
  have b : ND.Proof axioms (Semiformula.rewAux (Rew.subst ![zero]) prop) := by
    simpa [prop,eq,mul,add,succ,zero,Semiformula.rewAux,Rew.subst,Rew.func,emptyFn] using base
  have st : ND.Proof axioms (.all (prop 🡒 Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop)) := by
    exact inductionStep
  exact ND.mp st (ND.mp b ind)

def resultSentence : Sentence language := (Semiformula.all prop).univCl

theorem coe_closed (p : Fm) (hp : p.freeVariables = ∅) : (p.univCl : Fm) = p := by
  rw [Semiformula.coe_univCl_eq_univCl']
  exact Semiformula.univCl'_eq_self_of _ hp

def assumptions : List (Sentence language) :=
  [mulZero.univCl, mulSucc.univCl, addZero.univCl, transitivity.univCl,
    (inductionFormula prop).univCl]

noncomputable def mulRightZeroTheoryProof : ordinaryPAeq.Proof resultSentence := by
  apply ND.listTheoryProof (A := assumptions)
  · have h1 : mulZero.freeVariables = ∅ := by decide
    have h2 : mulSucc.freeVariables = ∅ := by decide
    have h3 : addZero.freeVariables = ∅ := by decide
    have h4 : transitivity.freeVariables = ∅ := by decide
    have h5 : (inductionFormula prop).freeVariables = ∅ := by decide
    have h6 : (Semiformula.all prop).freeVariables = ∅ := by decide
    simpa [assumptions, axioms, resultSentence, coe_closed _ h1, coe_closed _ h2,
      coe_closed _ h3, coe_closed _ h4, coe_closed _ h5, coe_closed _ h6] using mulRightZeroProof
  · intro φ hφ
    simp only [assumptions, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl | rfl | rfl | rfl
    · exact ⟨mulZero, .fixed _ (by simp [fixedAxioms]), rfl⟩
    · exact ⟨mulSucc, .fixed _ (by simp [fixedAxioms]), rfl⟩
    · exact ⟨addZero, .fixed _ (by simp [fixedAxioms]), rfl⟩
    · exact ⟨transitivity, .fixed _ (by simp [fixedAxioms]), rfl⟩
    · exact ⟨inductionFormula prop, .induction prop, rfl⟩


#print axioms mulRightZeroTheoryProof
end PA194PAeq.MulRightZero
