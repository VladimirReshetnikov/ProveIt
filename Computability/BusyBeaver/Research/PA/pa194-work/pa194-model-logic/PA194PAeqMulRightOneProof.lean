import PA194PAeqAddCongrAtTyped
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.MulRightOne
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194PAeq.AddOne PA194PAeq.AddCongrTyped
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

noncomputable def reflAt (t : Tm) (h : reflexivity ∈ Γ) : ND.Proof Γ (eq t t) := by
  have d : ND.Proof Γ reflexivity := ND.assumption h
  have e := ND.allElim _ t d
  simpa [reflexivity,eq,Semiformula.rewAux,Rew.subst,Rew.func,emptyFn] using e

def prop : Semiproposition language 1 := eq (mul (.bvar 0) (succ zero)) (.bvar 0)

def axioms : List Fm := [mulZero,mulSucc,addZero,addSucc,addCongruence,reflexivity,succCongruence,transitivity,inductionFormula prop]

noncomputable def base : ND.Proof axioms (eq (mul zero (succ zero)) zero) :=
  mulZeroAt (succ zero) (by simp [axioms])

noncomputable def stepAt (x : Tm) : ND.Proof ((eq (mul x (succ zero)) x) :: axioms)
    (eq (mul (succ x) (succ zero)) (succ x)) := by
  let Δ := (eq (mul x (succ zero)) x) :: axioms
  let one : Tm := succ zero
  have ih : ND.Proof Δ (eq (mul x one) x) := ND.assumption (by simp [Δ,one])
  have h1 : ND.Proof Δ (eq (mul (succ x) one) (add one (mul x one))) :=
    mulSuccAt x one (by simp [Δ,axioms])
  have h2 : ND.Proof Δ (eq (add one (mul x one)) (add one x)) :=
    addCongrAt one one (mul x one) x (by simp [Δ,axioms]) (reflAt one (by simp [Δ,axioms])) ih
  have h3 : ND.Proof Δ (eq (add one x) (succ (add zero x))) :=
    addSuccAt zero x (by simp [Δ,axioms,one])
  have h4 : ND.Proof Δ (eq (succ (add zero x)) (succ x)) :=
    succCongrAt _ _ (by simp [Δ,axioms]) (addZeroAt x (by simp [Δ,axioms]))
  exact transAt _ _ _ (by simp [Δ,axioms]) h1
    (transAt _ _ _ (by simp [Δ,axioms]) h2 (transAt _ _ _ (by simp [Δ,axioms]) h3 h4))

theorem shift_id (p : Fm) (hp : p.freeVariables = ∅) : p.shift = p := by
  apply Semiformula.rew_eq_self_of
  · intro i; exact Fin.elim0 i
  · intro i hi; exact False.elim (by simpa [Semiformula.FVar?,hp] using hi)

theorem axioms_shift : ND.shifted axioms = axioms := by
  have h1 : mulZero.freeVariables = ∅ := by decide
  have h2 : mulSucc.freeVariables = ∅ := by decide
  have h3 : addZero.freeVariables = ∅ := by decide
  have h4 : addSucc.freeVariables = ∅ := by decide
  have h5 : addCongruence.freeVariables = ∅ := by decide
  have h6 : reflexivity.freeVariables = ∅ := by decide
  have h7 : succCongruence.freeVariables = ∅ := by decide
  have h8 : transitivity.freeVariables = ∅ := by decide
  have h9 : (inductionFormula prop).freeVariables = ∅ := by decide
  simp [ND.shifted,axioms,shift_id _ h1,shift_id _ h2,shift_id _ h3,shift_id _ h4,
    shift_id _ h5,shift_id _ h6,shift_id _ h7,shift_id _ h8,shift_id _ h9]

noncomputable def inductionStep : ND.Proof axioms
    (.all (implies prop (Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop))) := by
  apply ND.allIntro
  rw [axioms_shift]
  change ND.Proof axioms ((prop 🡒 Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop).free)
  have d := ND.impIntro (stepAt (.fvar 0))
  simpa [prop, implies, Semiformula.free, Semiformula.imp_eq, eq, mul, add, succ, zero,
    Semiformula.neg_eq, Semiformula.neg, Rewriting.free, Semiformula.rewAux, Rew.free, Rew.subst, Rew.func,
    Rew.q, emptyFn, substShift] using d

noncomputable def mulRightOneProof : ND.Proof axioms (.all prop) := by
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
  [mulZero.univCl,mulSucc.univCl,addZero.univCl,addSucc.univCl,addCongruence.univCl,
   reflexivity.univCl,succCongruence.univCl,transitivity.univCl,(inductionFormula prop).univCl]

noncomputable def mulRightOneTheoryProof : ordinaryPAeq.Proof resultSentence := by
  apply ND.listTheoryProof (A := assumptions)
  · have h1 : mulZero.freeVariables = ∅ := by decide
    have h2 : mulSucc.freeVariables = ∅ := by decide
    have h3 : addZero.freeVariables = ∅ := by decide
    have h4 : addSucc.freeVariables = ∅ := by decide
    have h5 : addCongruence.freeVariables = ∅ := by decide
    have h6 : reflexivity.freeVariables = ∅ := by decide
    have h7 : succCongruence.freeVariables = ∅ := by decide
    have h8 : transitivity.freeVariables = ∅ := by decide
    have h9 : (inductionFormula prop).freeVariables = ∅ := by decide
    have h10 : (Semiformula.all prop).freeVariables = ∅ := by decide
    simpa [assumptions,axioms,resultSentence,coe_closed _ h1,coe_closed _ h2,coe_closed _ h3,
      coe_closed _ h4,coe_closed _ h5,coe_closed _ h6,coe_closed _ h7,coe_closed _ h8,
      coe_closed _ h9,coe_closed _ h10] using mulRightOneProof
  · intro φ hφ
    simp only [assumptions,List.mem_cons,List.not_mem_nil,or_false] at hφ
    rcases hφ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨mulZero,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨mulSucc,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨addZero,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨addSucc,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨addCongruence,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨reflexivity,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨succCongruence,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨transitivity,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨inductionFormula prop,.induction prop,rfl⟩

#print axioms mulRightOneTheoryProof
end PA194PAeq.MulRightOne
