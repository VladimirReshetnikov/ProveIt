import PA194PAeqLessCongrTyped
import PA194PAeqQuoteProof
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.AddEqOfLt
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PA194PAeq.AddOne
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩

def diff {ξ : Type} {n : Nat} (s t : Semiterm language ξ n) : Semiformula language ξ n :=
  .exs (eq (add (Rew.bShift s) (.bvar 0)) (Rew.bShift t))

noncomputable def atTerms (a b : Tm) : ND.Proof [] (less a b 🡒 diff a b) := by
  apply ND.impIntro
  let Γ := [less a b]
  let P : Semiproposition language 1 := eq (add (Rew.bShift a) (succ (.bvar 0))) (Rew.bShift b)
  have hp0 : ND.Proof Γ (less a b) := ND.assumption (by simp [Γ])
  have hp : ND.Proof Γ (∃⁰ P) := by
    convert hp0 using 1 <;> rfl
  apply ND.exsElim hp
  let Δ := P.free :: ND.shifted Γ
  let a' : Tm := Rew.shift a
  let b' : Tm := Rew.shift b
  let witness : Tm := .fvar 0
  have hfreeShift (t : Tm) :
      (Rew.bind ![&0] (fun m => &(m+1))) (Rew.bShift t) = Rew.shift t := by
    simpa [Rew.free] using (Rew.free_bShift_app t)
  have hw : ND.Proof Δ (eq (add a' (succ witness)) b') := by
    have h : ND.Proof Δ P.free := ND.assumption (by simp [Δ])
    simpa [Δ,P,a',b',witness,Semiformula.free,Rewriting.free,Semiformula.rewAux,Rew.free,Rew.subst,Rew.func,Rew.q,eq,add,succ,emptyFn,substShift,hfreeShift] using h
  let Q : Semiproposition language 1 := eq (add (Rew.bShift a') (.bvar 0)) (Rew.bShift b')
  have hq : ND.Proof Δ (∃⁰ Q) := by
    apply ND.exsIntro Q (succ witness)
    simpa [Q,eq,add,succ,Semiformula.rewAux,Rew.subst,Rew.func,emptyFn,substShift] using hw
  have hshift (t : Tm) : (Rew.shift.q) (Rew.bShift t) = Rew.bShift (Rew.shift t) := by exact Rew.q_comp_bShift_app Rew.shift t
  simp only [Rew.shift,Rew.map,Rew.q,emptyFn,Matrix.vecCons_empty_eq_singleton] at hshift
  change ND.Proof Δ (Semiformula.rewAux Rew.shift (diff a b))
  simpa [Δ,Q,a',b',P,diff,Semiformula.rewAux,Rew.shift,Rew.map,Rew.func,Rew.q,eq,add,succ,emptyFn,hshift] using hq

def body : Semiproposition language 2 := less (.bvar 1) (.bvar 0) 🡒 diff (.bvar 1) (.bvar 0)
def expected : Proposition language := .all (.all body)
theorem source_normalized : PA194PAeq.formula
    (Rewriting.emb PeanoMinus.Axiom.addEqOfLt : ArithmeticSemiformula ℕ 0) = expected := by rfl

noncomputable def certificate : ND.Proof [] expected := by
  unfold expected
  apply ND.allIntro
  apply ND.allIntro
  have h := atTerms (.fvar 1) (.fvar 0)
  simp only [ND.shifted,List.map_nil]
  convert h using 1
  simp [body,less,diff,Semiformula.free,Rewriting.free,Semiformula.imp_eq,Semiformula.neg_eq,
    Semiformula.neg,Semiformula.rewAux,Rew.free,Rew.subst,Rew.func,Rew.q,eq,add,succ,emptyFn]
  constructor <;> rfl

def targetSentence : Sentence language := expected.univCl
theorem targetSentence_coe : (targetSentence : Proposition language) = expected := coe_closed _ (by decide)
noncomputable def theoryProof : ordinaryPAeq.Proof targetSentence := by
  apply ND.listTheoryProof (A := [])
  · simpa [targetSentence_coe] using certificate
  · intro φ hφ; simp at hφ

theorem source_formula : PA194PAeq.formula
    (Rewriting.emb PeanoMinus.Axiom.addEqOfLt : ArithmeticSemiformula ℕ 0) =
    (Rewriting.emb targetSentence : Semiproposition language 0) := by
  change _ = (targetSentence : Proposition language)
  rw [targetSentence_coe]
  exact source_normalized
#print axioms theoryProof
#print axioms source_formula
#print axioms certificate
end PA194PAeq.AddEqOfLt
