import PA194PAeqAddOneProof
import PA194PAeqQuoteProof
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.EqRelExt
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PA194PAeq.AddOne
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩

def body : Semiproposition language 4 :=
  (eq (.bvar 0) (.bvar 2) ⋏ (eq (.bvar 1) (.bvar 3) ⋏ ⊤)) 🡒
    eq (.bvar 0) (.bvar 1) 🡒 eq (.bvar 2) (.bvar 3)
def expected : Proposition language := .all (.all (.all (.all body)))
theorem source_normalized : PA194PAeq.formula
    (Rewriting.emb (Theory.Eq.relExt (L := ℒₒᵣ) Language.ORing.Rel.eq) : ArithmeticSemiformula ℕ 0) = expected := by
  rfl

noncomputable def symmAt (a b : Tm) {Γ : List Fm} (h : symmetry ∈ Γ) (d : ND.Proof Γ (eq a b)) : ND.Proof Γ (eq b a) := by
  have d0 : ND.Proof Γ symmetry := ND.assumption h
  have d1 := ND.allElim _ a d0
  have d2 := ND.allElim _ b d1
  have h' : ND.Proof Γ (eq a b 🡒 eq b a) := by
    simpa [symmetry,implies,Semiformula.imp_eq,eq,Semiformula.neg_eq,Semiformula.neg,
      Semiformula.rewAux,Rew.subst,Rew.func,Rew.q,emptyFn,substShift] using d2
  exact ND.mp d h'

noncomputable def atTerms (a b c d : Tm) {Γ : List Fm} (hs : symmetry ∈ Γ) (ht : transitivity ∈ Γ) :
    ND.Proof Γ ((eq a c ⋏ (eq b d ⋏ ⊤)) 🡒 eq a b 🡒 eq c d) := by
  apply ND.impIntro
  apply ND.impIntro
  let Δ := eq a b :: (eq a c ⋏ (eq b d ⋏ ⊤)) :: Γ
  have hp : ND.Proof Δ (eq a c ⋏ (eq b d ⋏ ⊤)) := ND.assumption (by simp [Δ])
  have h1 : ND.Proof Δ (eq a c) := ND.andLeft hp
  have h2 : ND.Proof Δ (eq b d) := ND.andLeft (ND.andRight hp)
  have h3 : ND.Proof Δ (eq a b) := ND.assumption (by simp [Δ])
  have h4 : ND.Proof Δ (eq c a) := symmAt a c (by simp [Δ,hs]) h1
  exact transAt _ _ _ (by simp [Δ,ht]) (transAt _ _ _ (by simp [Δ,ht]) h4 h3) h2

noncomputable def certificate : ND.Proof [symmetry,transitivity] expected := by
  unfold expected
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  have hs : symmetry.freeVariables = ∅ := by decide
  have ht : transitivity.freeVariables = ∅ := by decide
  have h := atTerms (.fvar 0) (.fvar 1) (.fvar 2) (.fvar 3) (Γ := [symmetry,transitivity]) (by simp) (by simp)
  simpa [ND.shifted,shift_id _ hs,shift_id _ ht,body,Semiformula.free,Rewriting.free,Semiformula.imp_eq,
    Semiformula.neg_eq,Semiformula.neg,Semiformula.rewAux,Rew.free,Rew.subst,Rew.func,Rew.q,eq,emptyFn] using h

def targetSentence : Sentence language := expected.univCl
theorem targetSentence_coe : (targetSentence : Proposition language) = expected := coe_closed _ (by decide)

noncomputable def theoryProof : ordinaryPAeq.Proof targetSentence := by
  apply ND.listTheoryProof (A := [symmetry.univCl,transitivity.univCl])
  · have hs : symmetry.freeVariables = ∅ := by decide
    have ht : transitivity.freeVariables = ∅ := by decide
    simpa [coe_closed _ hs,coe_closed _ ht,targetSentence_coe] using certificate
  · intro φ hφ
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hφ
    rcases hφ with rfl | rfl
    · exact ⟨symmetry,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨transitivity,.fixed _ (by simp [fixedAxioms]),rfl⟩

theorem source_formula : PA194PAeq.formula
    (Rewriting.emb (Theory.Eq.relExt (L := ℒₒᵣ) Language.ORing.Rel.eq) : ArithmeticSemiformula ℕ 0) =
    (Rewriting.emb targetSentence : Semiproposition language 0) := by
  change _ = (targetSentence : Proposition language)
  rw [targetSentence_coe]
  exact source_normalized
#print axioms theoryProof
#print axioms source_formula
#print axioms certificate
end PA194PAeq.EqRelExt
