import PA194PAeqAddCongrAtTyped
import PA194PAeqQuoteProof
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeq.AddExtNormalized
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PA194PAeq.AddOne PA194PAeq.AddCongrTyped
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩

def body : Semiproposition language 4 :=
  (eq (.bvar 0) (.bvar 2) ⋏ (eq (.bvar 1) (.bvar 3) ⋏ ⊤)) 🡒
    eq (add (.bvar 0) (.bvar 1)) (add (.bvar 2) (.bvar 3))
def expected : Proposition language := .all (.all (.all (.all body)))
theorem source_normalized : PA194PAeq.formula
    (Rewriting.emb (Theory.Eq.funcExt (L := ℒₒᵣ) Language.ORing.Func.add) : ArithmeticSemiformula ℕ 0) = expected := by
  rfl
noncomputable def atTerms (a b c d : Tm) {Γ : List Fm} (h : addCongruence ∈ Γ) :
    ND.Proof Γ ((eq a c ⋏ (eq b d ⋏ ⊤)) 🡒 eq (add a b) (add c d)) := by
  apply ND.impIntro
  let Δ := (eq a c ⋏ (eq b d ⋏ ⊤)) :: Γ
  have hp : ND.Proof Δ (eq a c ⋏ (eq b d ⋏ ⊤)) := ND.assumption (by simp [Δ])
  have h1 : ND.Proof Δ (eq a c) := ND.andLeft hp
  have h2 : ND.Proof Δ (eq b d) := ND.andLeft (ND.andRight hp)
  exact addCongrAt a c b d (by simp [Δ,h]) h1 h2

noncomputable def certificate : ND.Proof [addCongruence] expected := by
  unfold expected
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  have hfree : addCongruence.freeVariables = ∅ := by decide
  have hid := shift_id addCongruence hfree
  have h := atTerms (.fvar 0) (.fvar 1) (.fvar 2) (.fvar 3) (Γ := [addCongruence]) (by simp)
  simpa [ND.shifted,hid,body,Semiformula.free,Rewriting.free,Semiformula.imp_eq,
    Semiformula.neg_eq,Semiformula.neg,Semiformula.rewAux,
    Rew.free,Rew.subst,Rew.func,Rew.q,eq,add,emptyFn] using h
def targetSentence : Sentence language := expected.univCl

theorem targetSentence_coe : (targetSentence : Proposition language) = expected := by
  unfold targetSentence
  exact coe_closed _ (by decide)

noncomputable def theoryProof : ordinaryPAeq.Proof targetSentence := by
  apply ND.singleTheoryProof (φ := addCongruence.univCl)
  · have hfree : addCongruence.freeVariables = ∅ := by decide
    simpa only [coe_closed _ hfree,targetSentence_coe] using certificate
  · exact ⟨addCongruence,.fixed _ (by simp [fixedAxioms]),rfl⟩

theorem source_formula : PA194PAeq.formula
    (Rewriting.emb (Theory.Eq.funcExt (L := ℒₒᵣ) Language.ORing.Func.add) : ArithmeticSemiformula ℕ 0) =
    (Rewriting.emb targetSentence : Semiproposition language 0) := by
  change _ = (targetSentence : Proposition language)
  rw [targetSentence_coe]
  exact source_normalized
#print axioms theoryProof
#print axioms source_formula
#print axioms certificate
#print axioms source_normalized
end PA194PAeq.AddExtNormalized
