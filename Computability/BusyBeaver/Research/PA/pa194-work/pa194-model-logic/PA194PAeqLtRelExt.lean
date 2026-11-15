import PA194PAeqLessCongrTyped
import PA194PAeqQuoteProof
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.LtRelExt
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PA194PAeq.AddOne PA194PAeq.LessCongrTyped
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩

def body : Semiproposition language 4 :=
  (eq (.bvar 0) (.bvar 2) ⋏ (eq (.bvar 1) (.bvar 3) ⋏ ⊤)) 🡒
    less (.bvar 0) (.bvar 1) 🡒 less (.bvar 2) (.bvar 3)
def expected : Proposition language := .all (.all (.all (.all body)))
theorem source_normalized : PA194PAeq.formula
    (Rewriting.emb (Theory.Eq.relExt (L := ℒₒᵣ) Language.ORing.Rel.lt) : ArithmeticSemiformula ℕ 0) = expected := by
  rfl

noncomputable def atTerms (a b c d : Tm) {Γ : List Fm}
    (hadd : addCongruence ∈ Γ) (hs : symmetry ∈ Γ) (ht : transitivity ∈ Γ) (hr : reflexivity ∈ Γ) :
    ND.Proof Γ ((eq a c ⋏ (eq b d ⋏ ⊤)) 🡒 less a b 🡒 less c d) := by
  apply ND.impIntro
  apply ND.impIntro
  let Δ := less a b :: (eq a c ⋏ (eq b d ⋏ ⊤)) :: Γ
  have hp : ND.Proof Δ (eq a c ⋏ (eq b d ⋏ ⊤)) := ND.assumption (by simp [Δ])
  have h1 : ND.Proof Δ (eq a c) := ND.andLeft hp
  have h2 : ND.Proof Δ (eq b d) := ND.andLeft (ND.andRight hp)
  have h3 : ND.Proof Δ (less a b) := ND.assumption (by simp [Δ])
  exact lessCongrAt a b c d h1 h2 h3 (by simp [Δ,hadd]) (by simp [Δ,hs])
    (by simp [Δ,ht]) (by simp [Δ,hr])

noncomputable def certificate : ND.Proof [addCongruence,symmetry,transitivity,reflexivity] expected := by
  unfold expected
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  have h0 : addCongruence.freeVariables = ∅ := by decide
  have h1 : symmetry.freeVariables = ∅ := by decide
  have h2 : transitivity.freeVariables = ∅ := by decide
  have h3 : reflexivity.freeVariables = ∅ := by decide
  have h := atTerms (.fvar 0) (.fvar 1) (.fvar 2) (.fvar 3)
    (Γ := [addCongruence,symmetry,transitivity,reflexivity]) (by simp) (by simp) (by simp) (by simp)
  simp only [ND.shifted,List.map_cons,List.map_nil,shift_id _ h0,shift_id _ h1,shift_id _ h2,shift_id _ h3]
  convert h using 1
  simp [body,less,Semiformula.free,Rewriting.free,Semiformula.imp_eq,Semiformula.neg_eq,
    Semiformula.neg,Semiformula.rewAux,Rew.free,Rew.subst,Rew.func,Rew.q,eq,add,succ,emptyFn]
  constructor <;> rfl

def targetSentence : Sentence language := expected.univCl
theorem targetSentence_coe : (targetSentence : Proposition language) = expected := coe_closed _ (by decide)

noncomputable def theoryProof : ordinaryPAeq.Proof targetSentence := by
  apply ND.listTheoryProof (A := [addCongruence.univCl,symmetry.univCl,transitivity.univCl,reflexivity.univCl])
  · have h0 : addCongruence.freeVariables = ∅ := by decide
    have h1 : symmetry.freeVariables = ∅ := by decide
    have h2 : transitivity.freeVariables = ∅ := by decide
    have h3 : reflexivity.freeVariables = ∅ := by decide
    simpa [coe_closed _ h0,coe_closed _ h1,coe_closed _ h2,coe_closed _ h3,targetSentence_coe] using certificate
  · intro φ hφ
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hφ
    rcases hφ with rfl | rfl | rfl | rfl
    · exact ⟨addCongruence,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨symmetry,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨transitivity,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨reflexivity,.fixed _ (by simp [fixedAxioms]),rfl⟩

theorem source_formula : PA194PAeq.formula
    (Rewriting.emb (Theory.Eq.relExt (L := ℒₒᵣ) Language.ORing.Rel.lt) : ArithmeticSemiformula ℕ 0) =
    (Rewriting.emb targetSentence : Semiproposition language 0) := by
  change _ = (targetSentence : Proposition language)
  rw [targetSentence_coe]
  exact source_normalized
#print axioms theoryProof
#print axioms source_formula
#print axioms certificate
end PA194PAeq.LtRelExt
