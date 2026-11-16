import PA194PAeqLessTransTyped
import PA194PAeqQuoteProof
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.LtTrans
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeq.AddOne PA194PAeq.LessTransTyped
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩

def body : Semiproposition language 3 := (less (.bvar 2) (.bvar 1) ⋏ less (.bvar 1) (.bvar 0)) 🡒 less (.bvar 2) (.bvar 0)
def expected : Proposition language := .all (.all (.all body))
theorem source_normalized : PA194PAeq.formula
    (Rewriting.emb PeanoMinus.Axiom.ltTrans : ArithmeticSemiformula ℕ 0) = expected := by rfl
noncomputable def atTerms (a b c : Tm) : ND.Proof AddLtAdd.axioms ((less a b ⋏ less b c) 🡒 less a c) := by
  apply ND.impIntro
  let Δ := (less a b ⋏ less b c) :: AddLtAdd.axioms
  have h : ND.Proof Δ (less a b ⋏ less b c) := ND.assumption (by simp [Δ])
  exact lessTransAt a b c (ND.andLeft h) (ND.andRight h) (by intro p hp; simp [Δ,hp])
noncomputable def certificate : ND.Proof AddLtAdd.axioms expected := by
  unfold expected
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  have h := atTerms (.fvar 2) (.fvar 1) (.fvar 0)
  simp only [ND.shifted,List.map_cons,List.map_nil]
  change ND.Proof (ND.shifted (ND.shifted (ND.shifted AddLtAdd.axioms))) _
  rw [AddLtAdd.axioms_shift,AddLtAdd.axioms_shift,AddLtAdd.axioms_shift]
  convert h using 1
  simp [body,less,eq,add,succ,zero,Semiformula.free,Rewriting.free,Semiformula.imp_eq,
    Semiformula.neg_eq,Semiformula.neg,Semiformula.rewAux,Rew.free,Rew.subst,Rew.func,Rew.q,emptyFn]
  constructor
  · constructor <;> rfl
  · rfl

def targetSentence : Sentence language := expected.univCl
noncomputable def theoryProof : ordinaryPAeq.Proof targetSentence := by
  let A : List (Sentence language) := AddLtAdd.axioms.map Semiformula.univCl
  apply ND.listTheoryProof (A := A)
  · have he : expected.freeVariables = ∅ := by decide
    have hmap : List.map (fun (φ : Sentence language) => (φ : Proposition language)) A = AddLtAdd.axioms := by
      change List.map (fun (φ : Sentence language) => (φ : Proposition language)) (AddLtAdd.axioms.map Semiformula.univCl) = AddLtAdd.axioms
      rw [List.map_map]
      calc
        _ = AddLtAdd.axioms.map id := List.map_congr_left (fun p hp => coe_closed p (AddLtAdd.axioms_closed p hp))
        _ = AddLtAdd.axioms := List.map_id AddLtAdd.axioms
    change ND.Proof (List.map (fun (φ : Sentence language) => (φ : Proposition language)) A) (targetSentence : Proposition language)
    rw [hmap]
    simpa [targetSentence,coe_closed _ he] using certificate
  · intro φ hφ
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hφ
    exact AddLtAdd.axioms_mem p hp

theorem source_formula : PA194PAeq.formula
    (Rewriting.emb PeanoMinus.Axiom.ltTrans : ArithmeticSemiformula ℕ 0) =
    (Rewriting.emb targetSentence : Semiproposition language 0) := by
  change _ = (targetSentence : Proposition language)
  unfold targetSentence
  rw [coe_closed _ (by decide)]
  exact source_normalized
#print axioms theoryProof
#print axioms source_formula
#print axioms certificate
end PA194PAeq.LtTrans
