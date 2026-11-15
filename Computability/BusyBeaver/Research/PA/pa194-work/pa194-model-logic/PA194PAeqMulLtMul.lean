import PA194PAeqMulLtMulTyped
import PA194PAeqQuoteProof
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.MulLtMul
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeq.AddOne PA194PAeq.MulLtMulTyped
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩

def body : Semiproposition language 3 := (less (.bvar 2) (.bvar 1) ⋏ less zero (.bvar 0)) 🡒 less (mul (.bvar 2) (.bvar 0)) (mul (.bvar 1) (.bvar 0))
def expected : Proposition language := .all (.all (.all body))
theorem source_normalized : PA194PAeq.formula
    (Rewriting.emb PeanoMinus.Axiom.mulLtMul : ArithmeticSemiformula ℕ 0) = expected := by rfl
noncomputable def atTerms (a b c : Tm) : ND.Proof MulAssoc.axioms ((less a b ⋏ less zero c) 🡒 less (mul a c) (mul b c)) := by
  apply ND.impIntro
  let Δ := (less a b ⋏ less zero c) :: MulAssoc.axioms
  have h : ND.Proof Δ (less a b ⋏ less zero c) := ND.assumption (by simp [Δ])
  exact MulLtMulTyped.atTerms a b c (ND.andLeft h) (ND.andRight h) (by intro p hp; simp [Δ,hp])
noncomputable def certificate : ND.Proof MulAssoc.axioms expected := by
  unfold expected
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  have h := atTerms (.fvar 2) (.fvar 1) (.fvar 0)
  simp only [ND.shifted,List.map_cons,List.map_nil]
  change ND.Proof (ND.shifted (ND.shifted (ND.shifted MulAssoc.axioms))) _
  rw [MulAssoc.axioms_shift,MulAssoc.axioms_shift,MulAssoc.axioms_shift]
  convert h using 1
  simp [body,less,eq,add,mul,succ,zero,Semiformula.free,Rewriting.free,Semiformula.imp_eq,
    Semiformula.neg_eq,Semiformula.neg,Semiformula.rewAux,Rew.free,Rew.subst,Rew.func,Rew.q,emptyFn]
  constructor
  · constructor <;> rfl
  · rfl

def targetSentence : Sentence language := expected.univCl
noncomputable def theoryProof : ordinaryPAeq.Proof targetSentence := by
  let A : List (Sentence language) := MulAssoc.axioms.map Semiformula.univCl
  apply ND.listTheoryProof (A := A)
  · have he : expected.freeVariables = ∅ := by decide
    have hmap : List.map (fun (φ : Sentence language) => (φ : Proposition language)) A = MulAssoc.axioms := by
      change List.map (fun (φ : Sentence language) => (φ : Proposition language)) (MulAssoc.axioms.map Semiformula.univCl) = MulAssoc.axioms
      rw [List.map_map]
      calc
        _ = MulAssoc.axioms.map id := List.map_congr_left (fun p hp => coe_closed p (MulAssoc.axioms_closed p hp))
        _ = MulAssoc.axioms := List.map_id MulAssoc.axioms
    change ND.Proof (List.map (fun (φ : Sentence language) => (φ : Proposition language)) A) (targetSentence : Proposition language)
    rw [hmap]
    simpa [targetSentence,coe_closed _ he] using certificate
  · intro φ hφ
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hφ
    exact MulAssoc.axioms_mem p hp

theorem source_formula : PA194PAeq.formula
    (Rewriting.emb PeanoMinus.Axiom.mulLtMul : ArithmeticSemiformula ℕ 0) =
    (Rewriting.emb targetSentence : Semiproposition language 0) := by
  change _ = (targetSentence : Proposition language)
  unfold targetSentence
  rw [coe_closed _ (by decide)]
  exact source_normalized
#print axioms theoryProof
#print axioms source_formula
#print axioms certificate
end PA194PAeq.MulLtMul
