import DiophantineConsistency.PRALenbitWitnessBound
import Foundation.FirstOrder.Arithmetic.Exponential.Exp
/-! A local bound for Foundation’s exact `extDef` graph. This does not establish
    bounds for the other subformulas of `exponentialDef`. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRAExtWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
omit [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] in
theorem eval_open_bnd {n : ℕ} (φ : ArithmeticSemisentence n) (ho : φ.Open)
    (e : Fin n → V) (w : V) :
    (bnd φ).Evalb (Fin.snoc e w) ↔ φ.Evalb e := by
  rw [bnd_open φ ho, Semiformula.eval_castLE, snoc_castLE]

theorem ext_bound (a b c : V) :
    extDef.val.Evalb ![a,b,c] →
      (bnd extDef.val).Evalb ![a,b,c,c+1] := by
  intro h
  simp [extDef, divDef, remDef, subDef] at h
  simp [extDef, divDef, remDef, subDef, Semiformula.bexsLTSucc, Semiformula.bexsLT,
    FirstOrder.bexs, bnd, bnd_open, Rew.subst, Rew.q]
  rcases h with ⟨q,hq,⟨hq₁,hq₀⟩,r,hr,⟨hr₁,hr₀⟩,ht₁,ht₀⟩
  have hs4 : Fin.snoc ![q,a,b,c] (c+1) = ![q,a,b,c,c+1] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases rfl (fun j => ?_) j
    exact Fin.cases rfl (fun j => Fin.elim0 j) j
  have hs5 : Fin.snoc ![r,q,a,b,c] (c+1) = ![r,q,a,b,c,c+1] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases rfl (fun j => ?_) j
    exact Fin.cases rfl (fun j => Fin.elim0 j) j
  refine ⟨q,lt_succ_iff_le.mpr hq,⟨?_,?_⟩,r,lt_succ_iff_le.mpr (le_trans hr hq),lt_succ_iff_le.mpr hr,⟨?_,?_⟩,?_,?_⟩
  · by_cases h : 0 < b
    · exact Or.inr (hq₁ h)
    · left
      have hn : (∼ (“0 < #2” : ArithmeticSemisentence 4)).Evalb ![q,a,b,c] := by simpa [LogicalConnective.HomClass.map_neg] using h
      rw [←hs4]
      exact (eval_open_bnd (∼ (“0 < #2” : ArithmeticSemisentence 4)) (by simp) ![q,a,b,c] (c+1)).mpr hn
  · by_cases h : b = 0
    · exact Or.inr (hq₀ h)
    · left
      have hn : (∼ (“#2 = 0” : ArithmeticSemisentence 4)).Evalb ![q,a,b,c] := by simpa [LogicalConnective.HomClass.map_neg] using h
      rw [←hs4]
      exact (eval_open_bnd (∼ (“#2 = 0” : ArithmeticSemisentence 4)) (by simp) ![q,a,b,c] (c+1)).mpr hn
  · by_cases h : 0 < b
    · exact Or.inr (hr₁ h)
    · left
      have hn : (∼ (“0 < #3” : ArithmeticSemisentence 5)).Evalb ![r,q,a,b,c] := by simpa [LogicalConnective.HomClass.map_neg] using h
      rw [←hs5]
      exact (eval_open_bnd (∼ (“0 < #3” : ArithmeticSemisentence 5)) (by simp) ![r,q,a,b,c] (c+1)).mpr hn
  · by_cases h : b = 0
    · exact Or.inr (hr₀ h)
    · left
      have hn : (∼ (“#3 = 0” : ArithmeticSemisentence 5)).Evalb ![r,q,a,b,c] := by simpa [LogicalConnective.HomClass.map_neg] using h
      rw [←hs5]
      exact (eval_open_bnd (∼ (“#3 = 0” : ArithmeticSemisentence 5)) (by simp) ![r,q,a,b,c] (c+1)).mpr hn
  · by_cases h : b*r ≤ q
    · exact Or.inr (ht₁ h)
    · left
      have hn : (∼ (“#3 * #0 ≤ #1” : ArithmeticSemisentence 5)).Evalb ![r,q,a,b,c] := by simpa [LogicalConnective.HomClass.map_neg] using h
      rw [←hs5]
      exact (eval_open_bnd (∼ (“#3 * #0 ≤ #1” : ArithmeticSemisentence 5)) (by simp) ![r,q,a,b,c] (c+1)).mpr hn
  · by_cases h : q < b*r
    · exact Or.inr (ht₀ h)
    · left
      have hn : (∼ (“#1 < #3 * #0” : ArithmeticSemisentence 5)).Evalb ![r,q,a,b,c] := by simpa [LogicalConnective.HomClass.map_neg] using h
      rw [←hs5]
      exact (eval_open_bnd (∼ (“#1 < #3 * #0” : ArithmeticSemisentence 5)) (by simp) ![r,q,a,b,c] (c+1)).mpr hn
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
section candidate
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem candidate_ext_bound (a b c : M) :
    (Semiformula.lMap embedding extDef.val).Eval ![a,b,c] Empty.elim →
    (Semiformula.lMap embedding (bnd extDef.val)).Eval ![a,b,c,c+1] Empty.elim := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  intro h
  rw [Semiformula.eval_lMap] at h ⊢
  rw [reduct_eq_standard] at h ⊢
  exact ext_bound a b c h
end candidate

def boundBody : Semisentence language 3 :=
  (Semiformula.lMap embedding extDef.val) 🡒
    (Rew.subst ![#0, #1, #2, applyCode addCode ![#2, applyCode oneCode Fin.elim0]] ▹
      Semiformula.lMap embedding (bnd extDef.val))

def boundSentence : Sentence language := ∀⁰* boundBody

theorem candidate_proves_ext_bound : PRA ⊢ boundSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  simp only [models_iff, boundSentence, Semiformula.eval_allClosure]
  intro e
  simp only [boundBody, LogicalConnective.HomClass.map_imply]
  intro he
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  have he' : (Semiformula.lMap embedding extDef.val).Eval ![e 0,e 1,e 2] Empty.elim := by
    have hv : ![e 0,e 1,e 2] = e := by
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      refine Fin.cases rfl (fun j => ?_) j
      exact Fin.cases rfl (fun j => Fin.elim0 j) j
    rw [hv]
    exact he
  have hb := candidate_ext_bound (e 0) (e 1) (e 2) he'
  simp only [Semiformula.eval_rew]
  have hv : (Semiterm.val e Empty.elim ∘
        (Rew.subst ![#0, #1, #2, applyCode addCode ![#2, applyCode oneCode Fin.elim0]]) ∘ Semiterm.bvar) =
      ![e 0,e 1,e 2,e 2+1] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases ?_ (fun j => Fin.elim0 j) j
    simp [Function.comp_def, Rew.subst, applyCode, Semiterm.val_func]
    congr 1
    funext k
    refine Fin.cases rfl (fun k => ?_) k
    refine Fin.cases ?_ (fun k => Fin.elim0 k) k
    change Structure.func (L := language) oneCode
      (Semiterm.val e Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN 3)) =
      Structure.func (L := language) oneCode Fin.elim0
    congr 1
    exact Subsingleton.elim _ _
  have hf : (Semiterm.val e Empty.elim ∘
        (Rew.subst ![#0, #1, #2, applyCode addCode ![#2, applyCode oneCode Fin.elim0]]) ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,hf]
  exact hb
end DiophantineConsistency.PRAExtWitnessBound
