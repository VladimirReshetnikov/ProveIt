import DiophantineConsistency.PRAModelIOpenPairing
import DiophantineConsistency.StrictSigmaOneInduction
import Foundation.FirstOrder.Arithmetic.HFS.Basic
/-! A concrete witness majorant for Foundation's actual `sndIdxDef`, used in
its derivation proof predicate. This does not bound the other syntax or
construct a certificate for the full ZFC refutation sentence. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRASndIdxWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open StrictSigmaOneInduction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
/-- In any IOpen model, every witness required by the literal `bnd`
transformation of Foundation's first-index graph is below `p + 1`. -/
theorem sndIdx_bnd_succ (x p : V) :
    sndIdxDef.val.Evalb ![x,p] →
      (bnd sndIdxDef.val).Evalb ![x,p,p+1] := by
  intro h
  simp [sndIdxDef, pi₂Def, pairDef, subDef] at h
  simp [sndIdxDef, pi₂Def, pairDef, subDef,
    Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs,
    bnd, bnd_open, Rew.subst, Rew.q]
  rcases h with ⟨a, ha, ⟨h₁,h₀⟩, b,hb,hpair⟩
  refine ⟨a, lt_succ_iff_le.mpr ha, ⟨?_,?_⟩, b, lt_succ_iff_le.mpr (le_trans hb ha), lt_succ_iff_le.mpr hb, hpair⟩
  · by_cases hp : 1 ≤ p
    · exact Or.inr (h₁ hp)
    · left
      have ho : ((“1 ≤ #2” : ArithmeticSemiformula Empty 3).neg).Open := by
        change (∼ (“1 ≤ #2” : ArithmeticSemiformula Empty 3)).Open
        exact Semiformula.open_neg.mpr (by simp)
      rw [bnd_open _ ho]
      simp only [Semiformula.eval_castLE]
      have he : (fun i : Fin 3 => ![a,x,p,p+1] (i.castLE (by omega))) = ![a,x,p] := by
        funext i
        refine Fin.cases rfl (fun i => ?_) i
        refine Fin.cases rfl (fun i => ?_) i
        exact Fin.cases rfl (fun i => Fin.elim0 i) i
      rw [he]
      change ((∼ (“1 ≤ #2” : ArithmeticSemiformula Empty 3)).Eval ![a,x,p] Empty.elim)
      simpa [LogicalConnective.HomClass.map_neg] using hp
  · by_cases hp : p = 0
    · exact Or.inr (h₀ hp)
    · left
      have ho : ((“#2 < 1” : ArithmeticSemiformula Empty 3).neg).Open := by
        change (∼ (“#2 < 1” : ArithmeticSemiformula Empty 3)).Open
        exact Semiformula.open_neg.mpr (by simp)
      rw [bnd_open _ ho]
      simp only [Semiformula.eval_castLE]
      change ¬ p < 1
      intro hlt
      apply hp
      have hz : p ≤ 0 := lt_succ_iff_le.mp (by simpa using hlt)
      exact le_antisymm hz (show 0 ≤ p from zero_le)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
section candidate
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- The exact graph and its bounded transformation in every candidate-PRA model. -/
theorem candidate_sndIdx_bound (x p : M) :
    (Semiformula.lMap embedding sndIdxDef.val).Eval ![x,p] Empty.elim →
    (Semiformula.lMap embedding (bnd sndIdxDef.val)).Eval ![x,p,p+1] Empty.elim := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  intro h
  rw [Semiformula.eval_lMap] at h ⊢
  rw [reduct_eq_standard] at h ⊢
  exact sndIdx_bnd_succ x p h
end candidate

def boundBody : Semisentence language 2 :=
  (Semiformula.lMap embedding sndIdxDef.val) 🡒
    (Rew.subst ![#0, #1, applyCode addCode ![#1, applyCode oneCode Fin.elim0]] ▹
      Semiformula.lMap embedding (bnd sndIdxDef.val))

def boundSentence : Sentence language := ∀⁰* boundBody

/-- Candidate PRA proves the universally closed instance with explicit
bound `p + 1`. This is a local component, not the full refutation bound. -/
theorem candidate_proves_sndIdx_bound : PRA ⊢ boundSentence := by
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
  have he' : (Semiformula.lMap embedding sndIdxDef.val).Eval ![e 0,e 1] Empty.elim := by
    have hv : ![e 0,e 1] = e := by
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      exact Fin.cases rfl (fun j => Fin.elim0 j) j
    rw [hv]
    exact he
  have hb := candidate_sndIdx_bound (e 0) (e 1) he'
  simp only [Semiformula.eval_rew]
  have hv : (Semiterm.val e Empty.elim ∘
        (Rew.subst ![#0, #1, applyCode addCode ![#1, applyCode oneCode Fin.elim0]]) ∘ Semiterm.bvar) =
      ![e 0, e 1, e 1+1] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases ?_ (fun j => Fin.elim0 j) j
    simp [Function.comp_def, Rew.subst, applyCode, Semiterm.val_func]
    congr 1
    funext k
    refine Fin.cases rfl (fun k => ?_) k
    refine Fin.cases ?_ (fun k => Fin.elim0 k) k
    change Structure.func (L := language) oneCode
      (Semiterm.val e Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN 2)) =
      Structure.func (L := language) oneCode Fin.elim0
    congr 1
    exact Subsingleton.elim _ _
  have hf : (Semiterm.val e Empty.elim ∘
        (Rew.subst ![#0, #1, applyCode addCode ![#1, applyCode oneCode Fin.elim0]]) ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,hf]
  exact hb
end DiophantineConsistency.PRASndIdxWitnessBound
