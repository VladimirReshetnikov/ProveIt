import DiophantineConsistency.PRAFstIdxWitnessBound
import Foundation.FirstOrder.Arithmetic.Exponential.Bit
/-! A concrete witness majorant for Foundation's actual `lenbitDef`, the
quotient/parity conjunct of `bitDef` used in the derivation fixpoint's coded
membership check. The separate exponential graph and history witnesses remain
unbounded here; this is not a bound for full ZFC refutability. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRALenbitWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
/-- In every IOpen model, the literal bounded translation of the lenbit
graph holds with common bound `y + 1` whenever the original graph holds. -/
theorem lenbit_bound (x y : V) :
    lenbitDef.val.Evalb ![x,y] →
      (bnd lenbitDef.val).Evalb ![x,y,y+1] := by
  intro h
  simp [lenbitDef, divDef, dvd] at h
  simp [lenbitDef, divDef, dvd, Semiformula.bexsLTSucc, Semiformula.bexsLT,
    FirstOrder.bexs, bnd, bnd_open, Rew.subst, Rew.q]
  rcases h with ⟨q, hq, ⟨hp,hz⟩, hn⟩
  refine ⟨q, lt_succ_iff_le.mpr hq, ⟨?_,?_⟩, ?_⟩
  · by_cases hx : 0 < x
    · exact Or.inr (hp hx)
    · left
      have ho : ((“0 < #1” : ArithmeticSemiformula Empty 3).neg).Open := by
        change (∼ (“0 < #1” : ArithmeticSemiformula Empty 3)).Open
        exact Semiformula.open_neg.mpr (by simp)
      rw [bnd_open _ ho]
      simp only [Semiformula.eval_castLE]
      change ¬ 0 < x
      exact hx
  · by_cases hx : x = 0
    · exact Or.inr (hz hx)
    · left
      have ho : ((“#1 = 0” : ArithmeticSemiformula Empty 3).neg).Open := by
        change (∼ (“#1 = 0” : ArithmeticSemiformula Empty 3)).Open
        exact Semiformula.open_neg.mpr (by simp)
      rw [bnd_open _ ho]
      simp only [Semiformula.eval_castLE]
      change x ≠ 0
      exact hx
  · intro r
    by_cases hr : r ≤ q
    · exact Or.inr (hn r hr)
    · left
      exact lt_iff_succ_le.mp (lt_of_not_ge hr)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
section candidate
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- The exact graph bound in every candidate-PRA model. -/
theorem candidate_lenbit_bound (x p : M) :
    (Semiformula.lMap embedding lenbitDef.val).Eval ![x,p] Empty.elim →
    (Semiformula.lMap embedding (bnd lenbitDef.val)).Eval ![x,p,p+1] Empty.elim := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  intro h
  rw [Semiformula.eval_lMap] at h ⊢
  rw [reduct_eq_standard] at h ⊢
  exact lenbit_bound x p h
end candidate

def boundBody : Semisentence language 2 :=
  (Semiformula.lMap embedding lenbitDef.val) 🡒
    (Rew.subst ![#0, #1, applyCode addCode ![#1, applyCode oneCode Fin.elim0]] ▹
      Semiformula.lMap embedding (bnd lenbitDef.val))

def boundSentence : Sentence language := ∀⁰* boundBody

/-- Candidate PRA proves the universally closed graph-bound sentence. -/
theorem candidate_proves_lenbit_bound : PRA ⊢ boundSentence := by
  apply PRASuccBoundCompleteness.proves_succ_bound lenbitDef.val (bnd lenbitDef.val)
  intro M _ _ x p
  exact lenbit_bound x p
end DiophantineConsistency.PRALenbitWitnessBound
