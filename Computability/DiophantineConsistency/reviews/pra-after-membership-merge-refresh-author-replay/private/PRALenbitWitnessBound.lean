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
  have he' : (Semiformula.lMap embedding lenbitDef.val).Eval ![e 0,e 1] Empty.elim := by
    have hv : ![e 0,e 1] = e := by
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      exact Fin.cases rfl (fun j => Fin.elim0 j) j
    rw [hv]
    exact he
  have hb := candidate_lenbit_bound (e 0) (e 1) he'
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
end DiophantineConsistency.PRALenbitWitnessBound
