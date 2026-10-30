import DiophantineConsistency.PRAModelIOpenPairing
import DiophantineConsistency.StrictSigmaOneInduction
import Foundation.FirstOrder.Arithmetic.HFS.Basic
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRAPairTripleWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open StrictSigmaOneInduction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
theorem pair3_bnd_succ (p a b c : V) :
    pair₃Def.val.Evalb ![p,a,b,c] →
      (bnd pair₃Def.val).Evalb ![p,a,b,c,p+1] := by
  intro h
  simp [pair₃Def, pairDef] at h
  simp [pair₃Def, pairDef, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs,
    bnd, bnd_open, Rew.subst]
  rcases h with ⟨z, hz, hp, hq⟩
  exact ⟨z, lt_succ_iff_le.mpr hz, hp, hq⟩
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
section candidate
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem candidate_pair3_bound (p a b c : M) :
    (Semiformula.lMap embedding pair₃Def.val).Eval ![p,a,b,c] Empty.elim →
    (Semiformula.lMap embedding (bnd pair₃Def.val)).Eval ![p,a,b,c,p+1] Empty.elim := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  intro h
  rw [Semiformula.eval_lMap] at h ⊢
  rw [reduct_eq_standard] at h ⊢
  exact pair3_bnd_succ p a b c h
end candidate

def boundBody : Semisentence language 4 :=
  (Semiformula.lMap embedding pair₃Def.val) 🡒
    (Rew.subst ![#0,#1,#2,#3,applyCode addCode ![#0,applyCode oneCode Fin.elim0]] ▹
      Semiformula.lMap embedding (bnd pair₃Def.val))
def boundSentence : Sentence language := ∀⁰* boundBody

theorem candidate_proves_pair3_bound : PRA ⊢ boundSentence := by
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
  have he' : (Semiformula.lMap embedding pair₃Def.val).Eval ![e 0,e 1,e 2,e 3] Empty.elim := by
    have hv : ![e 0,e 1,e 2,e 3] = e := by
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      refine Fin.cases rfl (fun j => ?_) j
      refine Fin.cases rfl (fun j => ?_) j
      exact Fin.cases rfl (fun j => Fin.elim0 j) j
    rw [hv]
    exact he
  have hb := candidate_pair3_bound (e 0) (e 1) (e 2) (e 3) he'
  simp only [Semiformula.eval_rew]
  have hv : (Semiterm.val e Empty.elim ∘
        (Rew.subst ![#0,#1,#2,#3,applyCode addCode ![#0,applyCode oneCode Fin.elim0]]) ∘ Semiterm.bvar) =
      ![e 0,e 1,e 2,e 3,e 0+1] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases ?_ (fun j => Fin.elim0 j) j
    simp [Function.comp_def, Rew.subst, applyCode, Semiterm.val_func]
    congr 1
    funext j
    refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases ?_ (fun j => Fin.elim0 j) j
    change Structure.func (L := language) oneCode
      (Semiterm.val e Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN 4)) =
      Structure.func (L := language) oneCode Fin.elim0
    congr 1
    exact Subsingleton.elim _ _
  have hf : (Semiterm.val e Empty.elim ∘
      Rew.subst ![#0,#1,#2,#3,applyCode addCode ![#0,applyCode oneCode Fin.elim0]] ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,hf]
  exact hb
end DiophantineConsistency.PRAPairTripleWitnessBound
