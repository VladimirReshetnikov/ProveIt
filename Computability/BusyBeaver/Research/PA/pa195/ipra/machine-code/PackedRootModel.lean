import PackedClock
import DiophantineConsistency.PRAOpenInduction

set_option autoImplicit false
/-! Correctness of the explicit root code in every candidate PRA model.
The square invariant is quantifier-free in the PRA code language and is
proved by the available model open-induction theorem. -/
namespace PackedRootModel
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAOpenInduction
open PRAModelIOpenPairing PRAMultiplication PRAQOrder PRAIsZero PRABooleanOps
open PRAHistoryPairCode PRASelectCode ConfigurationStep PackedClock

def xTerm : Semiterm language Nat 1 := .bvar 0
def rTerm : Semiterm language Nat 1 := .func rootCode ![xTerm]
def rsTerm : Semiterm language Nat 1 := .func Code.succ ![rTerm]
def r2Term : Semiterm language Nat 1 := .func mulCode ![rTerm,rTerm]
def rs2Term : Semiterm language Nat 1 := .func mulCode ![rsTerm,rsTerm]
def rootInvariant : Semiformula language Nat 1 :=
  .and (.nrel Language.ORing.Rel.lt ![xTerm,r2Term]) (.rel Language.ORing.Rel.lt ![xTerm,rs2Term])

theorem rootInvariant_open : rootInvariant.Open := by
  simp [rootInvariant, Semiformula.Open, Semiformula.qr]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
noncomputable local instance : DecidableRel ((· < ·) : M → M → Prop) := Classical.decRel _

def root (x : M) : M := Structure.func (L := language) rootCode (fun _ => x)

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem rootInvariant_eval (x : M) (e : Nat → M) : rootInvariant.Eval ![x] e ↔
    ¬ x < root x * root x ∧ x < (Structure.func (L := language) Code.succ (fun _ => root x)) *
      (Structure.func (L := language) Code.succ (fun _ => root x)) := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] rootInvariant ↔ _
  simp only [rootInvariant, Semiformula.EvalAux]
  have h0 : (fun i => Semiterm.val ![x] e (![xTerm,r2Term] i)) =
      ![x, root x * root x] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
      change Structure.func (L := language) mulCode _ = _
      congr 1
      funext k
      refine Fin.cases ?_ (fun j => ?_) k
      · simp [rTerm, xTerm, root, Semiterm.val_func, Semiterm.val_bvar, Matrix.fun_eq_vec_one]
      · refine Fin.cases ?_ (fun l => Fin.elim0 l) j
        simp [rTerm, xTerm, root, Semiterm.val_func, Semiterm.val_bvar, Matrix.fun_eq_vec_one]
  have h1 : (fun i => Semiterm.val ![x] e (![xTerm,rs2Term] i)) =
      ![x, (Structure.func (L := language) Code.succ (fun _ => root x)) *
        (Structure.func (L := language) Code.succ (fun _ => root x))] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
      change Structure.func (L := language) mulCode _ = _
      congr 1
      funext k
      refine Fin.cases ?_ (fun j => ?_) k
      · simp [rTerm, rsTerm, xTerm, root, Semiterm.val_func, Semiterm.val_bvar, Matrix.fun_eq_vec_one]
      · refine Fin.cases ?_ (fun l => Fin.elim0 l) j
        simp [rTerm, rsTerm, xTerm, root, Semiterm.val_func, Semiterm.val_bvar, Matrix.fun_eq_vec_one]
  rw [h0,h1]
  rfl

theorem modelUnary {n : Nat} (f : Code 1) (a : Code n) (e : Fin n → M) :
    Structure.func (L := language) (unary f a) e =
      Structure.func (L := language) f (fun _ => Structure.func (L := language) a e) := by
  rw [unary, modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => Fin.elim0 j) i
  rfl

theorem modelLtZero (x y : M) :
    Structure.func (L := language) ltBitCode ![x,y] = (0 : M) ↔ ¬x < y := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hb : IsBit (Structure.func (L := language) ltBitCode ![x,y]) := by
    rw [modelLtBit]
    exact modelNonzeroBit _
  have hd : x < y ↔ Structure.func (L := language) ltBitCode ![x,y] = (1 : M) := modelLtBitDefinition x y
  constructor
  · intro hz hxy
    have ho := hd.mp hxy
    have : (0 : M) = 1 := hz.symm.trans ho
    exact zero_ne_one this
  · intro hxy
    rcases hb with hz | ho
    · exact hz
    · exact False.elim (hxy (hd.mpr ho))

theorem modelRootStepFormula (i s : M) :
    Structure.func (L := language) rootStep ![i,s] =
      if (s+1)*(s+1) < (i+1)+1 then s+1 else s := by
  classical
  simp only [rootStep, modelSelectAmong, modelBin, inc, modelUnary, modelProjection,
    modelSelectAll, ← modelAddOne]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  change (if Structure.func (L := language) ltBitCode ![(s+1)*(s+1),(i+1)+1] = 0
    then s else s+1) = _
  rw [modelLtZero]
  split_ifs <;> simp_all

theorem modelRootInvariant (x : M) :
    root x * root x ≤ x ∧ x < (root x + 1) * (root x + 1) := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let e : Nat → M := fun _ => x
  have main : rootInvariant.Eval ![x] e := by
    apply modelOpenInduction (M := M) rootInvariant rootInvariant_open e
    · apply (rootInvariant_eval (0 : M) e).mpr
      have hz : root (0 : M) = 0 := modelRootZero
      rw [hz, ← modelAddOne]
      rw [not_lt]
      change (0 : M) * 0 ≤ 0 ∧ (0 : M) < (0+1)*(0+1)
      simp
    · intro y hy
      rw [← modelAddOne]
      apply (rootInvariant_eval (y+1) e).mpr
      have hi := (rootInvariant_eval y e).mp hy
      rw [← modelAddOne] at hi ⊢
      rw [not_lt] at hi ⊢
      change root y * root y ≤ y ∧ y < (root y+1)*(root y+1) at hi
      change root (y+1) * root (y+1) ≤ y+1 ∧ y+1 < (root (y+1)+1)*(root (y+1)+1)
      have hs : root (y+1) =
          if (root y+1)*(root y+1) < (y+1)+1 then root y+1 else root y := by
        change Structure.func (L := language) rootCode
          (fun _ => Structure.func (L := language) addCode ![y, Structure.func (L := language) oneCode Fin.elim0]) = _
        rw [modelAddOne, modelRootSucc, modelRootStepFormula]
        rfl
      rw [hs]
      split_ifs with h
      · have heq : (root y+1)*(root y+1) = y+1 := by
          apply le_antisymm
          · exact le_iff_lt_succ.mpr h
          · exact lt_iff_succ_le.mp hi.2
        constructor
        · exact heq.le
        · rw [←heq]
          exact mul_self_lt_mul_self (by simp) (lt_add_one _)
      · constructor
        · exact le_trans hi.1 (le_of_lt (lt_add_one y))
        · exact lt_of_not_ge (by simpa [le_iff_lt_succ] using h)
  have hf := (rootInvariant_eval x e).mp main
  rw [← modelAddOne, not_lt] at hf
  exact hf

theorem modelRootGraph (x : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    root x = sqrt x := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  exact sqrt_graph.mpr (modelRootInvariant x)
#print axioms modelRootGraph

end models
end PackedRootModel
