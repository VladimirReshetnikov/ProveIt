import ZFCinPA.LGlueCodes

set_option autoImplicit false
noncomputable section

/-!
# Environments matching the free variables

The glue between `envForm` and `relativize` compares a formula with free
variables `&0, …, &(j-1)` against its environment transform read at an
environment `t` whose slot `i` holds `&i`. That condition, for an internal
(possibly nonstandard) `j`, is the code `mVal j`, by primitive recursion in
the ambient model:

* `mVal 0 = ⌜t is functional⌝`;
* `mVal (j + 1) = ∃t₁ ∃z (z = &0 ∧ t = econs z t₁ ∧ (shift (mVal j))(t₁))`.

The successor clause is literally the freed form of the template piece the
glue's quantifier step reads, so that step's code identity is definitional.
The three fixed codes travel as parameters of the recursion, never as
numerals inside an arithmetic formula.
-/

namespace LeanProofs.ZFCinPA.LMatch

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.EnvTransform LeanProofs.ZFCinPA.LDriverBase
open scoped LO.FirstOrder.Arithmetic

/-- "`t` is functional". -/
def funcS : SetTheorySemisentence 1 :=
  “t. ∀ x, ∀ y, ∀ y', !LClosure.pmemS t x y → !LClosure.pmemS t x y' → y = y'”

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `z = &0`, at level one. -/
def zT : SF V 1 :=
  Bootstrapping.Semiformula.rel (Language.Eq.eq : (ℒₛₑₜ).Rel 2)
    ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.fvar 0]

/-- The same code, read at level three. -/
def zT3 : SF V 3 :=
  Bootstrapping.Semiformula.rel (Language.Eq.eq : (ℒₛₑₜ).Rel 2)
    ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.fvar 0]

lemma zT3_val : (zT3 (V := V)).val = (zT (V := V)).val := by
  simp [zT, zT3]

/-- `t = econs z t₁` with `z = #0`, `t₁ = #1`, `t = #2`. -/
def eT : SF V 3 :=
  (⌜econsS⌝ : SF V 3).subst
    ![Bootstrapping.Semiterm.bvar 2, Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.bvar 1]

/-- The base: `t` is functional. -/
def fT : SF V 1 := ⌜funcS⌝

namespace MatchRec

def blueprint : PR.Blueprint 3 where
  zero := .mkSigma “out c0 cZ cE. out = c0”
  succ := .mkSigma “out prev time c0 cZ cE.
    ∃ s, !(shiftGraph ℒₛₑₜ) s prev ∧ ∃ b, !qqBvarDef b 1 ∧ ∃ w, !adjoinDef w b 0 ∧
    ∃ u, !(substsGraph ℒₛₑₜ) u w s ∧ ∃ a₁, !qqAndDef a₁ cE u ∧ ∃ a₂, !qqAndDef a₂ cZ a₁ ∧
    ∃ e₁, !qqExsDef e₁ a₂ ∧ !qqExsDef out e₁”

def construction : PR.Construction V blueprint where
  zero v := v 0
  succ v _ prev := ^∃ ^∃ (v 1 ^⋏ (v 2 ^⋏ subst ℒₛₑₜ (^#1 ∷ 0) (shift ℒₛₑₜ prev)))
  zero_defined := .mk fun e ↦ by simp [blueprint]
  succ_defined := .mk fun e ↦ by simp [blueprint]

end MatchRec

/-- The recursion, with its three fixed codes as parameters. -/
def mRec (c0 cZ cE j : V) : V := MatchRec.construction.result ![c0, cZ, cE] j

instance mRec_definable : 𝚺₁-Function₄ (mRec : V → V → V → V → V) := by
  have h := (MatchRec.construction.result_defined.to_definable (V := V)).retraction
    (![0, 4, 1, 2, 3] : Fin 5 → Fin 5)
  refine HierarchySymbol.Definable.of_iff h (fun v ↦ ?_)
  simp only [mRec]
  apply iff_of_eq
  congr 2
  all_goals first
    | rfl
    | (funext i
       match i with
       | 0 => rfl
       | 1 => rfl
       | 2 => rfl)

/-- **The matching code** for `j` free variables. -/
def mVal (j : V) : V := mRec (fT (V := V)).val (zT (V := V)).val (eT (V := V)).val j

@[simp] lemma mVal_zero : mVal (0 : V) = (fT (V := V)).val := by
  simp [mVal, mRec, MatchRec.construction]

@[simp] lemma mVal_succ (j : V) :
    mVal (j + 1) = ^∃ ^∃ ((zT (V := V)).val ^⋏ ((eT (V := V)).val ^⋏
      subst ℒₛₑₜ (^#1 ∷ 0) (shift ℒₛₑₜ (mVal j)))) := by
  simp [mVal, mRec, MatchRec.construction]

instance mVal_definable : 𝚺₁-Function₁ (mVal : V → V) := by
  unfold mVal
  definability

lemma isSemiformula_mVal (j : V) : IsSemiformula ℒₛₑₜ 1 (mVal j) := by
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using (fT (V := V)).isSemiformula
  case succ j ih =>
    let P : SF V 1 := ⟨mVal j, by simpa using ih⟩
    have h := (∃⁰ ∃⁰ (zT3 ⋏ (eT ⋏ P.shift.subst
      (![Bootstrapping.Semiterm.bvar 1] : Bootstrapping.SemitermVec V ℒₛₑₜ 1 3))) :
        SF V 1).isSemiformula
    have hv : (∃⁰ ∃⁰ (zT3 ⋏ (eT ⋏ P.shift.subst
      (![Bootstrapping.Semiterm.bvar 1] : Bootstrapping.SemitermVec V ℒₛₑₜ 1 3))) :
        SF V 1).val = mVal (j + 1) := by
      simp [mVal_succ, zT3_val, P, Bootstrapping.SemitermVec.val, Matrix.vecHead,
        Matrix.vecTail]
    rw [← hv]
    simpa using h

/-- The typed matching formula. -/
def MT (j : V) : SF V 1 := ⟨mVal j, by simpa using isSemiformula_mVal j⟩

end LeanProofs.ZFCinPA.LMatch
