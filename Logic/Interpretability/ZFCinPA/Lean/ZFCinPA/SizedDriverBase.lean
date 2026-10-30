import ZFCinPA.SizedDriverLevels
import ZFCinPA.SizedEnvForm
import ZFCinPA.LDriver

/-!
# The bounded `hSchema` driver: levels and the induction predicate

For a target `M`, the function code of a formula code `q` is at level
`Gd M q = Ad M · 2^(Kd · q)` (`Gd_grow` absorbs the translation factor `tB` of
one compound step), every placeholder is at level `uD M = Gd M M`, and the
induction predicate is `ΘB (Ad M) Kd (Wd M + 60) M`. The induction cases are in
`SizedDriverAtoms`, `SizedDriverConn` and `SizedDriverQuant`; the theorem is
`SizedDriver.driver_le`.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.SizedDriver

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA
open LeanProofs.BoundedPAConsistency.SizedDerivation
open LeanProofs.ZFCinPA.SetCodeLevels LeanProofs.ZFCinPA.LevelDerivation
open LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.TemplateTranslateLevel
open LeanProofs.ZFCinPA.SizedCongruence (lt_lvB_succ le_of_add_eq)
open LeanProofs.ZFCinPA.SizedPlaceholderCongruence (conn_le verum_le)
open LeanProofs.ZFCinPA.SizedLNumOK LeanProofs.ZFCinPA.SizedDriverSteps
open LeanProofs.ZFCinPA.SizedEnvForm (Eb Ef0 envForm_le atomOf_le idx_le falsum_le)
open LeanProofs.ZFCinPA.LTemplate LeanProofs.ZFCinPA.LInvariant LeanProofs.ZFCinPA.LStepAnd
open LeanProofs.ZFCinPA.LStepBasic LeanProofs.ZFCinPA.LStepAtom LeanProofs.ZFCinPA.LStepExT
open LeanProofs.ZFCinPA.LDriverBase LeanProofs.ZFCinPA.LDriverSteps LeanProofs.ZFCinPA.LDriver
open LeanProofs.ZFCinPA.EnvTransform
open LeanProofs.ZFCinPA.NumeralOmega (numChainQ numChainQ_val)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local notation "Fm" => Bootstrapping.Formula V ℒₛₑₜ

/-! ## Levels of the function codes -/

/-! The translation constant of the driver's code bodies, with opaque
summands for the same reason as `SizedDriverSteps.tD`. -/
irreducible_def sB_max : ℕ := tA (Rewriting.emb maxRHS : Semiproposition L6 2)
irreducible_def sB_wb : ℕ := tA (Rewriting.emb (wbS P₀) : Semiproposition L6 2)
irreducible_def sB_wbN : ℕ := tA (Rewriting.emb (wbS (∼P₀)) : Semiproposition L6 2)

/-- The translation constant of the driver's code bodies, a right-nested sum. -/
def tB : ℕ := sB_max + (sB_wb + (sB_wbN + 1))

theorem tB_max : tA (Rewriting.emb maxRHS : Semiproposition L6 2) ≤ tB := by
  rw [← sB_max_def]; unfold tB; exact Nat.le_add_right _ _

theorem tB_wb : tA (Rewriting.emb (wbS P₀) : Semiproposition L6 2) ≤ tB := by
  rw [← sB_wb_def]; unfold tB; exact sumR (Nat.le_add_right _ _)

theorem tB_wbN : tA (Rewriting.emb (wbS (∼P₀)) : Semiproposition L6 2) ≤ tB := by
  rw [← sB_wbN_def]; unfold tB; exact sumR (sumR (Nat.le_add_right _ _))

theorem trB_le {n : ℕ} {u : V} (φ : Semisentence L6 n)
    (hφ : tA (Rewriting.emb φ : Semiproposition L6 n) ≤ tB)
    (Ks : (i : Fin 6) → SF V (ar6 i)) (hK : ∀ i, (Ks i).val ≤ lvB u) :
    (translateFormula Ks (Rewriting.emb φ)).val ≤ lvB ((tB : V) * (u + 1)) :=
  lift_lvB (translate_level _ u Ks hK)
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hφ) (Arithmetic.zero_le _))

theorem maxT_le {F₁ F₃ : SF V 2} {u : V} (hu : 2 ≤ u) (h₁ : F₁.val ≤ lvB u)
    (h₃ : F₃.val ≤ lvB u) : (MaxT F₁ F₃).val ≤ lvB ((tB : V) * (u + 1)) :=
  trB_le maxRHS tB_max _
    (K6_le (top_le hu) h₁ (top_le hu) h₃ (top_le hu) (top_le hu))

theorem wbT_le {P : SF V 1} {u : V} (hu : 2 ≤ u) (hP : P.val ≤ lvB u) :
    (WbT P).val ≤ lvB ((tB : V) * (u + 1)) :=
  trB_le (wbS P₀) tB_wb _
    (K6_le hP (top_le hu) (top_le hu) (top_le hu) (top_le hu) (top_le hu))

theorem wbNT_le {P : SF V 1} {u : V} (hu : 2 ≤ u) (hP : P.val ≤ lvB u) :
    (WbNT P).val ≤ lvB ((tB : V) * (u + 1)) :=
  trB_le (wbS (∼P₀)) tB_wbN _
    (K6_le hP (top_le hu) (top_le hu) (top_le hu) (top_le hu) (top_le hu))

/-! ## The level constants of a target `M` -/

/-- The level of the predicate placeholders and numerals up to `M`. -/
def A0 (M : V) : V := Eb + 200 * M + uN M + 2

/-- The base level of the function codes. -/
def Ad (M : V) : V := (tB : V) * (A0 M + 1) + A0 M + (succT (V := V)).val

/-- The growth exponent of the function codes. -/
def Kd : V := 2 * (tB : V) + 2

/-- **The level of the function code at a formula code `q`.** -/
def Gd (M q : V) : V := Ad M * Exp.exp (Kd * q)

/-- The uniform placeholder level of the driver up to `M`. -/
def uD (M : V) : V := Gd M M

/-- The base derivation level of the driver up to `M`. -/
def Wd (M : V) : V := wD (uD M) + wN M + 10 * M + 100

theorem A0_le_Ad (M : V) : A0 M ≤ Ad M := le_trans le_add_self le_self_add

theorem two_le_A0 (M : V) : (2 : V) ≤ A0 M := le_add_self

theorem succT_le_Ad (M : V) : (succT (V := V)).val ≤ Ad M := le_add_self

theorem Ad_le_Gd (M q : V) : Ad M ≤ Gd M q :=
  le_mul_of_one_le_right (Arithmetic.zero_le _) (one_le_exp _)

theorem Gd_mono (M : V) {a b : V} (h : a ≤ b) : Gd M a ≤ Gd M b :=
  mul_le_mul_of_nonneg_left (exp_monotone_le.mpr (mul_le_mul_of_nonneg_left h
    (Arithmetic.zero_le _))) (Arithmetic.zero_le _)

theorem two_le_Gd (M q : V) : (2 : V) ≤ Gd M q :=
  le_trans (two_le_A0 M) (le_trans (A0_le_Ad M) (Ad_le_Gd M q))

/-- **One compound step stays within the next level.** -/
theorem Gd_grow (M x : V) : (tB : V) * (Gd M x + 1) ≤ Gd M (x + 1) := by
  have he1 : 1 ≤ Gd M x := le_trans (by norm_num) (two_le_Gd M x)
  have hG : Gd M (x + 1) = Gd M x * Exp.exp Kd := by
    unfold Gd; rw [mul_add, mul_one, exp_add]; ring
  rw [hG]
  calc (tB : V) * (Gd M x + 1) ≤ (tB : V) * (Gd M x + Gd M x) :=
        mul_le_mul_of_nonneg_left (_root_.add_le_add le_rfl he1) (Arithmetic.zero_le _)
    _ ≤ Gd M x * Kd := by
        rw [show (tB : V) * (Gd M x + Gd M x) = Gd M x * (2 * tB) by ring]
        exact mul_le_mul_of_nonneg_left (by unfold Kd; exact le_self_add) (Arithmetic.zero_le _)
    _ ≤ Gd M x * Exp.exp Kd := mul_le_mul_of_nonneg_left (lt_exp Kd).le (Arithmetic.zero_le _)

theorem Gd_le_uD {M q : V} (h : q ≤ M) : Gd M q ≤ uD M := Gd_mono M h

theorem two_le_uD (M : V) : (2 : V) ≤ uD M := two_le_Gd M M

theorem A0_le_uD (M : V) : A0 M ≤ uD M := le_trans (A0_le_Ad M) (Ad_le_Gd M M)

theorem wD_le_Wd (M : V) : wD (uD M) ≤ Wd M :=
  le_trans le_self_add (le_trans le_self_add le_self_add)

theorem envF_le {n q M : V} (hq : IsSemiformula ℒₛₑₜ n q) (h : n + q ≤ M) :
    envForm n q ≤ lvB (A0 M) := by
  refine lift_lvB (envForm_le hq) ?_
  calc Eb + 100 * n + 200 * q ≤ Eb + 200 * (n + q) := le_of_add_eq (y := 100 * n) (by ring)
    _ ≤ Eb + 200 * M := _root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left h (by norm_num))
    _ ≤ A0 M := le_trans le_self_add le_self_add

theorem numQ_le_A0 {x M : V} (h : x ≤ M) : (numChainQ x).val ≤ lvB (A0 M) :=
  lift_lvB (numQ_le h) (le_trans le_add_self le_self_add)

theorem succT_le_uD (M : V) : (succT (V := V)).val ≤ lvB (uD M) :=
  lift_lvB (le_lvB_self _) (le_trans (succT_le_Ad M) (Ad_le_Gd M M))

/-! ## The bounded induction predicate -/

/-- **The bounded driver's induction predicate**, with the constants abstracted. -/
def ΘB (A K W M n p : V) : Prop :=
  n + p ≤ M → ∃ f, IsSemiformula ℒₛₑₜ 2 f ∧ f ≤ lvB (A * Exp.exp (K * p)) ∧
    DLv 𝗭𝗙 (insert (invVal (envForm n p) f) ∅) (W + 40 * p)

theorem ΘB_definable (A K W M : V) : 𝚺₁-Relation (ΘB A K W M : V → V → Prop) := by
  unfold ΘB
  simp only [DLv, DerivableLe, lvB]
  definability

theorem ΘB_of_typed {A K W n p : V} (P : SF V 1) (hP : P.val = envForm n p) (F : SF V 2)
    (hF : F.val ≤ lvB (A * Exp.exp (K * p)))
    (h : DLv 𝗭𝗙 (insert (InvT P F).val ∅) (W + 40 * p)) :
    ∃ f, IsSemiformula ℒₛₑₜ 2 f ∧ f ≤ lvB (A * Exp.exp (K * p)) ∧
      DLv 𝗭𝗙 (insert (invVal (envForm n p) f) ∅) (W + 40 * p) :=
  ⟨F.val, F.isSemiformula, hF, by rw [invT_val, hP] at h; exact h⟩

theorem typed_of_ΘB {A K W n m p : V} (hp : IsSemiformula ℒₛₑₜ m p)
    (h : ∃ f, IsSemiformula ℒₛₑₜ 2 f ∧ f ≤ lvB (A * Exp.exp (K * p)) ∧
      DLv 𝗭𝗙 (insert (invVal (envForm n p) f) ∅) (W + 40 * p)) :
    ∃ F : SF V 2, F.val ≤ lvB (A * Exp.exp (K * p)) ∧
      DLv 𝗭𝗙 (insert (InvT (envFormT n hp) F).val ∅) (W + 40 * p) := by
  obtain ⟨f, hf, hfl, hd⟩ := h
  refine ⟨⟨f, hf⟩, hfl, ?_⟩
  rw [invT_val]
  exact hd

/-! ## Auxiliary bounds -/

theorem numOK_W {M x : V} (h : x ≤ M) : wN M + 10 * x ≤ Wd M :=
  le_trans (_root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left h (by norm_num)))
    (le_of_add_eq (y := wD (uD M) + 100) (by unfold Wd; ring))

theorem atom_le_A0 {n k r v M : V} (hR : (ℒₛₑₜ).IsRel k r) (hv : IsSemitermVec ℒₛₑₜ k n v)
    (h : n + ⟪k, r, v⟫ ≤ M) : atomOf n r v ≤ lvB (A0 M) := by
  refine lift_lvB (atomOf_le hR hv) ?_
  calc Ef0 + 6 * (n + ⟪k, r, v⟫) + 18 ≤ Eb + 200 * (n + ⟪k, r, v⟫) :=
        le_of_add_eq (y := 9 * Ef0 + 182 + 194 * (n + ⟪k, r, v⟫)) (by unfold Eb; ring)
    _ ≤ Eb + 200 * M := _root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left h (by norm_num))
    _ ≤ A0 M := le_trans le_self_add le_self_add

theorem slot_idx {n k r v M : V} (hv : IsSemitermVec ℒₛₑₜ k n v) {i : V} (hi : i < k)
    (h : n + ⟪k, r, v⟫ ≤ M) : idx n v.[i] ≤ M :=
  le_trans (le_trans (idx_le (hv.nth hi).isUTerm) (_root_.add_le_add le_rfl
    (le_trans (nth_lt_self (by simpa [hv.lh] using hi)).le
      (le_trans (le_pair_right r v) (le_pair_right k _))))) h

theorem upW (M x y : V) (h : x ≤ y) : Wd M + 60 + 40 * x ≤ Wd M + 60 + 40 * y :=
  _root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left h (by norm_num))

theorem wD_le_W (M x : V) : wD (uD M) ≤ Wd M + 60 + 40 * x :=
  le_trans (wD_le_Wd M) (le_trans le_self_add le_self_add)

end LeanProofs.ZFCinPA.SizedDriver
