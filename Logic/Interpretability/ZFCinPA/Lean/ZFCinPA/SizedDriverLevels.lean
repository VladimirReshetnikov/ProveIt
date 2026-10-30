import ZFCinPA.SizedDriverComb

/-!
# Levels of the driver step templates

The translation constant `tD`, the compile levels `cD` of the nine step
templates, the working level `wD u`, and the level of the reflection
invariant (`invT_le`).

Part of the bounded `hSchema` driver (`SizedDriver`), split out of one
module so that each Lean process elaborates only a few step proofs.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.SizedDriverSteps

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA
open LeanProofs.BoundedPAConsistency.SizedDerivation
open LeanProofs.ZFCinPA.SetCodeLevels LeanProofs.ZFCinPA.LevelDerivation
open LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.TemplateTranslateLevel
open LeanProofs.ZFCinPA.SizedCongruence (lt_lvB_succ le_of_add_eq fvar0_le)
open LeanProofs.ZFCinPA.SizedPlaceholderCongruence (conn_le)
open LeanProofs.ZFCinPA.SizedLPlumbing LeanProofs.ZFCinPA.SizedLGlue1 LeanProofs.ZFCinPA.SizedLNumOK
open LeanProofs.ZFCinPA.SizedLSlot (tsubst_le_n)
open LeanProofs.ZFCinPA.LTemplate LeanProofs.ZFCinPA.LInvariant LeanProofs.ZFCinPA.LStepAnd
open LeanProofs.ZFCinPA.LStepBasic LeanProofs.ZFCinPA.LStepAtom LeanProofs.ZFCinPA.LStepExT
open LeanProofs.ZFCinPA.LDriverBase LeanProofs.ZFCinPA.LDriverSteps
open LeanProofs.ZFCinPA.SizedOpenTemplateLeaves (cExpG)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local notation "Fm" => Bootstrapping.Formula V ℒₛₑₜ


/-! ## Levels of the step templates -/

theorem memAtom_provable : templTheory 6 ar6 ⊢ memAtomTemplate := by
  simpa using atomTemplate_provable false

theorem eqAtom_provable : templTheory 6 ar6 ⊢ eqAtomTemplate := by
  simpa using atomTemplate_provable true

/-- One summand further right: `a ≤ c → a ≤ b + c`. -/
theorem sumR {a b c : ℕ} (h : a ≤ c) : a ≤ b + c := le_trans h (Nat.le_add_left _ _)

/-! The translation constant of the driver steps

Each summand is an `irreducible_def`: the elaborator's `Nat` defeq support
`whnf`s a summand looking for a numeral, and on a reducible `tA (emb σ)` that
evaluates the translation size of a whole template (a 28 GB runaway, also
when hidden behind `omega`, whose atom lookup is `isDefEq`). -/
irreducible_def sD_and : ℕ := tA (Rewriting.emb andTemplate : Proposition L6)
irreducible_def sD_or : ℕ := tA (Rewriting.emb orTemplate : Proposition L6)
irreducible_def sD_neg : ℕ := tA (Rewriting.emb negTemplate : Proposition L6)
irreducible_def sD_top : ℕ := tA (Rewriting.emb topBase : Proposition L6)
irreducible_def sD_bot : ℕ := tA (Rewriting.emb botBase : Proposition L6)
irreducible_def sD_mem : ℕ := tA (Rewriting.emb memAtomTemplate : Proposition L6)
irreducible_def sD_eq : ℕ := tA (Rewriting.emb eqAtomTemplate : Proposition L6)
irreducible_def sD_ex : ℕ := tA (Rewriting.emb exTemplate : Proposition L6)
irreducible_def sD_all : ℕ := tA (Rewriting.emb allTemplate : Proposition L6)
irreducible_def sD_tot : ℕ := tA (Rewriting.emb (totS F₅ : Sentence L6) : Proposition L6)
irreducible_def sD_refl : ℕ := tA (Rewriting.emb (reflS P₄ F₅ : Sentence L6) : Proposition L6)

/-- The translation constant of the driver, a right-nested sum. -/
def tD : ℕ :=
  sD_and + (sD_or + (sD_neg + (sD_top + (sD_bot + (sD_mem + (sD_eq + (sD_ex +
    (sD_all + (sD_tot + sD_refl)))))))))

theorem tD_and : tA (Rewriting.emb andTemplate : Proposition L6) ≤ tD := by
  rw [← sD_and_def]; unfold tD
  exact Nat.le_add_right _ _
theorem tD_or : tA (Rewriting.emb orTemplate : Proposition L6) ≤ tD := by
  rw [← sD_or_def]; unfold tD
  exact sumR (Nat.le_add_right _ _)
theorem tD_neg : tA (Rewriting.emb negTemplate : Proposition L6) ≤ tD := by
  rw [← sD_neg_def]; unfold tD
  exact sumR (sumR (Nat.le_add_right _ _))
theorem tD_top : tA (Rewriting.emb topBase : Proposition L6) ≤ tD := by
  rw [← sD_top_def]; unfold tD
  exact sumR (sumR (sumR (Nat.le_add_right _ _)))
theorem tD_bot : tA (Rewriting.emb botBase : Proposition L6) ≤ tD := by
  rw [← sD_bot_def]; unfold tD
  exact sumR (sumR (sumR (sumR (Nat.le_add_right _ _))))
theorem tD_mem : tA (Rewriting.emb memAtomTemplate : Proposition L6) ≤ tD := by
  rw [← sD_mem_def]; unfold tD
  exact sumR (sumR (sumR (sumR (sumR (Nat.le_add_right _ _)))))
theorem tD_eq : tA (Rewriting.emb eqAtomTemplate : Proposition L6) ≤ tD := by
  rw [← sD_eq_def]; unfold tD
  exact sumR (sumR (sumR (sumR (sumR (sumR (Nat.le_add_right _ _))))))
theorem tD_ex : tA (Rewriting.emb exTemplate : Proposition L6) ≤ tD := by
  rw [← sD_ex_def]; unfold tD
  exact sumR (sumR (sumR (sumR (sumR (sumR (sumR (Nat.le_add_right _ _)))))))
theorem tD_all : tA (Rewriting.emb allTemplate : Proposition L6) ≤ tD := by
  rw [← sD_all_def]; unfold tD
  exact sumR (sumR (sumR (sumR (sumR (sumR (sumR (sumR (Nat.le_add_right _ _))))))))
theorem tD_tot : tA (Rewriting.emb (totS F₅ : Sentence L6) : Proposition L6) ≤ tD := by
  rw [← sD_tot_def]; unfold tD
  exact sumR (sumR (sumR (sumR (sumR (sumR (sumR (sumR (sumR (Nat.le_add_right _ _)))))))))
theorem tD_refl : tA (Rewriting.emb (reflS P₄ F₅ : Sentence L6) : Proposition L6) ≤ tD := by
  rw [← sD_refl_def]; unfold tD
  exact sumR (sumR (sumR (sumR (sumR (sumR (sumR (sumR (sumR (sumR le_rfl)))))))))

/-- The member level of the driver at placeholder level `u`. -/
def mD (u : V) : V := (tD : V) * (u + 1)

theorem trD_le {u : V} (σ : Sentence L6) (hσ : tA (Rewriting.emb σ : Proposition L6) ≤ tD)
    (Ks : (i : Fin 6) → SF V (ar6 i)) (hK : ∀ i, (Ks i).val ≤ lvB u) :
    (translateFormula Ks (Rewriting.emb σ)).val ≤ lvB (mD u) :=
  lift_lvB (translate_level _ u Ks hK)
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hσ) (Arithmetic.zero_le _))

/-- The compile level of a step template. -/
def cL {σ : Sentence L6} (h : templTheory 6 ar6 ⊢ σ) (u : V) : V :=
  cExpG (tmA h) (tmB h) u + (tmK h : ℕ) + 1

/-- The compile levels of all nine step templates. -/
def cD (u : V) : V := cL andTemplate_provable u + (cL orTemplate_provable u +
  (cL negTemplate_provable u + (cL topBase_provable u + (cL botBase_provable u +
  (cL memAtom_provable u + (cL eqAtom_provable u + (cL exTemplate_provable u +
  cL allTemplate_provable u)))))))

theorem c_and_le (u : V) : cL andTemplate_provable u ≤ cD u := le_self_add
theorem c_or_le (u : V) : cL orTemplate_provable u ≤ cD u := le_trans le_self_add le_add_self
theorem c_neg_le (u : V) : cL negTemplate_provable u ≤ cD u :=
  le_trans le_self_add (le_trans le_add_self le_add_self)
theorem c_top_le (u : V) : cL topBase_provable u ≤ cD u :=
  le_trans le_self_add (le_trans le_add_self (le_trans le_add_self le_add_self))
theorem c_bot_le (u : V) : cL botBase_provable u ≤ cD u :=
  le_trans le_self_add (le_trans le_add_self (le_trans le_add_self (le_trans le_add_self
    le_add_self)))
theorem c_mem_le (u : V) : cL memAtom_provable u ≤ cD u :=
  le_trans le_self_add (le_trans le_add_self (le_trans le_add_self (le_trans le_add_self
    (le_trans le_add_self le_add_self))))
theorem c_eq_le (u : V) : cL eqAtom_provable u ≤ cD u :=
  le_trans le_self_add (le_trans le_add_self (le_trans le_add_self (le_trans le_add_self
    (le_trans le_add_self (le_trans le_add_self le_add_self)))))
theorem c_ex_le (u : V) : cL exTemplate_provable u ≤ cD u :=
  le_trans le_self_add (le_trans le_add_self (le_trans le_add_self (le_trans le_add_self
    (le_trans le_add_self (le_trans le_add_self (le_trans le_add_self le_add_self))))))
theorem c_all_le (u : V) : cL allTemplate_provable u ≤ cD u :=
  le_trans le_add_self (le_trans le_add_self (le_trans le_add_self (le_trans le_add_self
    (le_trans le_add_self (le_trans le_add_self (le_trans le_add_self le_add_self))))))

/-- The working level of the driver steps at placeholder level `u`. -/
def wD (u : V) : V := cD u + 1000 * (mD u + 10) + 20000 * u + 20000

theorem wD_4 {u w : V} (h : wD u ≤ w) : (4 : V) ≤ w :=
  le_trans (le_of_add_eq (y := cD u + 1000 * (mD u + 10) + 20000 * u + 19996) (by unfold wD; ring)) h

theorem wD_m {u w : V} (h : wD u ≤ w) : 10 * (mD u + 6 + 1) + 1 ≤ w :=
  le_trans (le_of_add_eq (y := cD u + 990 * mD u + 29929 + 20000 * u) (by unfold wD; ring)) h

theorem wD_a {u w : V} (h : wD u ≤ w) : 1000 * u + 3000 ≤ w :=
  le_trans (le_of_add_eq (y := cD u + 1000 * (mD u + 10) + 19000 * u + 17000) (by unfold wD; ring)) h

theorem wD_s {u w : V} (h : wD u ≤ w) : 10000 * u + 16000 ≤ w :=
  le_trans (le_of_add_eq (y := cD u + 1000 * (mD u + 10) + 10000 * u + 4000)
    (by unfold wD; ring)) h

theorem wD_i {u w : V} (h : wD u ≤ w) : 100 * u + 238 ≤ w :=
  le_trans (le_of_add_eq (y := 900 * u + 2762) (by ring)) (wD_a h)

theorem wD_c {u w : V} (h : wD u ≤ w) : cD u ≤ w :=
  le_trans (le_of_add_eq (y := 1000 * (mD u + 10) + 20000 * u + 20000) (by unfold wD; ring)) h

theorem wD_ante {u w : V} (h : wD u ≤ w) : 10 * (mD u + 1) + 1 ≤ w :=
  le_trans (le_of_add_eq (y := 60) (by ring)) (wD_m h)

/-- The bounds every step proof uses at its offsets `w + k`. -/
theorem wD_up {u w : V} (h : wD u ≤ w) :
    (∀ k : V, w ≤ w + k) ∧ (∀ k : V, (4 : V) ≤ w + k) ∧
      ∀ k : V, 10 * (mD u + 1) + 1 ≤ w + k :=
  ⟨fun _ => le_self_add, fun _ => le_trans (wD_4 h) le_self_add,
    fun _ => le_trans (wD_ante h) le_self_add⟩

/-- The level of the reflection invariant. -/
theorem invT_le {P : SF V 1} {F : SF V 2} {u : V} (hu : 2 ≤ u) (hP : P.val ≤ lvB u)
    (hF : F.val ≤ lvB u) : (InvT P F).val ≤ lvB (mD u + 6) := by
  have l1 : (TotT F).val ≤ lvB (mD u + 2) :=
    lift_lvB (trD_le (totS F₅) tD_tot _
      (K6_le (top_le hu) hF (top_le hu) hF (top_le hu) hF)) le_self_add
  have l2 : (ReflT P F).val ≤ lvB (mD u + 2) :=
    lift_lvB (trD_le (reflS P₄ F₅) tD_refl _ (K6_le hP hF hP hF hP hF)) le_self_add
  show (TotT F ⋏ ReflT P F).val ≤ _
  rw [Bootstrapping.Semiformula.val_and]
  exact le_trans (conn_le (tag := 4) le_add_self (by norm_num) l1 l2) (lvB_mono (le_of_eq (by ring)))

/-! ## The swapped function-code premise

The function-code definitions of the templates (`maxDefF`, `eqDefF`,
`succDefF`) translate to `∀∀(F.subst swapV ↔ G.subst swapV)`, so the closing
premise of a step is `∀∀(A.subst swapV ↔ A.subst swapV)`, not `∀∀(A ↔ A)`. -/

theorem swapV_le (i : Fin 2) : (swapV (V := V) i).val ≤ lvB 3 := by
  match i with
  | 0 => simpa [swapV] using SizedPlaceholderCongruence.bvar_small (V := V) 1 (by norm_num)
  | 1 => simpa [swapV] using SizedPlaceholderCongruence.bvar_small (V := V) 0 (by norm_num)

/-- **`∀∀(A[swap] ↔ A[swap])`, bounded.** -/
theorem dall2_swap (A : SF V 2) {a : V} (ha : A.val ≤ lvB a) (_h2 : 2 ≤ a) :
    DLv 𝗭𝗙 (insert (∀⁰ ∀⁰ (A.subst swapV 🡘 A.subst swapV) : Fm).val ∅) (10000 * a + 16000) := by
  have hs : (A.subst swapV).val ≤ lvB (10 * (a + 1) + 3) :=
    tsubst_le_n A swapV ha (by norm_num) swapV_le
  have h2' : (2 : V) ≤ 10 * (a + 1) + 3 := le_of_add_eq (y := 10 * a + 11) (by ring)
  exact (dall2_iff _ hs h2').mono (le_of_eq (by ring))

end LeanProofs.ZFCinPA.SizedDriverSteps
