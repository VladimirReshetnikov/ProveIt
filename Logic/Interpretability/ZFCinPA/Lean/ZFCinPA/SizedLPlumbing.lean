import ZFCinPA.SizedOpenTemplateLeaves
import ZFCinPA.SizedShiftCancel

/-!
# Plumbing for the bounded `L` inductions

The `L` inductions compile fixed templates with `LDriverSteps.compiled` and
`LGlue1.compiledG`, both thin wrappers around `LTemplate.compileT_provable`.
`compiledLe` is the bounded replacement on the level scale `DLv`: a template
provable in `templTheory` compiles at arbitrary placeholders of level `u`
within level `cExpG A B u + K`. The meta-level constants `A`, `B` and `K`
come from the template's fixed derivation, `h.get.toProof2`.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.SizedLPlumbing

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA
open LeanProofs.BoundedPAConsistency.SizedDerivation
open LeanProofs.ZFCinPA.SetCodeLevels LeanProofs.ZFCinPA.LevelDerivation
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.SizedTemplateCompiler LeanProofs.ZFCinPA.SizedOpenTemplate
open LeanProofs.ZFCinPA.BufferedTemplateProofCompiler
open LeanProofs.ZFCinPA.SizedOpenTemplateLeaves

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A stage tower over `lvB X + 1` is one level per stage. -/
theorem stg_lvB : ∀ (n : ℕ) {X : V}, 4 ≤ X → stg n (lvB X + 1) ≤ lvB (X + n + 1)
  | 0, X, _ => by
      simpa [stg] using lt_iff_succ_le.mp (SizedCongruence.lt_lvB_succ (le_rfl : lvB X ≤ lvB X))
  | n + 1, X, hX => by
      have ih := stg_lvB n hX
      have h4 : (4 : V) ≤ X + n + 1 := le_trans hX (le_trans le_self_add le_self_add)
      calc stg (n + 1) (lvB X + 1) = 1024 * stg n (lvB X + 1) := rfl
        _ ≤ 1024 * lvB (X + n + 1) := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ ≤ lvB (X + n + 1) * lvB (X + n + 1) :=
            mul_le_mul_of_nonneg_right (k1024_le_lvB h4) (Arithmetic.zero_le _)
        _ = lvB (X + ((n + 1 : ℕ) : V) + 1) := by
            rw [← lvB_succ]; push_cast; ring_nf

variable {k : ℕ} {arities : Fin k → ℕ}

/-- The constants of a fixed template derivation. -/
def tmA {σ : Sentence (setTemplateLanguage k arities)} (h : LTemplate.templTheory k arities ⊢ σ) : ℕ :=
  derMax h.get.toProof2

def tmB {σ : Sentence (setTemplateLanguage k arities)} (h : LTemplate.templTheory k arities ⊢ σ) : ℕ :=
  bufferBound h.get.toProof2 + height h.get.toProof2

def tmK {σ : Sentence (setTemplateLanguage k arities)} (h : LTemplate.templTheory k arities ⊢ σ) : ℕ :=
  height h.get.toProof2 + 4 * bufferBound h.get.toProof2

theorem four_le_cExpG (A B : ℕ) (u : V) : 4 ≤ cExpG A B u := by
  unfold cExpG
  refine le_trans ?_ (le_trans le_self_add le_self_add)
  exact le_trans (by norm_num : (4 : V) ≤ 10 * 1)
    (mul_le_mul_of_nonneg_left (le_add_self : (1 : V) ≤ (A : V) * (u + B + 1) + 1) (by norm_num))

/-- **Bounded `compiled`.** -/
theorem compiledLe (harity : ∀ i, arities i ≤ 3) {σ : Sentence (setTemplateLanguage k arities)}
    (h : LTemplate.templTheory k arities ⊢ σ)
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i)) {u : V} (hu : 2 ≤ u)
    (hK : ∀ i, (Ks i).val ≤ lvB u) :
    DLv 𝗭𝗙 (insert (translateFormula Ks (Rewriting.emb σ)).val ∅)
      (cExpG (tmA h) (tmB h) u + (tmK h : ℕ) + 1) := by
  have hc := sized_compileT_gen harity Ks hu hK h.get.toProof2
  rw [SizedShiftCancel.stg_add] at hc
  refine DerivableLe.mono hc (exp_monotone_le.mpr ?_)
  exact stg_lvB _ (four_le_cExpG _ _ _)

end LeanProofs.ZFCinPA.SizedLPlumbing
