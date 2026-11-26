import IPRADerivations.Analysis.Trigonometry.GaussianSineProductT4Finite
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaReflectionSineTransfer
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDiagonalRate

/-!
# Cofinal passage from finite sine products to Gamma reflection

A common cutoff dominates the finite sine-product comparison and the
literal product tail. At that cutoff, a finite approximation to the
original sinc yields its cross-equivalence with the literal product
and the cleared reflection identity of the original Gamma programs.
-/

set_option autoImplicit false
set_option maxHeartbeats 270000

namespace LeanProofs.IPRA.Analysis.GaussianSineProductT7

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaEulerReflectionHead (sineProduct)
open GaussianGammaReflectionProduct (complementarySource complementaryData gammaPairF)
open GaussianGammaReflectionSineTransfer
  (argumentF argumentData argumentRadius sineAtPiF sineAtPiData productIdentification)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianNamedDiagonalRate (diagonalRate cross_of_diagonal_rate)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (distanceBounded)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "T" => GaussianNamedSinc.nameF argumentF
local notation "S" => GaussianSineProductName.nameF
local notation "P" => GaussianGammaHalfPiName.nameF

def cutoff (R p : PTm n) : PTm n :=
  (GaussianSineProductT4Budget.cutoff R p+GaussianSineProductName.cutoff R p)+one

theorem cutoff_positive (R p : PTm n) : Γ ⊢[PRAAx] le one (cutoff R p) := le_add_left _ _

theorem t4_cutoff_le (R p : PTm n) : Γ ⊢[PRAAx] le (GaussianSineProductT4Budget.cutoff R p) (cutoff R p) :=
  le_trans (le_add_right _ _) (le_add_right _ _)

theorem tail_cutoff_le (R p : PTm n) : Γ ⊢[PRAAx] le (GaussianSineProductName.cutoff R p) (cutoff R p) :=
  le_trans (le_add_left _ _) (le_add_right _ _)

@[simp] theorem subst_cutoff {m : ℕ} (σ : Fin n → PTm m) (R p : PTm n) :
    Syn.subst σ (cutoff R p) = cutoff (Syn.subst σ R) (Syn.subst σ p) := by simp [cutoff,one]

def sincData (z B x : PTm n) : PTm n := GaussianNamedSinc.data argumentF (argumentRadius z B x) (argumentData z B x)

@[simp] theorem subst_sincData {m : ℕ} (σ : Fin n → PTm m) (z B x : PTm n) :
    Syn.subst σ (sincData z B x) = sincData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ x) :=
  by simp [sincData,argumentRadius,argumentData]

theorem sinc_regular (z B x : PTm n) : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN T (sincData z B x) := by
  have hr := GaussianGammaHalfPiName.name_regular (Γ := Γ) x
  have hz := GaussianGammaCanonicalExponent.constant_regular (Γ := Γ) (ofGaussian z B)
  have h := multiply_fast P GaussianGammaCanonicalExponent.constantF x (ofGaussian z B) hr hz
  exact GaussianNamedSinc.name_regular argumentF (argumentRadius z B x) (argumentData z B x)
    (GaussianGammaFiniteApproximantName.exponential_input argumentF (argumentData z B x) h)

def prefixAt (z R B x A p : PTm n) : Fm PTm n :=
  distanceBounded (ap2 T p (sincData z B x)) (sineProduct z B (cutoff R p)) A (unit p)

@[simp] theorem subst_prefixAt {m : ℕ} (σ : Fin n → PTm m) (z R B x A p : PTm n) :
    (prefixAt z R B x A p).subst σ =
      prefixAt (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ x) (Syn.subst σ A) (Syn.subst σ p) :=
  by simp [prefixAt,sineProduct]

def prefixRate (z R B x A : PTm n) : Fm PTm n :=
  .all (prefixAt (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift x) (Syn.shift A) (var 0))

@[simp] theorem subst_prefixRate {m : ℕ} (σ : Fin n → PTm m) (z R B x A : PTm n) :
    (prefixRate z R B x A).subst σ =
      prefixRate (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ x) (Syn.subst σ A) :=
  by simp [prefixRate,Syn.shift_subst,Syn.subst_shift]

theorem rate_at (z R B x A p : PTm n) (h : Γ ⊢[PRAAx] prefixRate z R B x A) :
    Γ ⊢[PRAAx] prefixAt z R B x A p := by
  simpa only [prefixRate,subst_prefixAt,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE p

theorem prefix_at (F : PR 2) (z R B x p q y A : PTm n)
    (hf : Γ ⊢[PRAAx] crossEquivalent T F (sincData z B x) y)
    (hpq : Γ ⊢[PRAAx] le p q)
    (ht : Γ ⊢[PRAAx] distanceBounded (ap2 F q y) (sineProduct z B (cutoff R p)) A (unit p)) :
    Γ ⊢[PRAAx] prefixAt z R B x (two+A) p := by
  let U := unit p
  let V := unit q
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have hUV : Γ ⊢[PRAAx] le U V := GaussianExponentialReference.unit_monotone hpq
  have compare : Γ ⊢[PRAAx] le ((U+V)*U) (two*(U*V)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add₂ (le_refl (U*V)) (le_mul_mono (le_refl U) hUV))
  have h := distance_radius_mono _ _ _ _ two U (positive_product _ _ hp hq) hp compare (cross_at _ _ _ _ p q hf)
  exact distance_triangle_same _ _ _ _ _ _ hp h ht

theorem prefix_of_finite_t4_at (F : PR 2) (row : PTm 2) (z R B x p y d s A : PTm n)
    (hf : Γ ⊢[PRAAx] crossEquivalent T F (sincData z B x) y)
    (ht : Γ ⊢[PRAAx] GaussianSineProductT4Finite.source row d s z R B (cutoff R p))
    (hb : Γ ⊢[PRAAx] distanceBounded (ap2 F p y)
      (GaussianSineProductT4Finite.value row d s R (cutoff R p)) A (unit p)) :
    Γ ⊢[PRAAx] prefixAt z R B x (two+(A+one)) p :=
  prefix_at F z R B x p p y (A+one) hf (le_refl p)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) hb
      (GaussianSineProductT4Finite.precision_at row d s z R B (cutoff R p) p ht (t4_cutoff_le R p)))

theorem diagonal_at (z R B x A p : PTm n) (hs : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B)
    (hA : Γ ⊢[PRAAx] prefixAt z R B x A p) :
    Γ ⊢[PRAAx] distanceBounded (ap2 S p (GaussianSineProductName.data z R B)) (ap2 T p (sincData z B x))
      (one+A) (unit p) := by
  let U := unit p
  have hp := unit_positive (Γ := Γ) p
  have tail := GaussianSineProductName.cofinal_error z R B p (cutoff R p) hs.andE₂.andE₁ hs.andE₂.andE₂ (tail_cutoff_le R p)
  exact distance_triangle_same _ _ _ _ _ _ hp
    (distance_symmetric _ _ _ _ hp tail) (distance_symmetric _ _ A U hp hA)

theorem product_identification (z R B x A : PTm n) (hs : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B)
    (hA : Γ ⊢[PRAAx] prefixRate z R B x A) :
    Γ ⊢[PRAAx] productIdentification z R B x := by
  apply cross_of_diagonal_rate S T (GaussianSineProductName.data z R B) (sincData z B x) (one+A)
    (GaussianSineProductName.name_regular z R B hs.andE₂.andE₁ hs.andE₂.andE₂) (sinc_regular z B x)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (a : PTm n) := Syn.shift a
  have hsrc : Δ ⊢[PRAAx] GaussianGammaCanonicalExponent.source (sh z) (sh R) (sh B) := by
    simpa [Fm.shift,Syn.shift,Δ,sh] using hs.shift
  have hr : Δ ⊢[PRAAx] prefixRate (sh z) (sh R) (sh B) (sh x) (sh A) := by
    simpa only [Fm.shift,Syn.shift,subst_prefixRate,Δ,sh] using hA.shift
  simpa only [diagonalRate,Syn.shift,subst_sincData,GaussianSineProductName.data,subst_pairT,
    PTm.subst_add,one,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Δ,sh] using
    diagonal_at (sh z) (sh R) (sh B) (sh x) (sh A) (var 0) hsrc (rate_at _ _ _ _ _ _ hr)

theorem cleared_reflection (z R B a d e f x A : PTm n) (hs : Γ ⊢[PRAAx] complementarySource z R B a d e f)
    (hA : Γ ⊢[PRAAx] prefixRate z R B x A) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF sineAtPiF gammaPairF) P
      (multiplyData sineAtPiF gammaPairF (sineAtPiData z B x) (complementaryData z R B d f)) x :=
  GaussianGammaReflectionSineTransfer.cleared_reflection z R B a d e f x hs
    (product_identification z R B x A hs.andE₁.andE₁ hA)

theorem actual_sine_product_identification_of_prefix_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (GaussianGammaCanonicalExponent.source (var 0) (var 1) (var 2) ⟶
        prefixRate (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ productIdentification (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 5 (.impI (.impI (product_identification _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_cleared_Gamma_reflection_of_prefix_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (complementarySource (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
        prefixRate (var 0) (var 1) (var 2) (var 7) (var 8) ⟶
        crossEquivalent (multiplyF sineAtPiF gammaPairF) P
          (multiplyData sineAtPiF gammaPairF (sineAtPiData (var 0) (var 2) (var 7))
            (complementaryData (var 0) (var 1) (var 2) (var 4) (var 6))) (var 7)) :=
  closeUniv 9 (.impI (.impI (cleared_reflection _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianSineProductT7
