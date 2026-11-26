import IPRADerivations.Analysis.Integration.GaussianCompactIntervalRescaling
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactAdditivity
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerCompactQuadrature

/-!
# Inverse dilation of the original Euler cutoff interval

For the rational scale c/d, the inverse image of the original interval
(a,C,E) uses the unscaled grid tuple (d*a,d*C,c*E). Applying the actual
rational dilation gives the original tuple multiplied by c*d. The
original evaluator is called at that new time encoding, and the
rescaling theorem pays for the true observation errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositiveScalingCutoffGeometry

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactRiemannName (quadrature)
open GaussianEulerCompactAdditivity (intervalSource compact_input)
open GaussianEulerCompactModulus (lipschitz)
open GaussianEulerIntegrandName (evaluatorF fixedData)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (unit)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaCompactQuadratureBoundary (width)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B a C E T c d : PTm n) : Fm PTm n :=
  intervalSource z R B a C E T ⋏ (le one c ⋏ le one d)

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B a C E T c d : PTm n) :
    (source z R B a C E T c d).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ c) (Syn.subst σ d) := by simp [source]

theorem pullback_interval (z R B a C E T c d : PTm n) (hs : Γ ⊢[PRAAx] source z R B a C E T c d) :
    Γ ⊢[PRAAx] intervalSource z R B (d*a) (d*C) (c*E) (d*T) := by
  have old := hs.andE₁.andE₁
  have hc := hs.andE₂.andE₁
  have hd := hs.andE₂.andE₂
  have endOld := mul_le_mul_right d hs.andE₁.andE₂.andE₂
  have endNew := mul_le_mul_right (E*(d*T)) hc
  have unscaled : Γ ⊢[PRAAx] le (d*a+d*C) (E*(d*T)) := le_congr (by ipra_ring) (by ipra_ring) endOld
  have right : Γ ⊢[PRAAx] le (d*a+d*C) ((c*E)*(d*T)) :=
    le_trans unscaled (le_congr (by ipra_ring) (by ipra_ring) endNew)
  exact .andI (.andI old.andE₁ (.andI (positive_product _ _ hc old.andE₂.andE₁) old.andE₂.andE₂))
    (.andI (positive_product _ _ hd hs.andE₁.andE₂.andE₁) right)

theorem cutoff_interval (k A z R B : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianGammaEulerCompactQuadrature.source z R B) : Γ ⊢[PRAAx]
    intervalSource z R B one (width k A R) (etaDen k A R) (top k A R) := by
  have old := GaussianGammaEulerCompactQuadrature.original_input z R B k A hs
  exact .andI old.andE₁ (.andI (le_refl one) old.andE₂)

theorem scaled_quadrature_code (F : PR 3) (p N a C E x c d : PTm n) : Γ ⊢[PRAAx]
    quadrature F p N ((c*d)*a) ((c*d)*C) ((c*d)*E) x ≐
      quadrature F p N (c*(d*a)) (c*(d*C)) (d*(c*E)) x := by
  have aEq : Γ ⊢[PRAAx] (c*d)*a ≐ c*(d*a) := by ipra_ring
  have cEq : Γ ⊢[PRAAx] (c*d)*C ≐ c*(d*C) := by ipra_ring
  have eEq : Γ ⊢[PRAAx] (c*d)*E ≐ d*(c*E) := by ipra_ring
  have left : Γ ⊢[PRAAx] quadrature F p N ((c*d)*a) ((c*d)*C) ((c*d)*E) x ≐
      quadrature F p N (c*(d*a)) ((c*d)*C) ((c*d)*E) x := by
    simpa only [GaussianCompactRiemannName.subst_quadrature,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (quadrature F (Syn.shift p) (Syn.shift N) (var 0) (Syn.shift ((c*d)*C))
        (Syn.shift ((c*d)*E)) (Syn.shift x)) aEq
  have mid : Γ ⊢[PRAAx] quadrature F p N (c*(d*a)) ((c*d)*C) ((c*d)*E) x ≐
      quadrature F p N (c*(d*a)) (c*(d*C)) ((c*d)*E) x := by
    simpa only [GaussianCompactRiemannName.subst_quadrature,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (quadrature F (Syn.shift p) (Syn.shift N) (Syn.shift (c*(d*a))) (var 0)
        (Syn.shift ((c*d)*E)) (Syn.shift x)) cEq
  have last : Γ ⊢[PRAAx] quadrature F p N (c*(d*a)) (c*(d*C)) ((c*d)*E) x ≐
      quadrature F p N (c*(d*a)) (c*(d*C)) (d*(c*E)) x := by
    simpa only [GaussianCompactRiemannName.subst_quadrature,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (quadrature F (Syn.shift p) (Syn.shift N) (Syn.shift (c*(d*a))) (Syn.shift (c*(d*C)))
        (var 0) (Syn.shift x)) eEq
  exact left.eqTrans (mid.eqTrans last)

theorem original_scaled_grid_comparison (p N z R B a C E T c d : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C E T c d) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (quadrature evaluatorF p N a C E (fixedData z B))
      (quadrature evaluatorF p N (c*(d*a)) (c*(d*C)) (d*(c*E)) (fixedData z B))
      (C*two) (E*unit p) := by
  have lift := positive_product _ _ hs.andE₂.andE₁ hs.andE₂.andE₂
  have compare := GaussianCompactIntervalRescaling.quadrature_distance evaluatorF p N (c*d) a C E (lipschitz R E T) T
    (fixedData z B) (.andI lift (compact_input z R B a C E T hs.andE₁)) hN
  exact distance_congr (.eqRefl _) (scaled_quadrature_code evaluatorF p N a C E (fixedData z B) c d)
    (.eqRefl _) (.eqRefl _) compare

theorem actual_Euler_positive_scale_pullback_interval_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      intervalSource (var 0) (var 1) (var 2) (var 8*var 3) (var 8*var 4) (var 7*var 5) (var 8*var 6)) :=
  closeUniv 9 (.impI (pullback_interval _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_Euler_positive_scale_original_grid_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    ((source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⋏ le one (var 1)) ⟶
      distanceBounded (quadrature evaluatorF (var 0) (var 1) (var 5) (var 6) (var 7) (fixedData (var 2) (var 4)))
        (quadrature evaluatorF (var 0) (var 1) (var 9*(var 10*var 5)) (var 9*(var 10*var 6)) (var 10*(var 9*var 7))
          (fixedData (var 2) (var 4))) (var 6*two) (var 7*unit (var 0))) :=
  closeUniv 11 (.impI (original_scaled_grid_comparison _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerPositiveScalingCutoffGeometry
