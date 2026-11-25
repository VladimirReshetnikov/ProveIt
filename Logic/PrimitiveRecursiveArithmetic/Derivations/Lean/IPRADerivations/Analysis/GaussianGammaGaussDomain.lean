import IPRADerivations.Analysis.GaussianGammaEulerDenominatorGrouping
import IPRADerivations.Analysis.GaussianGammaReciprocalInverse

/-!
# Pole-free domains for Gauss multiplication

A single guard for the scaled argument (mz/B) supplies all shifted
arguments (z/B+r/m). The pole test at row (r) and integer (j)
reduces to the scaled test at (mj+r). The denominator of the
original margin is enlarged by (m).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaGaussDomain

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (bounded bounded_add bounded_scale bounded_mono normSq normSq_one scale oneCode)
open GaussianGammaEulerDenominatorGrouping (shiftedNumerator translated_shift)
open GaussianGammaEulerHeadLower (translated poleAt poleGuard pole_at)
open GaussianGammaReciprocalInverse (source)
open GaussianRationalHorner (positive_product)
open GaussianRootAlgebra (normSq_equal)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def scaledRadius (R m : PTm n) : PTm n := m*(R+two)

@[simp] theorem subst_scaledRadius {l : ℕ} (σ : Fin n → PTm l) (R m : PTm n) :
    Syn.subst σ (scaledRadius R m) = scaledRadius (Syn.subst σ R) (Syn.subst σ m) := by
  simp [scaledRadius,two,one]

theorem shifted_disk (z R B m r : PTm n) (hz : Γ ⊢[PRAAx] bounded z (R*B))
    (hr : Γ ⊢[PRAAx] le r m) : Γ ⊢[PRAAx] bounded (shiftedNumerator z B m r) ((R+one)*(B*m)) := by
  have unitDisk : Γ ⊢[PRAAx] bounded (oneCode : PTm n) one :=
    le_congr normSq_one.eqSymm (by ipra_ring) (le_refl one)
  have h := bounded_add (bounded_scale m hz) (bounded_scale (B*r) unitDisk)
  have comp := add_le_add_right (m*(R*B)) (le_mul_mono (le_refl B) hr)
  exact bounded_mono h (le_congr (by ipra_ring) (by ipra_ring) comp)

theorem scaled_index_bound (R m r j : PTm n) (hr : Γ ⊢[PRAAx] le r m)
    (hj : Γ ⊢[PRAAx] le j (two*(R+one))) : Γ ⊢[PRAAx] le (m*j+r) (two*scaledRadius R m) := by
  have cap : Γ ⊢[PRAAx] le (m*(two*(R+one))+m) (two*scaledRadius R m) := by
    exact le_congr (.eqRefl _) (by unfold scaledRadius; ipra_ring)
      (le_add_right (m*(two*(R+one))+m) m)
  have first := add_le_add_right r (le_mul_mono (le_refl m) hj)
  have next := le_congr (add_comm _ _) (add_comm _ _) (add_le_add_right (m*(two*(R+one))) hr)
  exact le_trans first (le_trans next cap)

theorem shifted_pole_at (z R B m r a d j : PTm n)
    (hr : Γ ⊢[PRAAx] le r m) (hj : Γ ⊢[PRAAx] le j (two*(R+one)))
    (h : Γ ⊢[PRAAx] poleGuard (scale m z) B a d (two*scaledRadius R m)) :
    Γ ⊢[PRAAx] poleAt (shiftedNumerator z B m r) (B*m) a (d*m) j := by
  have pr := pole_at _ _ _ _ _ _ h (scaled_index_bound R m r j hr hj)
  have equalNorm := normSq_equal (translated_shift (Γ := Γ) z B m r j)
  change Γ ⊢[PRAAx] le (a*(B*m)*(a*(B*m)))
    (d*m*(d*m)*normSq (translated (shiftedNumerator z B m r) (B*m) j))
  have bigger := le_mul_mono (le_refl (m*m)) pr
  exact le_congr (by ipra_ring)
    ((congrMul (.eqRefl _) (congrMul (.eqRefl _) equalNorm.eqSymm)).eqTrans (by ipra_ring)) bigger

theorem shifted_pole_guard (z R B m r a d : PTm n) (hr : Γ ⊢[PRAAx] le r m)
    (h : Γ ⊢[PRAAx] poleGuard (scale m z) B a d (two*scaledRadius R m)) :
    Γ ⊢[PRAAx] poleGuard (shiftedNumerator z B m r) (B*m) a (d*m) (two*(R+one)) := by
  refine .allI (.impI ?_)
  let sh (t : PTm n) := Syn.shift t
  let Δ := le (var 0) (two*(sh R+one)) :: Γ.map Fm.shift
  have hr' : Δ ⊢[PRAAx] le (sh r) (sh m) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hr.shift.wk
  have hs : Δ ⊢[PRAAx] poleGuard (scale (sh m) (sh z)) (sh B) (sh a) (sh d)
      (two*scaledRadius (sh R) (sh m)) := by simpa [Δ,sh,Fm.shift,Syn.shift,two,one] using h.shift.wk
  have r := shifted_pole_at (sh z) (sh R) (sh B) (sh m) (sh r) (sh a) (sh d) (var 0)
    hr' (Prf.hyp0 : Δ ⊢[PRAAx] le (var 0) (two*(sh R+one))) hs
  simpa [poleGuard,Syn.shift,shiftedNumerator,sh,Δ,two,one] using r

theorem shifted_source (z R B m r a d : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hr : Γ ⊢[PRAAx] le r m)
    (hz : Γ ⊢[PRAAx] bounded z (R*B)) (hs : Γ ⊢[PRAAx] source (scale m z) (scaledRadius R m) B a d) :
    Γ ⊢[PRAAx] source (shiftedNumerator z B m r) (R+one) (B*m) a (d*m) :=
  .andI (.andI (le_add_left _ _) (.andI (positive_product _ _ hs.andE₁.andE₂.andE₁ hm)
    (shifted_disk z R B m r hz hr))) (.andI hs.andE₂.andE₁
      (.andI (positive_product _ _ hs.andE₂.andE₂.andE₁ hm)
        (shifted_pole_guard z R B m r a d hr hs.andE₂.andE₂.andE₂)))

theorem actual_Gauss_shifted_Gamma_source_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 3) ⟶ le (var 4) (var 3) ⟶ bounded (var 0) (var 1*var 2) ⟶
      source (scale (var 3) (var 0)) (scaledRadius (var 1) (var 3)) (var 2) (var 5) (var 6) ⟶
      source (shiftedNumerator (var 0) (var 2) (var 3) (var 4)) (var 1+one) (var 2*var 3) (var 5) (var 6*var 3)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI
    (shifted_source _ _ _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianGammaGaussDomain
