import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith

namespace OAI

section

namespace Erdos3

theorem slicedSource_transfer_gain {gain ε Z projected fine coarse model : ℝ}
    (hgain : 0 < gain) (hε : ε ≤ gain / 32) (hZ : 1 / 2 ≤ Z)
    (hprojected : gain / 2 - ε ≤ projected)
    (hfine : Z * (projected - ε) ≤ fine)
    (hcoarse : fine - ε ≤ coarse) (hmodel : coarse - ε ≤ model) :
    gain / 8 ≤ model := by
  have hnonneg : 0 ≤ projected - ε := by linarith only [hgain, hε, hprojected]
  have hhalf := (mul_le_mul_of_nonneg_right hZ hnonneg).trans hfine
  linarith only [hgain, hε, hprojected, hhalf, hcoarse, hmodel]

theorem slicedSource_transfer_exp {p E Z projected fine coarse model : ℝ}
    (hE : p + 32 ≤ E) (hZ : 1 / 2 ≤ Z)
    (hprojected : Real.exp (-p) / 2 - Real.exp (-E) ≤ projected)
    (hfine : Z * (projected - Real.exp (-E)) ≤ fine)
    (hcoarse : fine - Real.exp (-E) ≤ coarse)
    (hmodel : coarse - Real.exp (-E) ≤ model) :
    Real.exp (-(p + 8)) ≤ model := by
  have heps : Real.exp (-E) ≤ Real.exp (-p) / 32 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 32)).mpr
    calc
      _ ≤ Real.exp (-E) * Real.exp 32 := mul_le_mul_of_nonneg_left
        (by linarith [Real.add_one_le_exp (32 : ℝ)] : (32 : ℝ) ≤ Real.exp 32) (Real.exp_pos _).le
      _ = Real.exp (-E + 32) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hE])
  have hsource := slicedSource_transfer_gain (Real.exp_pos (-p)) heps hZ hprojected hfine hcoarse hmodel
  apply le_trans _ hsource
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
  calc
    _ ≤ Real.exp (-(p + 8)) * Real.exp 8 := mul_le_mul_of_nonneg_left
      (by linarith [Real.add_one_le_exp (8 : ℝ)] : (8 : ℝ) ≤ Real.exp 8) (Real.exp_pos _).le
    _ = Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring

theorem slicedSource_transfer_combined_exp {p E Z model : ℝ}
    (hE : p + 32 ≤ E) (hZ : 1 / 2 ≤ Z)
    (hsource : Z * (Real.exp (-p) / 2 - Real.exp (-E) - Real.exp (-E)) -
      Real.exp (-E) - Real.exp (-E) ≤ model) :
    Real.exp (-(p + 8)) ≤ model := by
  exact slicedSource_transfer_exp hE hZ le_rfl le_rfl le_rfl hsource

theorem slicedSource_selected_gain_exp {p δ Cmodel Cspatial M S : ℝ}
    (hδ : Real.exp (-(p + 8)) ≤ δ) (hCmodel : 0 < Cmodel) (hCspatial : 0 < Cspatial)
    (hmodel : Cmodel ≤ Real.exp M) (hspatial : Cspatial ≤ Real.exp S) :
    Real.exp (-(p + 8 + M + S)) ≤ δ / (Cmodel * Cspatial) := by
  apply (le_div_iff₀ (mul_pos hCmodel hCspatial)).mpr
  calc
    _ ≤ Real.exp (-(p + 8 + M + S)) * (Real.exp M * Real.exp S) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hmodel hspatial hCspatial.le (Real.exp_nonneg _))
        (Real.exp_nonneg _)
    _ = Real.exp (-(p + 8)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ δ := hδ

end Erdos3

end

section

namespace Erdos3

theorem canonicalSlicedSource_transfer_exp
    {p gain Z Pproj target Ecoarse lossTarget model : ℝ}
    (hgain : Real.exp (-p) / 2 ≤ gain) (hZ : 1 / 2 ≤ Z)
    (hPproj : p + 32 ≤ Pproj) (htarget : p + 32 ≤ target)
    (hEcoarse : p + 32 ≤ Ecoarse) (hlossTarget : p + 32 ≤ lossTarget)
    (hsource : Z * (gain - Real.exp (-Pproj) - Real.exp (-target)) -
      Real.exp (-Ecoarse) - Real.exp (-lossTarget) ≤ model) :
    Real.exp (-(p + 8)) ≤ model := by
  have hZnonneg : 0 ≤ Z := le_trans (by norm_num) hZ
  have hproj : Real.exp (-Pproj) ≤ Real.exp (-(p + 32)) :=
    Real.exp_le_exp.mpr (neg_le_neg hPproj)
  have ht : Real.exp (-target) ≤ Real.exp (-(p + 32)) :=
    Real.exp_le_exp.mpr (neg_le_neg htarget)
  have hc : Real.exp (-Ecoarse) ≤ Real.exp (-(p + 32)) :=
    Real.exp_le_exp.mpr (neg_le_neg hEcoarse)
  have hl : Real.exp (-lossTarget) ≤ Real.exp (-(p + 32)) :=
    Real.exp_le_exp.mpr (neg_le_neg hlossTarget)
  apply slicedSource_transfer_combined_exp (E := p + 32) le_rfl hZ
  exact (sub_le_sub (sub_le_sub
    (mul_le_mul_of_nonneg_left (sub_le_sub (sub_le_sub hgain hproj) ht) hZnonneg)
    hc) hl).trans hsource

end Erdos3

end

end OAI
