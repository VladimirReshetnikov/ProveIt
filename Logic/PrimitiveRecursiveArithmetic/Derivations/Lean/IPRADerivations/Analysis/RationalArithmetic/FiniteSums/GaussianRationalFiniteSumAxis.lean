import IPRADerivations.Analysis.RationalArithmetic.Embeddings.RationalGaussianEmbedding
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalFiniteSum

/-! A finite sum of Gaussian rational rows with zero imaginary part is real. -/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalFiniteSumAxis

open_ipra
open GaussianRationalFiniteSum (sum subst_sum)
open RationalGaussianEmbedding (axis subst_axis axis_add axis_congr axis_zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rowAxes (t : PTm 2) (x : PTm n) : Fm PTm n := .all (axis (inst2 t (var 0) (Syn.shift x)))

@[simp] theorem subst_rowAxes {m : ℕ} (σ : Fin n → PTm m) (t : PTm 2) (x : PTm n) :
    (rowAxes t x).subst σ = rowAxes t (Syn.subst σ x) := by simp [rowAxes,Syn.subst_shift,Syn.shift_subst]

theorem row_axis (t : PTm 2) (x i : PTm n) (h : Γ ⊢[PRAAx] rowAxes t x) : Γ ⊢[PRAAx] axis (inst2 t i x) := by
  ipra_simpa_inst [rowAxes,subst_axis,subst_inst2] using h.allE i

theorem sum_axis (t : PTm 2) (N x : PTm n) (h : Γ ⊢[PRAAx] rowAxes t x) : Γ ⊢[PRAAx] axis (sum t N x) := by
  let y := Syn.shift x
  let Δ := Γ.map Fm.shift
  let motive : Fm PTm (n+1) := axis (sum t (var 0) y)
  have rows : Δ ⊢[PRAAx] rowAxes t y := by simpa only [Δ,y,Fm.shift,Syn.shift,subst_rowAxes] using h.shift
  have all : Γ ⊢[PRAAx] .all motive := by
    ipra_qfind (by simp [motive,axis,RationalArgmin.rationalEq,Fm.QF]) [motive, y, subst_axis, subst_sum]
    · exact
        (axis_congr (GaussianRationalFiniteSum.sum_zero (Γ := Γ) t x).eqSymm axis_zero)
    · exact axis_congr (GaussianRationalFiniteSum.sum_succ t (var 0) y).eqSymm
        (axis_add _ _ Prf.hyp0 (row_axis t y (var 0) rows.wk))
  ipra_simpa_inst [motive,y,subst_axis,subst_sum] using all.allE N

end LeanProofs.IPRA.Analysis.GaussianRationalFiniteSumAxis
