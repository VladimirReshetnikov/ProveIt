import IPRADerivations.Analysis.Trigonometry.Arctangent.PartialSums.GaussianArctangentExponentialPrefix

/-!
# Finite slope of the native partial arctangent quadrature

For any two indices on the same grid the accumulated imaginary
coordinate of the phase (2i\arctan(t)) changes by at least the
index distance divided by the mesh size and at most twice that.
Both inequalities hold after clearing the actual shared factorial
denominator of the original observations.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentSlope

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.FiniteHausdorff (sum_mono)
open BaselQuadrature (Qb uq)
open GaussianArctangentCayleyValues (denominator)
open GaussianArctangentExponentialPrefix (source subst_source total subst_total total_succ denominator_upper quotient_exact)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def lowerSlope (j k M L : PTm n) : Fm PTm n :=
  le (k*fact L+two*M*total j M L) (two*M*total (j+k) M L)
def upperSlope (j k M L : PTm n) : Fm PTm n :=
  le (M*total (j+k) M L) (M*total j M L+k*fact L)
def slope (j k M L : PTm n) : Fm PTm n := lowerSlope j k M L ⋏ upperSlope j k M L
private def guardedSlope (j k M L : PTm n) : Fm PTm n := le (j+k) M ⟶ slope j k M L

ipra_subst lowerSlope [Products.fact]
ipra_subst upperSlope [Products.fact]
ipra_subst slope
@[simp] private theorem subst_guardedSlope {m : ℕ} (σ : Fin n → PTm m) (j k M L : PTm n) :
    (guardedSlope j k M L).subst σ = guardedSlope (Syn.subst σ j) (Syn.subst σ k) (Syn.subst σ M) (Syn.subst σ L) := by
  simp [guardedSlope]

private theorem total_index_congr {i j : PTm n} (M L : PTm n) (h : Γ ⊢[PRAAx] i ≐ j) :
    Γ ⊢[PRAAx] total i M L ≐ total j M L :=
  congrAp2 (sumF Qb) h (.eqRefl _)

theorem row_slope (j M L : PTm n) (hs : Γ ⊢[PRAAx] source M L) (hj : Γ ⊢[PRAAx] lt j M) :
    Γ ⊢[PRAAx] le (fact L) (two*M*(M*uq j M L)) ⋏ le (M*(M*uq j M L)) (fact L) := by
  have upper := denominator_upper j M hj
  have lower : Γ ⊢[PRAAx] le (M*M) (denominator M j) := le_add_right _ _
  have exactDiv := quotient_exact j M L hs hj
  exact .andI
    (le_congr exactDiv.eqSymm (by ipra_ring) (le_mul_mono upper (le_refl (uq j M L))))
    (le_congr (by ipra_ring) exactDiv.eqSymm (le_mul_mono lower (le_refl (uq j M L))))

private theorem slope_zero (j M L : PTm n) : Γ ⊢[PRAAx] slope j zero M L := by
  have e := total_index_congr (Γ := Γ) M L (add_zero j)
  exact .andI
    (le_congr (by ipra_ring) (congrMul (.eqRefl (two*M)) e.eqSymm) (le_refl _))
    (le_congr (congrMul (.eqRefl M) e.eqSymm) (by ipra_ring) (le_refl _))

private theorem slope_step (j k M L : PTm n) (hs : Γ ⊢[PRAAx] source M L)
    (hend : Γ ⊢[PRAAx] le (j+succ k) M) (prev : Γ ⊢[PRAAx] slope j k M L) :
    Γ ⊢[PRAAx] slope j (succ k) M L := by
  have hi : Γ ⊢[PRAAx] lt (j+k) M := le_congr (add_succ j k) (.eqRefl _) hend
  have term := row_slope (j+k) M L hs hi
  have hnext := (total_index_congr (Γ := Γ) M L (add_succ j k)).eqTrans (total_succ (j+k) M L)
  have e := natEq hnext
  have hl := sum_mono prev.andE₁ term.andE₁
  have hu := sum_mono prev.andE₂ term.andE₂
  exact .andI
    (le_congr (by ipra_ring) (by
      apply deriveNat
      ipra_simps
      rw [e]
      ring) hl)
    (le_congr (by
      apply deriveNat
      ipra_simps
      rw [e]
      ring) (by ipra_ring) hu)

theorem finite_slope (j k M L : PTm n) (hs : Γ ⊢[PRAAx] source M L)
    (hend : Γ ⊢[PRAAx] le (j+k) M) : Γ ⊢[PRAAx] slope j k M L := by
  have all : Γ ⊢[PRAAx] .all (guardedSlope (Syn.shift j) (var 0) (Syn.shift M) (Syn.shift L)) := by
    ipra_qfind (⟨le_QF _ _,⟨le_QF _ _,le_QF _ _⟩⟩) [subst_guardedSlope]
    · exact .impI (slope_zero _ _ _)
    · refine .impI ?_
      let a := Syn.shift j
      let m := Syn.shift M
      let l := Syn.shift L
      let i : PTm (n+1) := var 0
      let Δ := le (a+succ i) m :: guardedSlope a i m l :: Γ.map Fm.shift
      have hsrc : Γ.map Fm.shift ⊢[PRAAx] source m l := by
        simpa only [Fm.shift,subst_source,Syn.shift,m,l] using hs.shift
      have hnext : Δ ⊢[PRAAx] le (a+succ i) m := Prf.hyp0
      have current : Δ ⊢[PRAAx] le (a+i) m :=
        le_of_lt (le_congr (add_succ a i) (.eqRefl _) hnext)
      exact slope_step a i m l hsrc.wk.wk hnext (.impE Prf.hyp1 current)
  have h : Γ ⊢[PRAAx] guardedSlope j k M L := by
    simpa only [subst_guardedSlope,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE h hend

theorem actual_finite_arctangent_slope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 2) (var 3) ⟶ le (var 0+var 1) (var 2) ⟶ slope (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (finite_slope _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianArctangentSlope
