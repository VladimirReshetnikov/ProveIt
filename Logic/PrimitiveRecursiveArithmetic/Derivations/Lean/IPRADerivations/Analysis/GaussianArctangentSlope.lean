import IPRADerivations.Analysis.GaussianArctangentExponentialPrefix

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

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.FiniteHausdorff (sum_mono)
open BaselQuadrature (Qb uq inst_Qb)
open GaussianArctangentCayleyValues (denominator denominator_positive)
open GaussianArctangentExponentialPrefix (source subst_source total subst_total)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def lowerSlope (j k M L : PTm n) : Fm PTm n :=
  le (k*fact L+two*M*total j M L) (two*M*total (j+k) M L)
def upperSlope (j k M L : PTm n) : Fm PTm n :=
  le (M*total (j+k) M L) (M*total j M L+k*fact L)
def slope (j k M L : PTm n) : Fm PTm n := lowerSlope j k M L ⋏ upperSlope j k M L
private def guardedSlope (j k M L : PTm n) : Fm PTm n := le (j+k) M ⟶ slope j k M L

@[simp] theorem subst_lowerSlope {m : ℕ} (σ : Fin n → PTm m) (j k M L : PTm n) :
    (lowerSlope j k M L).subst σ = lowerSlope (Syn.subst σ j) (Syn.subst σ k) (Syn.subst σ M) (Syn.subst σ L) := by
  simp [lowerSlope,Products.fact]
@[simp] theorem subst_upperSlope {m : ℕ} (σ : Fin n → PTm m) (j k M L : PTm n) :
    (upperSlope j k M L).subst σ = upperSlope (Syn.subst σ j) (Syn.subst σ k) (Syn.subst σ M) (Syn.subst σ L) := by
  simp [upperSlope,Products.fact]
@[simp] theorem subst_slope {m : ℕ} (σ : Fin n → PTm m) (j k M L : PTm n) :
    (slope j k M L).subst σ = slope (Syn.subst σ j) (Syn.subst σ k) (Syn.subst σ M) (Syn.subst σ L) := by
  simp [slope]
@[simp] private theorem subst_guardedSlope {m : ℕ} (σ : Fin n → PTm m) (j k M L : PTm n) :
    (guardedSlope j k M L).subst σ = guardedSlope (Syn.subst σ j) (Syn.subst σ k) (Syn.subst σ M) (Syn.subst σ L) := by
  simp [guardedSlope]

private theorem total_index_congr {i j : PTm n} (M L : PTm n) (h : Γ ⊢[PRAAx] i ≐ j) :
    Γ ⊢[PRAAx] total i M L ≐ total j M L :=
  congrAp2 (sumF Qb) h (.eqRefl _)

private theorem total_succ (j M L : PTm n) : Γ ⊢[PRAAx]
    total (succ j) M L ≐ total j M L+M*uq j M L :=
  (sum_succ Qb j (pairT M L)).eqTrans (congrAdd (.eqRefl _) (inst_Qb j M L))

private theorem denominator_bounds (j M : PTm n) (hj : Γ ⊢[PRAAx] lt j M) :
    Γ ⊢[PRAAx] le (M*M) (denominator M j) ⋏ le (denominator M j) (two*(M*M)) := by
  have hs : Γ ⊢[PRAAx] le (j*j) (M*M) := le_mul_mono (le_of_lt hj) (le_of_lt hj)
  exact .andI (le_add_right _ _)
    (le_congr (.eqRefl _) (by ipra_ring) (sum_mono (le_refl (M*M)) hs))

private theorem quotient_exact (j M L : PTm n) (hs : Γ ⊢[PRAAx] source M L)
    (hD : Γ ⊢[PRAAx] le (denominator M j) (two*(M*M))) :
    Γ ⊢[PRAAx] fact L ≐ denominator M j*uq j M L := by
  have hd := RationalIntegerNormalization.positive_form (denominator_positive M j hs.andE₁)
  have hl : Γ ⊢[PRAAx] le (denominator M j) L := le_trans hD hs.andE₂
  have hv := AnalyticNumberTheory.Primes.dvd_fact (le_congr hd (.eqRefl _) hl)
  exact DiophantineNumberTheory.Coprime.eq_of_dvd' hd (dvd_congr_left hd.eqSymm hv)

theorem row_slope (j M L : PTm n) (hs : Γ ⊢[PRAAx] source M L) (hj : Γ ⊢[PRAAx] lt j M) :
    Γ ⊢[PRAAx] le (fact L) (two*M*(M*uq j M L)) ⋏ le (M*(M*uq j M L)) (fact L) := by
  have bd := denominator_bounds j M hj
  have exactDiv := quotient_exact j M L hs bd.andE₂
  exact .andI
    (le_congr exactDiv.eqSymm (by ipra_ring) (le_mul_mono bd.andE₂ (le_refl (uq j M L))))
    (le_congr (by ipra_ring) exactDiv.eqSymm (le_mul_mono bd.andE₁ (le_refl (uq j M L))))

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
    refine PRA.qfInd _ ⟨le_QF _ _,⟨le_QF _ _,le_QF _ _⟩⟩ ?_ ?_
    · simp only [subst_guardedSlope,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (slope_zero _ _ _)
    · simp only [subst_guardedSlope,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
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
