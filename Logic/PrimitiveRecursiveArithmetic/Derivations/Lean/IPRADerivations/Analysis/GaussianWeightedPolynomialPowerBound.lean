import IPRADerivations.Analysis.GaussianFiniteExponentialWeightedNorm

/-!
# Rational weighted coefficient bounds for the actual polynomial powers

The original fixed-cap polynomial power fold is bounded by any supplied
nonnegative rational bound on its original input coefficient norm. The
proof is genuine guarded QF induction on that SAME fold; all numerator,
denominator, degree and cap parameters remain internal.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianWeightedPolynomialPowerBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalPolynomialPowers (powerPrefix prefix_length prefix_zero prefix_succ)
open GaussianRationalPolynomialDilation (weightedNorm)
open GaussianFiniteExponentialWeightedNorm (weighted_congr weighted_nonnegative multiply_bounds singleton_weighted_norm)
open RationalArgmin (rationalLE)
open GaussianEuclideanDistanceName (fraction)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def powerLaw (C N K t A D j : PTm n) : Fm PTm n := le j K ⟶
  rationalLE (weightedNorm (powerPrefix C N K j) (j*N) t) (RationalNonnegativePowers.power A D j)
@[simp] theorem subst_powerLaw {m : ℕ} (σ : Fin n → PTm m) (C N K t A D j : PTm n) :
    (powerLaw C N K t A D j).subst σ = powerLaw (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ K)
      (Syn.subst σ t) (Syn.subst σ A) (Syn.subst σ D) (Syn.subst σ j) := by simp [powerLaw]

theorem power_zero (C N K t A D : PTm n) : Γ ⊢[PRAAx] powerLaw C N K t A D zero := by
  refine .impI ?_
  have actual := (weighted_congr (Γ := le zero K :: Γ) (prefix_zero C N K) (zero_mul N) (.eqRefl _)).eqTrans
    (singleton_weighted_norm t)
  exact RationalArgmin.rationalLE_congr actual.eqSymm (RationalNonnegativePowers.power_zero A D).eqSymm (RationalArgmin.reflexive _)

theorem power_step (C N K t A D j : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hD : Γ ⊢[PRAAx] le one D) (hNorm : Γ ⊢[PRAAx] rationalLE (weightedNorm C N t) (fraction A D))
    (hj : Γ ⊢[PRAAx] lt j K)
    (ih : Γ ⊢[PRAAx] rationalLE (weightedNorm (powerPrefix C N K j) (j*N) t) (RationalNonnegativePowers.power A D j)) : Γ ⊢[PRAAx]
    rationalLE (weightedNorm (powerPrefix C N K (succ j)) (succ j*N) t) (RationalNonnegativePowers.power A D (succ j)) := by
  have actual := GaussianRationalPolynomialDilation.weighted_product_bound (powerPrefix C N K j) C (j*N) N t (prefix_length _ _ _ _) hC
  have nonnegative := GaussianRationalL1.nonnegative_of_representation _ _ _
    (RationalNonnegativePowers.denominator_positive D j hD) (RationalNonnegativePowers.power_represents A D j hD)
  have multiplied := multiply_bounds _ _ _ _ (weighted_nonnegative C N t) nonnegative ih hNorm
  exact RationalArgmin.rationalLE_congr (weighted_congr (prefix_succ C N K j hj).eqSymm (by ipra_ring) (.eqRefl _))
    (RationalNonnegativePowers.power_succ A D j hD).eqSymm (RationalArgmin.transitive actual multiplied)

/-- The actual stored fixed-cap powers, with a genuine rational bound. -/
theorem power_bound (C N K t A D j : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hD : Γ ⊢[PRAAx] le one D) (hNorm : Γ ⊢[PRAAx] rationalLE (weightedNorm C N t) (fraction A D))
    (hj : Γ ⊢[PRAAx] le j K) : Γ ⊢[PRAAx]
    rationalLE (weightedNorm (powerPrefix C N K j) (j*N) t) (RationalNonnegativePowers.power A D j) := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hC.shift
  have ds : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift D) := by simpa [Fm.shift,Syn.shift] using hD.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] rationalLE (weightedNorm (Syn.shift C) (Syn.shift N) (Syn.shift t))
      (fraction (Syn.shift A) (Syn.shift D)) := by simpa [Fm.shift,Syn.shift] using hNorm.shift
  have all : Γ ⊢[PRAAx] .all (powerLaw (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift t) (Syn.shift A) (Syn.shift D) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [subst_powerLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact power_zero _ _ _ _ _ _
    · simp only [subst_powerLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact .impI (power_step _ _ _ _ _ _ _ cs.wk.wk ds.wk.wk ns.wk.wk Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)))
  have rule : Γ ⊢[PRAAx] powerLaw C N K t A D j := by
    simpa only [subst_powerLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE rule hj

theorem original_polynomial_powers_rational_weighted_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((length (var 0) ≐ succ (var 1) ⋏ le one (var 5) ⋏
      rationalLE (weightedNorm (var 0) (var 1) (var 3)) (fraction (var 4) (var 5)) ⋏ le (var 6) (var 2)) ⟶
      rationalLE (weightedNorm (powerPrefix (var 0) (var 1) (var 2) (var 6)) (var 6*var 1) (var 3))
        (RationalNonnegativePowers.power (var 4) (var 5) (var 6))) :=
  closeUniv 7 (.impI (power_bound _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianWeightedPolynomialPowerBound
