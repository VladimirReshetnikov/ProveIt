import IPRADerivations.Analysis.Trigonometry.GaussianSineProductName
import IPRADerivations.Analysis.Names.Rates.GaussianRationalLowerPerturbation

/-!
# Exact lower bound for the finite sine-product head

The pole separation at the integers between −N and N supplies the
factor estimate δ²/k² and the prefix estimate δ^(2N)/(N!)².
The exact factor pairing is the same one used in the finite
Euler reflection proof.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianSineProductHeadLower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaEulerReflectionHead (sineProduct squareFactor paired_factor body)
open GaussianGammaEulerHeadLower (poleAt poleGuard pole_at factor_lower translated_zero)
open GaussianRationalLowerBounds (lower lower_congr lower_from_representation product_lower)
open GaussianRationalLowerPerturbation (lower_near_unit)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalFiniteProduct (product_zero)
open GaussianRationalReciprocal (qone)
open GaussianRationalHorner (positive_product ofGaussian ofGaussian_represents)
open GaussianSineProductName (sine_product_succ)
open GaussianFactorBudget (power_positive)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "gneg" => ComplexLogarithmRemainder.neg

def numerator (a N : PTm n) : PTm n := pw (a*a) N
def denominator (d N : PTm n) : PTm n := pw (d*d) N*(fact N*fact N)

def prefixBound (z B a d N : PTm n) : Fm PTm n :=
  lower (sineProduct z B N) (numerator a N) (denominator d N)

def input (z B a d N : PTm n) : Fm PTm n :=
  poleGuard z B a d N ⋏ poleGuard (gneg z) B a d N

@[simp] theorem subst_prefixBound {l : ℕ} (σ : Fin n → PTm l) (z B a d N : PTm n) :
    (prefixBound z B a d N).subst σ = prefixBound (Syn.subst σ z) (Syn.subst σ B)
      (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ N) := by
  simp [prefixBound,numerator,denominator,sineProduct,fact]

@[simp] theorem subst_input {l : ℕ} (σ : Fin n → PTm l) (z B a d N : PTm n) :
    (input z B a d N).subst σ = input (Syn.subst σ z) (Syn.subst σ B)
      (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ N) := by
  simp [input]

theorem lower_one : Γ ⊢[PRAAx] lower (qone : PTm n) one one :=
  lower_congr (.eqRefl _) (monus_zero one) (.eqRefl _)
    (lower_near_unit qone zero one (le_refl _) (zero_le one) (distance_refl_zero qone one (le_refl _)))

theorem denominator_positive (d N : PTm n) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] le one (denominator d N) := by
  have hf := GaussianRationalPolynomialExponential.factorial_positive (Γ := Γ) N
  exact positive_product _ _ (power_positive _ _ (positive_product _ _ hd hd)) (positive_product _ _ hf hf)

theorem factor_bound (i z B a d : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hd : Γ ⊢[PRAAx] le one d) (hpos : Γ ⊢[PRAAx] poleAt z B a d (succ i))
    (hneg : Γ ⊢[PRAAx] poleAt (gneg z) B a d (succ i)) :
    Γ ⊢[PRAAx] lower (squareFactor i z B) (a*a) ((d*succ i)*(d*succ i)) :=
  lower_congr (paired_factor i z B hB) (.eqRefl _) (.eqRefl _)
    (product_lower _ _ _ _ _ _ (positive_product _ _ hd (zero_lt_succ i))
      (positive_product _ _ hd (zero_lt_succ i)) (factor_lower i z B a d hB hd hpos)
      (factor_lower i (gneg z) B a d hB hd hneg))

theorem argument_lower (z B a d : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hd : Γ ⊢[PRAAx] le one d) (h : Γ ⊢[PRAAx] poleAt z B a d zero) :
    Γ ⊢[PRAAx] lower (ofGaussian z B) a d := by
  apply lower_from_representation _ _ _ _ _ hB hd (ofGaussian_represents z B hB)
  exact le_congr (by ipra_ring) (congrMul (.eqRefl _) (GaussianRootAlgebra.normSq_equal (translated_zero z B))) h

theorem prefix_zero (z B a d : PTm n) : Γ ⊢[PRAAx] prefixBound z B a d zero := by
  have f := natEq (fact_zero (Γ := Γ) (zero : PTm n))
  have d' : Γ ⊢[PRAAx] denominator d zero ≐ one := by
    unfold denominator
    have p := natEq (pw_zero (Γ := Γ) (d*d))
    apply deriveNat
    ipra_simps
    rw [f,p]
    ring
  exact lower_congr (product_zero body (pairT z B)).eqSymm (pw_zero (a*a)).eqSymm d'.eqSymm lower_one

theorem prefix_succ (z B a d N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hd : Γ ⊢[PRAAx] le one d) (hpos : Γ ⊢[PRAAx] poleAt z B a d (succ N))
    (hneg : Γ ⊢[PRAAx] poleAt (gneg z) B a d (succ N))
    (ih : Γ ⊢[PRAAx] prefixBound z B a d N) : Γ ⊢[PRAAx] prefixBound z B a d (succ N) := by
  let t := d*succ N
  have ht := positive_product (Γ := Γ) _ _ hd (zero_lt_succ N)
  have step := product_lower _ _ _ _ _ _ (denominator_positive d N hd)
    (positive_product t t ht ht) ih (factor_bound N z B a d hB hd hpos hneg)
  have den : Γ ⊢[PRAAx] denominator d N*(t*t) ≐ denominator d (succ N) := by
    have p := natEq (pw_succ (Γ := Γ) (d*d) N)
    have f := natEq (fact_succ (Γ := Γ) N zero)
    unfold denominator t
    apply deriveNat
    ipra_simps
    rw [p,f]
    ring
  exact lower_congr (sine_product_succ z B N).eqSymm (pw_succ (a*a) N).eqSymm den step

theorem head_lower (z B a d N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hd : Γ ⊢[PRAAx] le one d) (h : Γ ⊢[PRAAx] input z B a d N) :
    Γ ⊢[PRAAx] prefixBound z B a d N := by
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have ds : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift d) := by simpa [Fm.shift,Syn.shift] using hd.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift z) (Syn.shift B) (Syn.shift a) (Syn.shift d) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift N) ⟶
      prefixBound (Syn.shift z) (Syn.shift B) (Syn.shift a) (Syn.shift d) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simpa only [Fm.subst_imp,subst_le,subst_prefixBound,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
        (Prf.impI (prefix_zero (Γ := le zero N :: Γ) z B a d))
    · simp only [Fm.subst_imp,subst_le,subst_prefixBound,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact .impI (prefix_succ _ _ _ _ _ bs.wk.wk ds.wk.wk
        (pole_at _ _ _ _ _ _ hs.wk.wk.andE₁ Prf.hyp0) (pole_at _ _ _ _ _ _ hs.wk.wk.andE₂ Prf.hyp0)
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)))
  have last : Γ ⊢[PRAAx] le N N ⟶ prefixBound z B a d N := by
    simpa only [Fm.subst_imp,subst_le,subst_prefixBound,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N
  exact .impE last (le_refl N)

theorem actual_sine_product_head_lower_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ le one (var 3) ⟶ input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      prefixBound (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (head_lower _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianSineProductHeadLower
