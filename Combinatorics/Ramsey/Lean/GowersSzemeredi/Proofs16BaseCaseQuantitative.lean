import GowersSzemeredi.Proofs16BaseCaseRestriction

/-!
# Quantitative slack for the one-dimensional base case

This module isolates the numerical estimates used by both branches of the
proper-box cover.  A sufficiently large share of the global iteration budget
forces a tiny local width exponent and a correspondingly large graph-count
allowance.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi.BaseCase

/-! ## Quantitative slack for one extracted graph -/

def lemma163Iteration (gamma theta : Real) : Real :=
  gamma ^ (-(2 : Int)) * multipleS theta gamma 1

def lemma163StageIteration (gamma theta : Real) (q : Nat) : Real :=
  lemma163Iteration gamma theta / q

def lemma163LocalExponent
    (gamma theta eta : Real) (q : Nat) : Real :=
  (multipleC ((lemma163StageIteration gamma theta q)⁻¹ * eta) gamma 1) ^
    (lemma163StageIteration gamma theta q)

def lemma163LocalGraphBound
    (gamma theta eta : Real) (q : Nat) : Real :=
  (multipleQ ((lemma163StageIteration gamma theta q)⁻¹ * eta) gamma 1) ^
    (lemma163StageIteration gamma theta q)

lemma lemma163_stage_large {gamma theta : Real} {q : Nat}
    (hgamma : 0 < gamma) (hgammaOne : gamma ≤ 1)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1) (hq : 0 < q)
    (hqBound : (q : Real) * lemma163Alpha gamma theta ≤
      gamma ^ (-(2 : Int))) :
    (2 : Real) ^ (8000 : Nat) ≤ lemma163StageIteration gamma theta q := by
  let a := gamma * theta
  let T : Nat := (2 : Nat) ^ ((2 : Nat) ^ (1 + 6))
  have ha : 0 < a := by dsimp only [a]; positivity
  have haOne : a ≤ 1 := by
    dsimp only [a]
    nlinarith [mul_le_mul hgammaOne hthetaOne htheta.le (by norm_num : (0 : Real) ≤ 1)]
  have hqReal : (0 : Real) < q := by exact_mod_cast hq
  have hstageAlpha :
      multipleS theta gamma 1 * lemma163Alpha gamma theta ≤
        lemma163StageIteration gamma theta q := by
    rw [show lemma163StageIteration gamma theta q =
        (gamma ^ (-(2 : Int)) / q) * multipleS theta gamma 1 by
      unfold lemma163StageIteration lemma163Iteration
      ring]
    calc
      multipleS theta gamma 1 * lemma163Alpha gamma theta ≤
          multipleS theta gamma 1 * (gamma ^ (-(2 : Int)) / q) := by
        apply mul_le_mul_of_nonneg_left _ (by unfold multipleS; positivity)
        exact (le_div_iff₀ hqReal).2 (by simpa [mul_comm] using hqBound)
      _ = (gamma ^ (-(2 : Int)) / q) * multipleS theta gamma 1 := by ring
  have hT : 10000 ≤ T := by
    dsimp only [T]
    norm_num
  have hbase : (1 : Real) ≤ 2 / a := by
    have : a ≤ 2 := haOne.trans (by norm_num)
    exact (le_div_iff₀ ha).2 (by simpa using this)
  have hmain : (2 : Real) ^ (8000 : Nat) ≤
      multipleS theta gamma 1 * lemma163Alpha gamma theta := by
    have hsplit : T = 10000 + (T - 10000) := by omega
    have hS : multipleS theta gamma 1 = (2 / a) ^ T := by
      unfold multipleS
      rw [show theta * gamma = a by dsimp only [a]; ring]
    have hAlpha : lemma163Alpha gamma theta =
        (2 : Real) ^ (-(2000 : Real)) * a ^ (10000 : Nat) := by
      unfold lemma163Alpha
      rfl
    rw [hS, hAlpha]
    rw [hsplit, pow_add]
    have hcancel :
        (2 / a) ^ (10000 : Nat) * a ^ (10000 : Nat) =
          (2 : Real) ^ (10000 : Nat) := by
      rw [← mul_pow]
      field_simp [ha.ne']
    have htail : (1 : Real) ≤ (2 / a) ^ (T - 10000) := by
      exact one_le_pow₀ hbase
    calc
      (2 : Real) ^ (8000 : Nat) =
          (2 : Real) ^ (10000 : Nat) * (2 : Real) ^ (-(2000 : Real)) := by
        calc
          (2 : Real) ^ (8000 : Nat) = (2 : Real) ^ (8000 : Real) :=
            (Real.rpow_natCast 2 8000).symm
          _ = (2 : Real) ^ ((10000 : Real) + (-(2000 : Real))) := by norm_num
          _ = (2 : Real) ^ (10000 : Real) *
              (2 : Real) ^ (-(2000 : Real)) :=
            Real.rpow_add (x := (2 : Real))
              (by norm_num : (0 : Real) < 2)
              (10000 : Real) (-(2000 : Real))
          _ = (2 : Real) ^ (10000 : Nat) *
              (2 : Real) ^ (-(2000 : Real)) := by
            have h10000 : (2 : Real) ^ (10000 : Real) =
                (2 : Real) ^ (10000 : Nat) :=
              Real.rpow_natCast 2 10000
            rw [h10000]
      _ = ((2 / a) ^ (10000 : Nat) * a ^ (10000 : Nat)) *
          (2 : Real) ^ (-(2000 : Real)) := by rw [hcancel]
      _ ≤ ((2 / a) ^ (10000 : Nat) * (2 / a) ^ (T - 10000)) *
          ((2 : Real) ^ (-(2000 : Real)) * a ^ (10000 : Nat)) := by
        have hc : 0 ≤ ((2 / a) ^ (10000 : Nat) * a ^ (10000 : Nat)) *
            (2 : Real) ^ (-(2000 : Real)) := by positivity
        calc
          ((2 / a) ^ (10000 : Nat) * a ^ (10000 : Nat)) *
                (2 : Real) ^ (-(2000 : Real)) ≤
              (((2 / a) ^ (10000 : Nat) * a ^ (10000 : Nat)) *
                (2 : Real) ^ (-(2000 : Real))) *
                  (2 / a) ^ (T - 10000) :=
            le_mul_of_one_le_right hc htail
          _ = _ := by ac_rfl
      _ = _ := by ac_rfl
  exact hmain.trans hstageAlpha

lemma lemma163_local_bounds {gamma theta eta : Real} {q : Nat}
    (hgamma : 0 < gamma) (hgammaOne : gamma ≤ 1)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1)
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (hq : 0 < q)
    (hqBound : (q : Real) * lemma163Alpha gamma theta ≤
      gamma ^ (-(2 : Int))) :
    0 < lemma163LocalExponent gamma theta eta q ∧
    lemma163LocalExponent gamma theta eta q ≤
        (2 : Real) ^ (-(512 : Real)) * eta ^ (2 : Nat) ∧
    (2 : Real) ^ (512 : Nat) * eta ^ (-(2 : Int)) ≤
      lemma163LocalGraphBound gamma theta eta q := by
  let s := lemma163StageIteration gamma theta q
  let b := gamma * (s⁻¹ * eta)
  let E : Nat := (2 : Nat) ^ ((2 : Nat) ^ (1 + 8))
  have hsLarge := lemma163_stage_large hgamma hgammaOne htheta hthetaOne hq hqBound
  have htwoPowOne : (1 : Real) ≤ 2 ^ (8000 : Nat) :=
    one_le_pow₀ (by norm_num)
  have hs : (1 : Real) ≤ s := htwoPowOne.trans hsLarge
  have hsPos : 0 < s := zero_lt_one.trans_le hs
  have hb : 0 < b := by dsimp only [b]; positivity
  have hbHalf : b ≤ eta / 2 := by
    dsimp only [b]
    have htwoSelf : (2 : Real) ≤ 2 ^ (8000 : Nat) :=
      le_self_pow₀ (by norm_num) (by norm_num)
    have hsTwo : (2 : Real) ≤ s := htwoSelf.trans hsLarge
    have hinv : s⁻¹ ≤ (2 : Real)⁻¹ :=
      (inv_le_inv₀ hsPos (by norm_num)).2 hsTwo
    calc
      gamma * (s⁻¹ * eta) ≤ 1 * ((2 : Real)⁻¹ * eta) := by gcongr
      _ = eta / 2 := by ring
  have hbOne : b ≤ 1 := hbHalf.trans (by nlinarith)
  have hE : 512 ≤ E := by
    dsimp only [E]
    rw [show 512 = 2 ^ 9 by norm_num]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hC : b ^ E ≤ (eta / 2) ^ (512 : Nat) := by
    calc
      b ^ E ≤ b ^ (512 : Nat) := pow_le_pow_of_le_one hb.le hbOne hE
      _ ≤ (eta / 2) ^ (512 : Nat) := by gcongr
  have hCOne : b ^ E ≤ 1 := pow_le_one₀ hb.le hbOne
  have hw : (b ^ E) ^ s ≤ b ^ E :=
    Real.rpow_le_self_of_le_one (by positivity) hCOne hs
  have hetaPow : eta ^ (512 : Nat) ≤ eta ^ (2 : Nat) :=
    pow_le_pow_of_le_one heta.le hetaOne (by omega)
  have htwoNeg :
      (2 : Real) ^ (-(512 : Real)) =
        ((2 : Real) ^ (512 : Nat))⁻¹ := by
    calc
      (2 : Real) ^ (-(512 : Real)) =
          ((2 : Real) ^ (512 : Real))⁻¹ :=
        Real.rpow_neg (by norm_num) (512 : Real)
      _ = ((2 : Real) ^ (512 : Nat))⁻¹ :=
        congrArg (fun x : Real => x⁻¹) (Real.rpow_natCast 2 512)
  have hsmall : (b ^ E) ^ s ≤
      (2 : Real) ^ (-(512 : Real)) * eta ^ (2 : Nat) := by
    calc
      (b ^ E) ^ s ≤ b ^ E := hw
      _ ≤ (eta / 2) ^ (512 : Nat) := hC
      _ = (2 : Real) ^ (-(512 : Real)) * eta ^ (512 : Nat) := by
        rw [div_pow, div_eq_mul_inv, htwoNeg]
        ac_rfl
      _ ≤ (2 : Real) ^ (-(512 : Real)) * eta ^ (2 : Nat) := by gcongr
  have hwPos : 0 < (b ^ E) ^ s := Real.rpow_pos_of_pos (pow_pos hb E) s
  have hgraph : (2 : Real) ^ (512 : Nat) * eta ^ (-(2 : Int)) ≤
      ((b ^ E)⁻¹) ^ s := by
    rw [Real.inv_rpow (by positivity)]
    have hleftPos : 0 < (2 : Real) ^ (512 : Nat) * eta ^ (-(2 : Int)) := by
      positivity
    apply (le_inv_comm₀ hleftPos hwPos).2
    calc
      (b ^ E) ^ s ≤ (2 : Real) ^ (-(512 : Real)) * eta ^ (2 : Nat) := hsmall
      _ = ((2 : Real) ^ (512 : Nat) * eta ^ (-(2 : Int)))⁻¹ := by
        rw [htwoNeg, mul_inv, zpow_neg, zpow_ofNat, inv_inv]
  have hlocalExponent :
      lemma163LocalExponent gamma theta eta q = (b ^ E) ^ s := by
    rfl
  have hlocalGraphBound :
      lemma163LocalGraphBound gamma theta eta q = ((b ^ E)⁻¹) ^ s := by
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hlocalExponent]
    exact hwPos
  · rw [hlocalExponent]
    exact hsmall
  · rw [hlocalGraphBound]
    exact hgraph

def lemma163CorollaryExponent (eta : Real) : Real :=
  (2 : Real) ^ (-(14 : Real)) * eta ^ (2 : Nat)

def lemma163CoarseCellLength (eta : Real) : Nat :=
  Nat.ceil (4096 / eta)

lemma lemma163_exponent_le_corollary_half {gamma theta eta : Real}
    {q : Nat} (hgamma : 0 < gamma) (hgammaOne : gamma ≤ 1)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1)
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (hq : 0 < q)
    (hqBound : (q : Real) * lemma163Alpha gamma theta ≤
      gamma ^ (-(2 : Int))) :
    lemma163LocalExponent gamma theta eta q ≤
      lemma163CorollaryExponent eta / 2 := by
  have h := (lemma163_local_bounds hgamma hgammaOne htheta hthetaOne
    heta hetaOne hq hqBound).2.1
  unfold lemma163CorollaryExponent
  calc
    lemma163LocalExponent gamma theta eta q ≤
        (2 : Real) ^ (-(512 : Real)) * eta ^ (2 : Nat) := h
    _ ≤ ((2 : Real) ^ (-(14 : Real)) * eta ^ (2 : Nat)) / 2 := by
      have : (2 : Real) ^ (-(512 : Real)) ≤
          (2 : Real) ^ (-(15 : Real)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      calc
        (2 : Real) ^ (-(512 : Real)) * eta ^ (2 : Nat) ≤
            (2 : Real) ^ (-(15 : Real)) * eta ^ (2 : Nat) :=
          mul_le_mul_of_nonneg_right this (sq_nonneg eta)
        _ = ((2 : Real) ^ (-(14 : Real)) * eta ^ (2 : Nat)) / 2 := by
          norm_num [Real.rpow_neg, Real.rpow_natCast]
          ring

lemma lemma163_coarse_count_le_graphBound {gamma theta eta : Real}
    {q : Nat} (hgamma : 0 < gamma) (hgammaOne : gamma ≤ 1)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1)
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (hq : 0 < q)
    (hqBound : (q : Real) * lemma163Alpha gamma theta ≤
      gamma ^ (-(2 : Int))) :
    ((2 * lemma163CoarseCellLength eta : Nat) : Real) ≤
      lemma163LocalGraphBound gamma theta eta q := by
  have hg := (lemma163_local_bounds hgamma hgammaOne htheta hthetaOne
    heta hetaOne hq hqBound).2.2
  have hceil : (lemma163CoarseCellLength eta : Real) < 4096 / eta + 1 := by
    exact Nat.ceil_lt_add_one (by positivity)
  have hetaInv : 1 ≤ eta⁻¹ := by
    simpa using (inv_le_inv₀ (by norm_num : (0 : Real) < 1) heta).2 hetaOne
  have hcoarse : ((2 * lemma163CoarseCellLength eta : Nat) : Real) ≤
      (2 : Real) ^ (14 : Nat) * eta ^ (-(2 : Int)) := by
    push_cast
    rw [zpow_neg, zpow_ofNat, ← inv_pow]
    have : (lemma163CoarseCellLength eta : Real) ≤ 4097 * eta⁻¹ := by
      rw [div_eq_mul_inv] at hceil
      nlinarith
    have hinvSq : eta⁻¹ ≤ eta⁻¹ ^ (2 : Nat) := by nlinarith [sq_nonneg eta⁻¹]
    calc
      2 * (lemma163CoarseCellLength eta : Real) ≤ 8194 * eta⁻¹ := by nlinarith
      _ ≤ 8194 * eta⁻¹ ^ (2 : Nat) := by gcongr
      _ ≤ (2 : Real) ^ (14 : Nat) * eta⁻¹ ^ (2 : Nat) := by
        apply mul_le_mul_of_nonneg_right (by norm_num)
        positivity
  have hpow : (2 : Real) ^ (14 : Nat) ≤ 2 ^ (512 : Nat) :=
    pow_le_pow_right₀ (by norm_num) (by norm_num)
  exact hcoarse.trans ((mul_le_mul_of_nonneg_right
    hpow
    (by positivity : 0 ≤ eta ^ (-(2 : Int)))).trans hg)

end LeanProofs.GowersSzemeredi.BaseCase
