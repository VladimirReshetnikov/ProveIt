import GowersSzemeredi.Proofs16PowerCoverUniformUnion
import GowersSzemeredi.Proofs16PowerCoverProfile

/-! Explicit uniform parameters for the common cover of the extracted
Section 16 pieces. Every parameter depends only on density, product constant,
dimension, and requested exceptional fraction. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section16PowerPieceBudget (theta gamma : Real) (k : Nat) : Nat :=
  Nat.ceil (gamma ^ (-(2 : Int)) * multipleS theta gamma (k + 1))

def section16PowerSliceBudget (theta gamma : Real) (k : Nat) : Real :=
  gamma ^ (-(2 : Int)) * multipleS ((2 : Real) ^ (-(k + 2 : Real)) * theta) gamma k

def section16JointPowerLoss (rho theta gamma : Real) (k : Nat) : Real :=
  rho / ((section16PowerPieceBudget theta gamma k : Real) + 1)

def section16JointPowerGraphBudget (rho theta gamma : Real) (k : Nat) : Real :=
  (section16PowerPieceBudget theta gamma k : Real) *
    section16UniformLiftGraphBudget (section16JointPowerLoss rho theta gamma k / 4)
      theta gamma (section16PowerSliceBudget theta gamma k) k

def section16JointPowerExponent (rho theta gamma : Real) (k : Nat) : Real :=
  (min (section16UniformLiftExponent (section16JointPowerLoss rho theta gamma k / 4)
    theta gamma (section16PowerSliceBudget theta gamma k) k) 1) ^
      section16PowerPieceBudget theta gamma k

def section16JointPowerThreshold (rho theta gamma : Real) (k : Nat) : Real :=
  section16PowerIterationThreshold
    (max 1 (section16UniformLiftThreshold (section16JointPowerLoss rho theta gamma k / 4)
      theta gamma (section16PowerSliceBudget theta gamma k) k))
    (min (section16UniformLiftExponent (section16JointPowerLoss rho theta gamma k / 4)
      theta gamma (section16PowerSliceBudget theta gamma k) k) 1)
    (section16PowerPieceBudget theta gamma k)

def Section16JointPowerCoverProfile {N : Nat} [NeZero N] (theta gamma : Real) (k : Nat)
    (Gamma : Finset (Point N (k + 1) × ZMod N)) : Prop :=
  ∀ rho : Real, 0 < rho → rho ≤ 1 →
    LargeBoxMultilinearCover Gamma rho (section16JointPowerGraphBudget rho theta gamma k)
      (section16JointPowerExponent rho theta gamma k) (section16JointPowerThreshold rho theta gamma k)

theorem section16JointPowerLoss_pos {rho theta gamma : Real} (k : Nat) (hr : 0 < rho) :
    0 < section16JointPowerLoss rho theta gamma k := by
  unfold section16JointPowerLoss
  positivity

theorem section16JointPowerLoss_le_one {rho theta gamma : Real} (k : Nat) (hr : rho ≤ 1) :
    section16JointPowerLoss rho theta gamma k ≤ 1 := by
  unfold section16JointPowerLoss
  apply (div_le_one (by positivity)).mpr
  exact hr.trans (by have := Nat.cast_nonneg (α := Real) (section16PowerPieceBudget theta gamma k); linarith)

theorem section16PowerSliceBudget_pos {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (hg : 0 < gamma) : 0 < section16PowerSliceBudget theta gamma k := by
  unfold section16PowerSliceBudget multipleS
  positivity

theorem section16JointPowerExponent_pos {k : Nat} (hk : 0 < k)
    {rho theta gamma : Real} (hr : 0 < rho) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    0 < section16JointPowerExponent rho theta gamma k := by
  unfold section16JointPowerExponent
  exact pow_pos (lt_min (section16UniformLiftExponent_pos hk
    (div_pos (section16JointPowerLoss_pos k hr) (by norm_num)) ht ht1 hg hg1
    (section16PowerSliceBudget_pos k ht hg)) zero_lt_one) _

theorem section16JointPowerThreshold_one_le (rho theta gamma : Real) (k : Nat) :
    1 ≤ section16JointPowerThreshold rho theta gamma k :=
  section16PowerIterationThreshold_one_le _ _ _

/-- Assemble the actual piece profiles into a single cover whose controls
are independent of the extracted piece count. -/
theorem section16_joint_power_profile_of_pieces {N k q : Nat} [NeZero N]
    (hk : 0 < k) {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (G : Fin q → Finset (Point N (k + 1) × ZMod N))
    (hG : ∀ i, Section16PowerCoverProfile theta gamma k (G i))
    (hq : (q : Real) ≤ gamma ^ (-(2 : Int)) * multipleS theta gamma (k + 1)) :
    Section16JointPowerCoverProfile theta gamma k (section16FinsetUnion G) := by
  intro rho hr hr1
  let eta := section16JointPowerLoss rho theta gamma k
  have heta : 0 < eta := section16JointPowerLoss_pos k hr
  have heta1 : eta ≤ 1 := section16JointPowerLoss_le_one k hr1
  have hs := section16PowerSliceBudget_pos k ht hg
  have he := section16UniformLiftExponent_pos (sigma := eta / 4) hk (div_pos heta (by norm_num)) ht ht1 hg hg1 hs
  have hC : 0 ≤ section16UniformLiftGraphBudget (eta / 4) theta gamma
      (section16PowerSliceBudget theta gamma k) k := by
    unfold section16UniformLiftGraphBudget multipleQ multipleC
    dsimp only
    positivity
  have hqR : q ≤ section16PowerPieceBudget theta gamma k := by
    exact_mod_cast hq.trans (Nat.le_ceil _)
  have h := LargeBoxMultilinearCover.bounded_finsetUnion G
    (fun i => hG i eta heta heta1) hqR heta.le he hC
  apply h.loss_mono
  change (section16PowerPieceBudget theta gamma k : Real) *
    (rho / ((section16PowerPieceBudget theta gamma k : Real) + 1)) ≤ rho
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hr.le]

end LeanProofs.GowersSzemeredi
