import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.ThirdDerivative.Cofinal.GaussianBarnesCanonicalThirdLogarithmOrder
import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.Observations.GaussianSignedObservationOrder
import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.CubicTaylor.SignedCubicTaylorGrid
import IPRADerivations.Analysis.Names.Rates.Moduli.GaussianRationalModulus

/-!
# Cubic force of the actual far-axis Barnes discrepancy

At precision p, translate by the integer 4*2^p. Every original
canonical cubic observation at the translated chart then has norm at
most 2^(-p). Named nonnegativity of the candidate derivative bounds
its actual p-observation from below. The difference of the two signed
rounded derivative numerators is at least -5, including both roundings.
-/

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesVignerasCubicForce

open_ipra
open GaussianBarnesCanonicalThirdLogarithmCauchy (gain)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at scalar_coordinate_distance)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (distanceBounded bounded qnormSq qsub squaredTolerance)
open GaussianSignedObservationGrid (rounded)
open RationalValueBounds (upper upper_congr upper_of_radius upper_triangle upper_mono)
open PolynomialBisection (zle_congr zle_scale)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def translation (p : PTm n) : PTm n := gain*unit p

def farNumerator (p A B : PTm n) : PTm n := A+translation p*B

def canonicalSample (p A B : PTm n) : PTm n :=
  ap2 GaussianBarnesCanonicalThirdLogarithmCofinal.nameF p
    (GaussianBarnesCanonicalThirdLogarithmCofinal.data (farNumerator p A B) B)

def coefficient (g : PR 2) (x p A B : PTm n) : ZT n :=
  rounded (ap2 g p x) (unit p)-rounded (canonicalSample p A B) (unit p)

def forceBudget (H : PTm n) : PTm n := num 30*(H*(H*H))

@[simp] theorem subst_translation {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (translation p) = translation (Syn.subst σ p) := by
  simp [translation,gain,two,one]

@[simp] theorem subst_farNumerator {m : ℕ} (σ : Fin n → PTm m) (p A B : PTm n) :
    Syn.subst σ (farNumerator p A B) = farNumerator (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ B) := by
  simp [farNumerator]

@[simp] theorem subst_canonicalSample {m : ℕ} (σ : Fin n → PTm m) (p A B : PTm n) :
    Syn.subst σ (canonicalSample p A B) = canonicalSample (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ B) := by
  simp [canonicalSample]

@[simp] theorem subst_coefficient {m : ℕ} (σ : Fin n → PTm m) (g : PR 2) (x p A B : PTm n) :
    (coefficient g x p A B).subst σ =
      coefficient g (Syn.subst σ x) (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ B) := by
  simp [coefficient]

theorem canonical_decay (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (canonicalSample p A B) one (unit p) := by
  have hG : Γ ⊢[PRAAx] le one (gain : PTm n) :=
    positive_product _ _ (le_succ_self one) (le_succ_self one)
  have hT := positive_product (Γ := Γ) _ _ hG (unit_positive p)
  have far : Γ ⊢[PRAAx] le (translation p*B) (farNumerator p A B) := le_add_left _ _
  have start : Γ ⊢[PRAAx] le B (farNumerator p A B) :=
    le_trans (le_congr (one_mul B) (.eqRefl _) (mul_le_mul_right B hT)) far
  exact GaussianBarnesCanonicalThirdLogarithmOrder.far_decay p p _ B hB start far

theorem upper_at (g : PR 2) (x p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hg : Γ ⊢[PRAAx] realOrder constantF g qzero x) :
    Γ ⊢[PRAAx] upper (fstT (canonicalSample p A B)) (fstT (ap2 g p x)) (num 3) (unit p) := by
  let q := canonicalSample p A B
  let r := ap2 g p x
  let U := unit p
  have hU := unit_positive (Γ := Γ) p
  have dist : Γ ⊢[PRAAx] distanceBounded q qzero one U := by
    change Γ ⊢[PRAAx] RationalArgmin.rationalLE (qnormSq (qsub q qzero)) (squaredTolerance one U)
    exact RationalArgmin.rationalLE_congr (GaussianRationalModulus.norm_sub_zero q).eqSymm
      (.eqRefl _) (canonical_decay p A B hB)
  have small : Γ ⊢[PRAAx] upper (fstT q) (fstT (qzero : PTm n)) one U :=
    upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hU dist)
  have sign : Γ ⊢[PRAAx] upper (fstT (qzero : PTm n)) (fstT r) (U+U) (U*U) :=
    upper_congr (congrFst (constant_at p qzero)) (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (real_order_at constantF g qzero x p p hg)
  have comp := upper_triangle _ _ _ _ _ _ _ small sign
  apply upper_mono _ _ _ _ _ _ (positive_product _ _ hU (positive_product _ _ hU hU)) comp
  exact le_congr (.eqRefl _) (by ipra_ring) (le_refl _)

theorem coefficient_lower (g : PR 2) (x p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hg : Γ ⊢[PRAAx] realOrder constantF g qzero x) :
    Γ ⊢[PRAAx] zle (-ZT.ofNat (num 5)) (coefficient g x p A B) :=
  zle_congr (by simp only [ZT.toZ_neg,ZT.toZ_ofNat]; ipra_simps; ring) rfl
    (GaussianSignedObservationOrder.lower _ _ _ _ (upper_at g x p A B hB hg))

theorem force_lower (g : PR 2) (x p A B H : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hg : Γ ⊢[PRAAx] realOrder constantF g qzero x) :
    Γ ⊢[PRAAx] zle (-ZT.ofNat (forceBudget H)) (SignedCubicTaylorGrid.force (coefficient g x p A B) H) := by
  apply zle_congr ?_ rfl (zle_scale (num 6*(H*(H*H))) (coefficient_lower g x p A B hB hg))
  simp only [forceBudget,ZT.toZ_mul,ZT.toZ_neg,ZT.toZ_ofNat,Q.mk_mul,map_mul]
  ipra_simps
  ring

theorem actual_Barnes_far_cubic_force_lower_closed (g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (let x := var 0
       let p := var 1
       let A := var 2
       let B := var 3
       let H := var 4
       le one B ⟶ realOrder constantF g qzero x ⟶
         zle (-ZT.ofNat (forceBudget H)) (SignedCubicTaylorGrid.force (coefficient g x p A B) H)) :=
  closeUniv 5 (.impI (.impI (force_lower g _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesVignerasCubicForce
