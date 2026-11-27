import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Compact.GaussianGammaZetaMellinGeometric
import IPRADerivations.Analysis.Gamma.Zeta.Mellin.EndpointBounds.GaussianGammaZetaMellinOriginCell

/-!
# A magnitude bound independent of the finite Mellin count

The finite geometric prefix at the actual reciprocal clock is the
original Mellin observation multiplied by a factor in the disk of
radius two. The result applies to both added exterior strips.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinGeometricEnvelope

open_ipra
open GaussianCoefficientNameBounds (bounded_radius_mono unit unit_positive)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianEulerLowerTailPowerPanel (width)
open GaussianGammaEulerHeadShift (shifted)
open GaussianEulerIntegrandName (powerData powerF)
open GaussianGammaZetaMellinGeometric (weightedValue ratio partial_value ratio_bound)
open GaussianGammaZetaMellinIntegrand (nameF data factorClock reciprocalF reciprocalData sample_at)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded qsub qnegative)
open GaussianRationalPowerDifference (bounded_power_integer bounded_sum_one)
open GaussianRationalReciprocal (power bounded_negative bounded_product bound_congr qone_bounded)
open GaussianRationalSyntheticDivision (qone qmul_congr)
open GaussianReciprocalHorner (qmul_associative)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def factor (p z D a b N : PTm n) : PTm n :=
  qsub qone (power (ratio (factorClock p z D a b) a b) N)

theorem factorization (p z D a b N : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] weightedValue p z D a b N ≐
      qmul (ap2 nameF p (data z D a b)) (factor p z D a b N) := by
  let k := factorClock p z D a b
  let x := ap2 powerF k (powerData z D a b)
  let y := ap2 reciprocalF k (reciprocalData a b)
  let v := factor p z D a b N
  exact (qmul_congr (.eqRefl x) (partial_value k a b N ha hb)).eqTrans
    ((qmul_associative x y v).eqSymm.eqTrans (qmul_congr (sample_at p z D a b).eqSymm (.eqRefl v)))

theorem factor_bound (p z D a b N : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] bounded (factor p z D a b N) two one := by
  let x := ratio (factorClock p z D a b) a b
  have hx : Γ ⊢[PRAAx] bounded x one one := by
    have cmp : Γ ⊢[PRAAx] le (b*one) (one*(b+a)) :=
      le_congr ((mul_comm b one).eqTrans (one_mul b)).eqSymm (one_mul (b+a)).eqSymm (le_add_right b a)
    exact bounded_radius_mono x b (b+a) one one (le_trans hb (le_add_right b a)) (le_refl one) cmp
      (ratio_bound (factorClock p z D a b) a b hb)
  have hp : Γ ⊢[PRAAx] bounded (power x N) one one :=
    bound_congr (.eqRefl _) (GaussianPolynomialPerturbation.one_power N) (.eqRefl _)
      (bounded_power_integer x one N hx)
  have h := bounded_sum_one qone_bounded
    (bounded_negative _ _ _ (le_refl one) hp)
  exact bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _) h

/-- Same-clock envelope in terms of any available original Mellin point bound. -/
theorem weighted_bound (p z D a b N U V : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hV : Γ ⊢[PRAAx] le one V) (h : Γ ⊢[PRAAx] bounded (ap2 nameF p (data z D a b)) U V) :
    Γ ⊢[PRAAx] bounded (weightedValue p z D a b N) (U*two) V :=
  bound_congr (factorization p z D a b N ha hb).eqSymm (.eqRefl _)
    ((mul_comm V one).eqTrans (one_mul V))
    (bounded_product _ _ U V two one hV (le_refl one) h (factor_bound p z D a b N hb))

/-- The same bound holds after multiplying by an arbitrary original cell weight. -/
theorem weighted_product_bound (p z D a b N w U V : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) (hV : Γ ⊢[PRAAx] le one V)
    (h : Γ ⊢[PRAAx] bounded (qmul w (ap2 nameF p (data z D a b))) U V) :
    Γ ⊢[PRAAx] bounded (qmul w (weightedValue p z D a b N)) (U*two) V := by
  have e := (qmul_congr (.eqRefl w) (factorization p z D a b N ha hb)).eqTrans
    (qmul_associative w (ap2 nameF p (data z D a b)) (factor p z D a b N)).eqSymm
  exact bound_congr e.eqSymm (.eqRefl _) ((mul_comm V one).eqTrans (one_mul V))
    (bounded_product _ _ U V two one hV (le_refl one) h (factor_bound p z D a b N hb))

def originCell (p z D k x y b N : PTm n) : PTm n :=
  qmul (fraction (width x y k) (pw b (succ k)))
    (weightedValue p (shifted z D) D (pw y (succ k)) (pw b (succ k)) N)

theorem origin_cell_bound (p z R D k x y b N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerOrder.source z R D (succ k) y b)
    (hxy : Γ ⊢[PRAAx] le x y) :
    Γ ⊢[PRAAx] bounded (originCell p z D k x y b N)
      (((succ k*monus y x)*(unit p+num 3))*two) (b*unit p) := by
  have hy := GaussianPolynomialPerturbation.power_positive y (succ k) h.andE₂.andE₁.andE₁
  have hb := GaussianPolynomialPerturbation.power_positive b (succ k) h.andE₂.andE₁.andE₂
  exact weighted_product_bound p (shifted z D) D (pw y (succ k)) (pw b (succ k)) N
    (fraction (width x y k) (pw b (succ k))) _ _ hy hb (positive_product _ _ h.andE₂.andE₁.andE₂ (unit_positive p))
    (GaussianGammaZetaMellinOriginCell.right_cell_bound p z R D k x y b h hxy)

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinGeometricEnvelope
