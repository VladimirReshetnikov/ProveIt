import IPRADerivations.Analysis.Logarithm.FiniteSeries.GaussianFiniteLogarithmWeightedNorm
import IPRADerivations.Analysis.Exponential.FiniteSeries.ExponentialMajorant

/-!
# The actual finite exponential's auxiliary-radius coefficient norm

The original power prefixes and original factorial-weighted exponential
stages retain their numerical cap. Genuine guarded QF inductions compare
their actual weighted coefficient norms with actual nonnegative rational
powers and the existing finite geometric program. The original H_d norm
bound is derived by its supplier, not assumed at the source endpoint.
This is a finite C4 majorant; no analytic exponential identity is asserted.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianFiniteExponentialWeightedNorm

open_ipra
open GaussianRationalPolynomialDilation (weightedNorm dilated)
open GaussianRationalHorner (qmul)
open GaussianRationalSyntheticDivision (qone qone_canonical)
open GaussianRationalPolynomialPowers (powerPrefix prefix_length)
open GaussianRationalPolynomialExponential (stage advance inverseFactorial factorial_positive)
open GaussianRationalPolynomialBuffers (leftPad added)
open GaussianRationalCoefficientScaling (scaled)
open GaussianRationalMonicReduction (singleton)
open GaussianCoefficientL1 (coefficientNorm prefixNorm qL1_congr)
open GaussianRationalL1 (qL1)
open GaussianEuclideanDistanceName (fraction fraction_represents fraction_order)
open RationalArgmin (rationalLE)
open RationalArithmetic (multiply add)
open RationalSupMetric (numeratorOf)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def ratio : PTm n := fraction (num 65) (num 72)
def powerBudget (j : PTm n) : PTm n := RationalNonnegativePowers.power (num 65) (num 72) j
ipra_subst ratio
ipra_subst powerBudget
theorem denominator_positive : Γ ⊢[PRAAx] le one (num 72 : PTm n) := le_of_eq_add (d := num 71) (by ipra_ring)
theorem power_denominator_positive (j : PTm n) : Γ ⊢[PRAAx] le one (pw (num 72) j) :=
  GaussianFactorBudget.power_positive _ _ denominator_positive

theorem weighted_congr {C D N M t u : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D)
    (hN : Γ ⊢[PRAAx] N ≐ M) (ht : Γ ⊢[PRAAx] t ≐ u) : Γ ⊢[PRAAx]
    weightedNorm C N t ≐ weightedNorm D M u := by
  ipra_congr (weightedNorm (var 0) (var 1) (var 2) : PTm 3) with [hC, hN, ht]

theorem weighted_nonnegative (C N t : PTm n) : Γ ⊢[PRAAx]
    le (numeratorOf (weightedNorm C N t)).neg (numeratorOf (weightedNorm C N t)).pos :=
  GaussianCoefficientNormOrder.coefficient_numerator_nonnegative _
theorem power_nonnegative (j : PTm n) : Γ ⊢[PRAAx]
    le (numeratorOf (powerBudget j)).neg (numeratorOf (powerBudget j)).pos :=
  GaussianRationalL1.nonnegative_of_representation _ _ _ (power_denominator_positive j)
    (RationalNonnegativePowers.power_represents _ _ _ denominator_positive)

/-- Two actual scalar comparisons multiply through derived nonnegative
factors; no coefficient-output norm law is introduced. -/
theorem multiply_bounds (a b A B : PTm n)
    (hb : Γ ⊢[PRAAx] le (numeratorOf b).neg (numeratorOf b).pos)
    (hA : Γ ⊢[PRAAx] le (numeratorOf A).neg (numeratorOf A).pos)
    (ha : Γ ⊢[PRAAx] rationalLE a A) (hB : Γ ⊢[PRAAx] rationalLE b B) :
    Γ ⊢[PRAAx] rationalLE (multiply a b) (multiply A B) :=
  RationalArgmin.transitive
    (RationalArgmin.rationalLE_congr (RationalAlgebra.multiply_commutative _ _)
      (RationalAlgebra.multiply_commutative _ _) (RationalArithmetic.multiply_monotone b a A hb ha))
    (RationalArithmetic.multiply_monotone A b B hA hB)

theorem singleton_weighted_norm (t : PTm n) : Γ ⊢[PRAAx]
    weightedNorm (singleton qone) zero t ≐ fraction one one := by
  have value : Γ ⊢[PRAAx] entry (dilated (singleton qone) zero t) zero ≐ qone :=
    (GaussianRationalPolynomialDilation.dilated_lookup _ zero t zero (le_refl _)).eqTrans
      ((GaussianRationalSyntheticDivision.qmul_congr (GaussianRationalMonicReduction.singleton_lookup qone)
        ((congrAp2 GaussianRationalReciprocal.powerF (monus_self zero) (.eqRefl _)).eqTrans
          (GaussianRationalReciprocal.power_zero t))).eqTrans
            (GaussianReciprocalHorner.qmul_one_right qone qone_canonical))
  have initial := (GaussianCoefficientL1.prefix_zero (Γ := Γ) (dilated (singleton qone) zero t)).eqTrans
    GaussianRationalLinearProduct.scalar_zero_code.eqSymm
  exact (GaussianRationalLinearProduct.norm_length _ _ (GaussianRationalPolynomialDilation.dilated_length _ _ _)).eqTrans
    ((GaussianCoefficientL1.prefix_succ _ zero).eqTrans
      ((RationalAlgebra.add_congr initial ((qL1_congr value).eqTrans GaussianRationalSyntheticBounds.qL1_qone)).eqTrans
        (GaussianRationalLinearProduct.scalar_zero_add _
          (RationalNormalForm.normalize_well_formed _ _ (le_refl one)))))

def powerLaw (C N K t j : PTm n) : Fm PTm n := le j K ⟶
  rationalLE (weightedNorm (powerPrefix C N K j) (j*N) t) (powerBudget j)
ipra_subst powerLaw

theorem power_zero (C N K t : PTm n) : Γ ⊢[PRAAx] powerLaw C N K t zero := by
  refine .impI ?_
  have actual := (weighted_congr (Γ := le zero K :: Γ) (GaussianRationalPolynomialPowers.prefix_zero C N K)
    (zero_mul N) (.eqRefl _)).eqTrans (singleton_weighted_norm t)
  exact RationalArgmin.rationalLE_congr actual.eqSymm (RationalNonnegativePowers.power_zero (num 65) (num 72)).eqSymm
    (RationalArgmin.reflexive _)

theorem power_step (C N K t j : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hNorm : Γ ⊢[PRAAx] rationalLE (weightedNorm C N t) ratio)
    (hj : Γ ⊢[PRAAx] lt j K)
    (ih : Γ ⊢[PRAAx] rationalLE (weightedNorm (powerPrefix C N K j) (j*N) t) (powerBudget j)) :
    Γ ⊢[PRAAx] rationalLE (weightedNorm (powerPrefix C N K (succ j)) (succ j*N) t) (powerBudget (succ j)) := by
  have productBound := GaussianRationalPolynomialDilation.weighted_product_bound
    (powerPrefix C N K j) C (j*N) N t (prefix_length _ _ _ _) hC
  have monotone := multiply_bounds _ _ _ _ (weighted_nonnegative C N t) (power_nonnegative j) ih hNorm
  have joined := RationalArgmin.transitive productBound monotone
  exact RationalArgmin.rationalLE_congr
    (weighted_congr (GaussianRationalPolynomialPowers.prefix_succ C N K j hj).eqSymm (by ipra_ring) (.eqRefl _))
    (RationalNonnegativePowers.power_succ (num 65) (num 72) j denominator_positive).eqSymm joined

/-- Actual original fixed-cap power prefixes obey the source coefficient
norm majorant. The cap is retained inside the QF induction guard. -/
theorem power_bound (C N K t j : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hNorm : Γ ⊢[PRAAx] rationalLE (weightedNorm C N t) ratio) (hj : Γ ⊢[PRAAx] le j K) :
    Γ ⊢[PRAAx] rationalLE (weightedNorm (powerPrefix C N K j) (j*N) t) (powerBudget j) := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hC.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] rationalLE (weightedNorm (Syn.shift C) (Syn.shift N) (Syn.shift t)) ratio := by
    simpa only [Fm.shift,RationalArgmin.subst_rationalLE,GaussianRationalPolynomialDilation.subst_weightedNorm,subst_ratio,Syn.shift] using hNorm.shift
  have all : Γ ⊢[PRAAx] .all (powerLaw (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift t) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,le_QF _ _⟩) [subst_powerLaw]
    · exact power_zero _ _ _ _
    · exact .impI (power_step _ _ _ _ _ cs.wk.wk ns.wk.wk Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)))
  have rule : Γ ⊢[PRAAx] powerLaw C N K t j := by
    simpa only [subst_powerLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE rule hj


theorem inverse_factorial_norm (r : PTm n) : Γ ⊢[PRAAx]
    qL1 (inverseFactorial r) ≐ fraction one (Products.fact r) :=
  GaussianFiniteLogarithmWeightedNorm.l1_from_representation _ _ _ _ (factorial_positive r)
    (GaussianRationalPolynomialExponential.inverse_factorial_represents r) GaussianL1.norm1_one

theorem inverse_factorial_bound (r : PTm n) : Γ ⊢[PRAAx] rationalLE (qL1 (inverseFactorial r)) (fraction one one) :=
  RationalArgmin.rationalLE_congr (inverse_factorial_norm r).eqSymm (.eqRefl _)
    (fraction_order one (Products.fact r) one one (factorial_positive r) (le_refl _)
      (le_congr (by ipra_ring) (by ipra_ring) (factorial_positive r)))

theorem weighted_term_bound (C N K t r : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hNorm : Γ ⊢[PRAAx] rationalLE (weightedNorm C N t) ratio) (hr : Γ ⊢[PRAAx] le r K) : Γ ⊢[PRAAx]
    rationalLE (weightedNorm (scaled (powerPrefix C N K r) (inverseFactorial r)) (r*N) t) (powerBudget r) := by
  have first := GaussianRationalPolynomialDilation.weighted_scaled_bound (Γ := Γ) (powerPrefix C N K r) (r*N) t
    (inverseFactorial r) (prefix_length _ _ _ _)
  have second := multiply_bounds _ _ _ _ (weighted_nonnegative _ _ _)
    (GaussianRationalSyntheticBounds.natCode_nonnegative one) (inverse_factorial_bound r) (power_bound C N K t r hC hNorm hr)
  have unit : Γ ⊢[PRAAx] multiply (fraction one one) (powerBudget r) ≐ powerBudget r :=
    (RationalNonnegativePowers.fraction_multiply one one (pw (num 65) r) (pw (num 72) r)
      (le_refl _) (power_denominator_positive r)).eqTrans
      (RationalNonnegativePowers.fraction_congr (one_mul _) (one_mul _))
  exact RationalArgmin.rationalLE_congr (.eqRefl _) unit (RationalArgmin.transitive first second)

def geometricData : PTm n := pairT (num 65) (num 7)
def geometricPrefix (j : PTm n) : PTm n := fraction (ExponentialMajorant.Gg (succ j) geometricData) (pw (num 72) j)
ipra_subst geometricData
ipra_subst geometricPrefix [ExponentialMajorant.Gg]

theorem geometric_step (j : PTm n) : Γ ⊢[PRAAx] ExponentialMajorant.Gg (succ j) geometricData ≐
    num 72*ExponentialMajorant.Gg j geometricData+pw (num 65) j :=
  (ExponentialMajorant.Gg_succ j geometricData).eqTrans
    (congrAdd (congrMul ((congrAdd (fst_pair _ _) (snd_pair _ _)).eqTrans (by ipra_ring)) (.eqRefl _))
      (congrAp2 powF (.eqRefl _) (fst_pair _ _)))

theorem geometric_identity (j : PTm n) : Γ ⊢[PRAAx]
    num 7*ExponentialMajorant.Gg j geometricData+pw (num 65) j ≐ pw (num 72) j := by
  have left : Γ ⊢[PRAAx] sndT geometricData*ExponentialMajorant.Gg j geometricData+pw (fstT geometricData) j ≐
      num 7*ExponentialMajorant.Gg j geometricData+pw (num 65) j :=
    congrAdd (congrMul (snd_pair _ _) (.eqRefl _)) (congrAp2 powF (.eqRefl _) (fst_pair _ _))
  have right : Γ ⊢[PRAAx] pw (fstT geometricData+sndT geometricData) j ≐ pw (num 72) j :=
    congrAp2 powF (.eqRefl _) ((congrAdd (fst_pair _ _) (snd_pair _ _)).eqTrans (by ipra_ring))
  exact left.eqSymm.eqTrans ((ExponentialMajorant.geom j geometricData).eqTrans right)

theorem geometric_zero : Γ ⊢[PRAAx] geometricPrefix (zero : PTm n) ≐ fraction one one := by
  have count : Γ ⊢[PRAAx] ExponentialMajorant.Gg (succ zero) (geometricData : PTm n) ≐ one :=
    (geometric_step zero).eqTrans
      ((congrAdd (congrMul (.eqRefl _) (ExponentialMajorant.Gg_zero geometricData)) (pw_zero (num 65))).eqTrans (by ipra_ring))
  exact RationalNonnegativePowers.fraction_congr count (pw_zero (num 72))

/-- The scalar geometric budget is tied to the real finite Gg program,
with its literal successor recurrence proved by rational representations. -/
theorem geometric_prefix_succ (j : PTm n) : Γ ⊢[PRAAx]
    geometricPrefix (succ j) ≐ add (geometricPrefix j) (powerBudget (succ j)) := by
  have hB := power_denominator_positive (Γ := Γ) j
  have hD := power_denominator_positive (Γ := Γ) (succ j)
  have rep := RationalRepresentations.represents_add (Γ := Γ) (geometricPrefix j) (powerBudget (succ j))
    (ZT.ofNat (ExponentialMajorant.Gg (succ j) geometricData)) (ZT.ofNat (pw (num 65) (succ j)))
    (pw (num 72) j) (pw (num 72) (succ j)) (fraction_represents _ _ hB) (fraction_represents _ _ hD)
  apply Prf.eqSymm
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ hD) rep (fraction_represents _ _ hD)
    (GaussianRationalHorner.positive_product _ _ hB hD) hD
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
  ipra_simps
  rw [natEq (geometric_step (Γ := Γ) (succ j)),natEq (pw_succ (Γ := Γ) (num 72) j)]
  ipra_simps
  ring

theorem geometric_bound (j : PTm n) : Γ ⊢[PRAAx]
    rationalLE (geometricPrefix j) (fraction (num 72) (num 7)) := by
  have h7 : Γ ⊢[PRAAx] le one (num 7 : PTm n) := le_of_eq_add (d := num 6) (by ipra_ring)
  have budget : Γ ⊢[PRAAx] le (num 7*ExponentialMajorant.Gg (succ j) geometricData) (pw (num 72) (succ j)) :=
    le_congr (.eqRefl _) (geometric_identity (succ j)) (le_add_right _ _)
  exact fraction_order _ _ _ _ (power_denominator_positive j) h7
    (le_congr (.eqRefl _) ((pw_succ (num 72) j).eqTrans (mul_comm _ _)) budget)


def exponentialLaw (C N K t j : PTm n) : Fm PTm n := le j K ⟶
  rationalLE (weightedNorm (stage C N K j) (j*N) t) (geometricPrefix j)
ipra_subst exponentialLaw

theorem exponential_zero (C N K t : PTm n) : Γ ⊢[PRAAx] exponentialLaw C N K t zero := by
  refine .impI ?_
  have actual := (weighted_congr (Γ := le zero K :: Γ) (GaussianRationalPolynomialExponential.stage_zero C N K)
    (zero_mul N) (.eqRefl _)).eqTrans (singleton_weighted_norm t)
  exact RationalArgmin.rationalLE_congr actual.eqSymm geometric_zero.eqSymm (RationalArgmin.reflexive _)

theorem exponential_step (C N K t j : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hNorm : Γ ⊢[PRAAx] rationalLE (weightedNorm C N t) ratio) (hj : Γ ⊢[PRAAx] lt j K)
    (ih : Γ ⊢[PRAAx] rationalLE (weightedNorm (stage C N K j) (j*N) t) (geometricPrefix j)) :
    Γ ⊢[PRAAx] rationalLE (weightedNorm (stage C N K (succ j)) (succ j*N) t) (geometricPrefix (succ j)) := by
  have padded : Γ ⊢[PRAAx] weightedNorm (leftPad (stage C N K j) N) (succ j*N) t ≐
      weightedNorm (stage C N K j) (j*N) t :=
    (weighted_congr (.eqRefl _) (show Γ ⊢[PRAAx] succ j*N ≐ N+j*N by ipra_ring) (.eqRefl _)).eqTrans
      (GaussianRationalPolynomialDilation.weighted_padding (stage C N K j) (j*N) t N
        (GaussianRationalPolynomialExponential.stage_length _ _ _ _))
  have oldBound := RationalArgmin.rationalLE_congr padded.eqSymm (.eqRefl _) ih
  have newBound := weighted_term_bound C N K t (succ j) hC hNorm hj
  have sumBound := GaussianRationalSyntheticBounds.add_monotone _ _ _ _ oldBound newBound
  have actual := GaussianRationalPolynomialDilation.weighted_added_bound (Γ := Γ)
    (leftPad (stage C N K j) N) (scaled (powerPrefix C N K (succ j)) (inverseFactorial (succ j))) (succ j*N) t
  exact RationalArgmin.rationalLE_congr
    (weighted_congr (GaussianRationalPolynomialExponential.stage_succ C N K j).eqSymm (.eqRefl _) (.eqRefl _))
    (geometric_prefix_succ j).eqSymm (RationalArgmin.transitive actual sumBound)

/-- A genuine guarded QF induction follows the SAME factorial-weighted
coefficient-buffer stage constructor. Original source length and original
coefficient norm suffice; no stage norm or recurrence is assumed. -/
theorem exponential_bound (C N K t j : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hNorm : Γ ⊢[PRAAx] rationalLE (weightedNorm C N t) ratio) (hj : Γ ⊢[PRAAx] le j K) :
    Γ ⊢[PRAAx] rationalLE (weightedNorm (stage C N K j) (j*N) t) (geometricPrefix j) := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hC.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] rationalLE (weightedNorm (Syn.shift C) (Syn.shift N) (Syn.shift t)) ratio := by
    simpa only [Fm.shift,RationalArgmin.subst_rationalLE,GaussianRationalPolynomialDilation.subst_weightedNorm,subst_ratio,Syn.shift] using hNorm.shift
  have all : Γ ⊢[PRAAx] .all (exponentialLaw (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift t) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,le_QF _ _⟩) [subst_exponentialLaw]
    · exact exponential_zero _ _ _ _
    · exact .impI (exponential_step _ _ _ _ _ cs.wk.wk ns.wk.wk Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)))
  have rule : Γ ⊢[PRAAx] exponentialLaw C N K t j := by
    simpa only [subst_exponentialLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE rule hj

theorem polynomial_bound (C N K t : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hNorm : Γ ⊢[PRAAx] rationalLE (weightedNorm C N t) ratio) : Γ ⊢[PRAAx]
    rationalLE (weightedNorm (GaussianRationalPolynomialExponential.polynomial C N K) (K*N) t)
      (fraction (num 72) (num 7)) :=
  RationalArgmin.transitive (exponential_bound C N K t K hC hNorm (le_refl _)) (geometric_bound K)

/-- The actual original source H_d discharges every norm and shape input.
The numerical cutoff K is the SAME finite exponential cutoff. -/
theorem composition_bound (d K : PTm n) : Γ ⊢[PRAAx]
    rationalLE (weightedNorm (GaussianFiniteLogarithmPolynomial.composition d K) (K*d) GaussianFiniteLogarithmWeightedNorm.point)
      (fraction (num 72) (num 7)) :=
  polynomial_bound (GaussianFiniteLogarithmPolynomial.polynomial d) d K GaussianFiniteLogarithmWeightedNorm.point
    (GaussianFiniteLogarithmPolynomial.polynomial_length d) (GaussianFiniteLogarithmWeightedNorm.logarithm_bound d)

theorem relaxed_budget : Γ ⊢[PRAAx] rationalLE (fraction (num 72) (num 7) : PTm n) (fraction (num 11) one) :=
  fraction_order _ _ _ _ (le_of_eq_add (d := num 6) (by ipra_ring)) (le_refl _)
    (le_of_eq_add (d := num 5) (by ipra_ring))
theorem composition_bound_eleven (d K : PTm n) : Γ ⊢[PRAAx]
    rationalLE (weightedNorm (GaussianFiniteLogarithmPolynomial.composition d K) (K*d) GaussianFiniteLogarithmWeightedNorm.point)
      (fraction (num 11) one) := RationalArgmin.transitive (composition_bound d K) relaxed_budget


theorem composition_geometric_bound (d K : PTm n) : Γ ⊢[PRAAx]
    rationalLE (weightedNorm (GaussianFiniteLogarithmPolynomial.composition d K) (K*d) GaussianFiniteLogarithmWeightedNorm.point)
      (geometricPrefix K) :=
  exponential_bound (GaussianFiniteLogarithmPolynomial.polynomial d) d K GaussianFiniteLogarithmWeightedNorm.point K
    (GaussianFiniteLogarithmPolynomial.polynomial_length d) (GaussianFiniteLogarithmWeightedNorm.logarithm_bound d) (le_refl _)

/-! The actual PR2 payload keeps the SAME source coefficient buffer,
its actual dilation, computed norm, finite majorant and auxiliary point. -/
def output (d K : PTm n) : PTm n := pairT (GaussianFiniteLogarithmPolynomial.composition d K)
  (pairT (dilated (GaussianFiniteLogarithmPolynomial.composition d K) (K*d) GaussianFiniteLogarithmWeightedNorm.point)
    (pairT (weightedNorm (GaussianFiniteLogarithmPolynomial.composition d K) (K*d) GaussianFiniteLogarithmWeightedNorm.point)
      (pairT (geometricPrefix K) GaussianFiniteLogarithmWeightedNorm.point)))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (d K : PTm n) : PTm n := ap2 outputF d K
ipra_subst output
ipra_subst run
theorem program_at (d K : PTm n) : Γ ⊢[PRAAx] run d K ≐ output d K := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![d,K]
theorem returned_composition (d K : PTm n) : Γ ⊢[PRAAx] fstT (run d K) ≐ GaussianFiniteLogarithmPolynomial.composition d K :=
  (program_at d K).fstE
theorem returned_tail (d K : PTm n) : Γ ⊢[PRAAx] sndT (run d K) ≐
    pairT (dilated (GaussianFiniteLogarithmPolynomial.composition d K) (K*d) GaussianFiniteLogarithmWeightedNorm.point)
      (pairT (weightedNorm (GaussianFiniteLogarithmPolynomial.composition d K) (K*d) GaussianFiniteLogarithmWeightedNorm.point)
        (pairT (geometricPrefix K) GaussianFiniteLogarithmWeightedNorm.point)) :=
  (program_at d K).sndE
theorem returned_dilation (d K : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run d K)) ≐
    dilated (GaussianFiniteLogarithmPolynomial.composition d K) (K*d) GaussianFiniteLogarithmWeightedNorm.point :=
  (returned_tail d K).fstE
theorem returned_rest (d K : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run d K)) ≐
    pairT (weightedNorm (GaussianFiniteLogarithmPolynomial.composition d K) (K*d) GaussianFiniteLogarithmWeightedNorm.point)
      (pairT (geometricPrefix K) GaussianFiniteLogarithmWeightedNorm.point) :=
  (returned_tail d K).sndE
theorem returned_norm (d K : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run d K))) ≐
    weightedNorm (GaussianFiniteLogarithmPolynomial.composition d K) (K*d) GaussianFiniteLogarithmWeightedNorm.point :=
  (returned_rest d K).fstE
theorem returned_pair (d K : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run d K))) ≐
    pairT (geometricPrefix K) (GaussianFiniteLogarithmWeightedNorm.point : PTm n) :=
  (returned_rest d K).sndE
theorem returned_geometric (d K : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run d K)))) ≐ geometricPrefix K :=
  (returned_pair d K).fstE
theorem returned_point (d K : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run d K)))) ≐ (GaussianFiniteLogarithmWeightedNorm.point : PTm n) :=
  (returned_pair d K).sndE
theorem returned_geometric_bound (d K : PTm n) : Γ ⊢[PRAAx]
    rationalLE (fstT (sndT (sndT (run d K)))) (fstT (sndT (sndT (sndT (run d K))))) :=
  RationalArgmin.rationalLE_congr (returned_norm d K).eqSymm (returned_geometric d K).eqSymm (composition_geometric_bound d K)
theorem returned_bound (d K : PTm n) : Γ ⊢[PRAAx]
    rationalLE (fstT (sndT (sndT (run d K)))) (fraction (num 72) (num 7)) :=
  RationalArgmin.rationalLE_congr (returned_norm d K).eqSymm (.eqRefl _) (composition_bound d K)
theorem returned_length (d K : PTm n) : Γ ⊢[PRAAx] length (fstT (run d K)) ≐ succ (K*d) :=
  (congrFst (returned_composition d K)).eqTrans (GaussianRationalPolynomialExponential.polynomial_length _ _ _)

theorem original_power_weighted_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 1) ⟶ rationalLE (weightedNorm (var 0) (var 1) (var 3)) ratio ⟶ le (var 4) (var 2) ⟶
      rationalLE (weightedNorm (powerPrefix (var 0) (var 1) (var 2) (var 4)) (var 4*var 1) (var 3)) (powerBudget (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (power_bound _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem original_inverse_factorial_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (qL1 (inverseFactorial (var 0)) ≐ fraction one (Products.fact (var 0))) := closeUniv 1 (inverse_factorial_norm _)
theorem original_exponential_stage_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 1) ⟶ rationalLE (weightedNorm (var 0) (var 1) (var 3)) ratio ⟶ le (var 4) (var 2) ⟶
      rationalLE (weightedNorm (stage (var 0) (var 1) (var 2) (var 4)) (var 4*var 1) (var 3)) (geometricPrefix (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (exponential_bound _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem original_finite_exponential_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ rationalLE (weightedNorm (var 0) (var 1) (var 3)) ratio ⟶
      rationalLE (weightedNorm (GaussianRationalPolynomialExponential.polynomial (var 0) (var 1) (var 2)) (var 2*var 1) (var 3))
        (fraction (num 72) (num 7))) := closeUniv 4 (.impI (.impI (polynomial_bound _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem original_logarithm_composition_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (rationalLE (weightedNorm (GaussianFiniteLogarithmPolynomial.composition (var 0) (var 1)) (var 1*var 0)
      GaussianFiniteLogarithmWeightedNorm.point) (fraction (num 72) (num 7))) := closeUniv 2 (composition_bound _ _)
theorem original_logarithm_composition_eleven_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (rationalLE (weightedNorm (GaussianFiniteLogarithmPolynomial.composition (var 0) (var 1)) (var 1*var 0)
      GaussianFiniteLogarithmWeightedNorm.point) (fraction (num 11) one)) := closeUniv 2 (composition_bound_eleven _ _)
theorem actual_weighted_exponential_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)
theorem returned_weighted_exponential_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (rationalLE (fstT (sndT (sndT (run (var 0) (var 1))))) (fraction (num 72) (num 7))) := closeUniv 2 (returned_bound _ _)
theorem returned_weighted_exponential_fields_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((length (fstT (run (var 0) (var 1))) ≐ succ (var 1*var 0)) ⋏
      rationalLE (fstT (sndT (sndT (run (var 0) (var 1))))) (fstT (sndT (sndT (sndT (run (var 0) (var 1))))))) :=
  closeUniv 2 (.andI (returned_length _ _) (returned_geometric_bound _ _))

end LeanProofs.IPRA.Analysis.GaussianFiniteExponentialWeightedNorm
