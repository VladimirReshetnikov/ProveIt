import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaCoefficientNorm

/-!
# The original sampled zeta-tail polynomial has uniform coefficient mass

The actual degree L+2 buffer is dilated at the positive real radius R.
Its absolute coefficient sum is bounded independently of L and of the
original reciprocal-power sampling precision. The half-disk cutoff
condition is the same numerical 2R≤N used by the source construction.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaWeightedNorm

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaReciprocalDegreeCells (degree)
open GaussianGammaZetaCoefficientPolynomial (coefficient polynomial)
open GaussianRationalHorner (qmul)
open GaussianRationalReciprocal (power)
open GaussianRationalL1 (qL1)
open GaussianRationalPolynomialDilation (dilated weightedNorm)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianEuclideanDistanceName (fraction fraction_represents fraction_order)
open GaussianCoefficientL1 (prefixNorm)
open RationalArgmin (rationalLE)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def buffer (q N L R : PTm n) : PTm n := dilated (polynomial q N L) (degree L) (radiusPoint R one)
def budget (R N j : PTm n) : PTm n := fraction (R*R) (N*pw two j)
@[simp] theorem subst_buffer {m : ℕ} (σ : Fin n → PTm m) (q N L R : PTm n) :
    Syn.subst σ (buffer q N L R) = buffer (Syn.subst σ q) (Syn.subst σ N) (Syn.subst σ L) (Syn.subst σ R) := by simp [buffer]
@[simp] theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (R N j : PTm n) :
    Syn.subst σ (budget R N j) = budget (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ j) := by simp [budget]

theorem budget_denominator (_R N j : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le one (N*pw two j) :=
  GaussianRationalHorner.positive_product _ _ hN (GaussianFactorBudget.power_positive _ _ (le_succ_self one))

theorem power_split (a j : PTm n) : Γ ⊢[PRAAx] pw a (degree j) ≐ pw a j*a*a :=
  (pw_succ a (succ j)).eqTrans (congrMul (pw_succ a j) (.eqRefl _))

theorem native_geometric_comparison (R N j : PTm n) (hh : Γ ⊢[PRAAx] le (two*R) N) : Γ ⊢[PRAAx]
    le (pw R (degree j)*(N*pw two (succ j)))
      ((R*R)*(degree j*(pred (degree j)*pw N (pred (degree j))))) := by
  have coeff : Γ ⊢[PRAAx] le two (degree j*succ j) :=
    le_congr (by ipra_ring) (.eqRefl _) (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono
      (GaussianGammaZetaDegreeName.degree_positive j) (zero_lt_succ j))
  have base := LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono coeff (pw_le_pw j hh)
  have scaled := mul_le_mul_right (R*R*N) base
  have er := natEq (power_split (Γ := Γ) R j)
  have et := natEq (pw_succ (Γ := Γ) two j)
  have ep := natEq (GaussianProductStability.power_product (Γ := Γ) two R j)
  have eN : Γ ⊢[PRAAx] pw N (pred (degree j)) ≐ pw N j*N :=
    (congrAp2 powF (pred_succ (succ j)) (.eqRefl N)).eqTrans (pw_succ N j)
  have eD : Γ ⊢[PRAAx] pred (degree j) ≐ succ j := pred_succ (succ j)
  have en := natEq eN
  have ed := natEq eD
  exact le_congr (by apply deriveNat; ipra_simps; rw [er,et,ep]; ring)
    (by apply deriveNat; ipra_simps; rw [en,ed]; ring) scaled

theorem geometric_coefficient (q N j R : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hh : Γ ⊢[PRAAx] le (two*R) N) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qmul (coefficient q N (degree j)) (power (radiusPoint R one) (degree j))))
      (budget R N (succ j)) :=
  RationalArgmin.transitive (GaussianGammaZetaCoefficientNorm.weighted_coefficient_bound q N j R hN)
    (fraction_order _ _ _ _
      (GaussianRationalHorner.positive_product _ _ (zero_lt_succ (succ j))
        (RationalReciprocalPowerTail.potential_denominator_positive (degree j) N
          (GaussianGammaZetaDegreeName.degree_positive j) hN))
      (budget_denominator R N (succ j) hN)
      (le_congr (by ipra_ring) (.eqRefl _) (native_geometric_comparison R N j hh)))

theorem budget_congr {R N j R' N' j' : PTm n} (hR : Γ ⊢[PRAAx] R ≐ R')
    (hN : Γ ⊢[PRAAx] N ≐ N') (hj : Γ ⊢[PRAAx] j ≐ j') : Γ ⊢[PRAAx] budget R N j ≐ budget R' N' j' :=
  RationalNonnegativePowers.fraction_congr (congrMul hR hR) (congrMul hN (congrAp2 powF hj (.eqRefl _)))

theorem budget_step (R N j : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    RationalArithmetic.add (budget R N (succ j)) (budget R N (succ j)) ≐ budget R N j := by
  have hD := budget_denominator R N (succ j) hN
  have hE := budget_denominator R N j hN
  have rep := RationalRepresentations.represents_add (Γ := Γ) (budget R N (succ j)) (budget R N (succ j))
    (ZT.ofNat (R*R)) (ZT.ofNat (R*R)) (N*pw two (succ j)) (N*pw two (succ j))
    (fraction_represents _ _ hD) (fraction_represents _ _ hD)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ hE) rep (fraction_represents _ _ hE)
    (GaussianRationalHorner.positive_product _ _ hD hD) hE
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
  ipra_simps
  rw [natEq (pw_succ (Γ := Γ) two j)]
  ipra_simps
  ring

theorem degree_difference (L i : PTm n) (hi : Γ ⊢[PRAAx] le i L) : Γ ⊢[PRAAx]
    monus (degree L) i ≐ degree (monus L i) :=
  (GaussianRationalPowerExpansion.remaining_before (succ L) i (le_trans hi (le_succ_self L))).eqTrans
    (congrSucc (GaussianRationalPowerExpansion.remaining_before L i hi))

theorem entry_at (q N L R i : PTm n) (hi : Γ ⊢[PRAAx] le i (degree L)) : Γ ⊢[PRAAx]
    entry (buffer q N L R) i ≐ qmul (coefficient q N (monus (degree L) i))
      (power (radiusPoint R one) (monus (degree L) i)) :=
  (GaussianRationalPolynomialDilation.dilated_lookup _ _ _ _ hi).eqTrans
    (GaussianRationalSyntheticDivision.qmul_congr (GaussianGammaZetaCoefficientPolynomial.polynomial_lookup q N L i hi) (.eqRefl _))

theorem entry_geometric (q N L R i : PTm n) (hi : Γ ⊢[PRAAx] le i L)
    (hN : Γ ⊢[PRAAx] le one N) (hh : Γ ⊢[PRAAx] le (two*R) N) : Γ ⊢[PRAAx]
    rationalLE (qL1 (entry (buffer q N L R) i)) (budget R N (succ (monus L i))) := by
  have range : Γ ⊢[PRAAx] le i (degree L) := le_trans hi (le_of_eq_add (d := two) (by unfold degree; ipra_ring))
  have same := (entry_at q N L R i range).eqTrans
    (GaussianRationalSyntheticDivision.qmul_congr
      (GaussianGammaZetaCoefficientPolynomial.coefficient_congr (.eqRefl _) (.eqRefl _) (degree_difference L i hi))
      (congrAp2 GaussianRationalReciprocal.powerF (degree_difference L i hi) (.eqRefl _)))
  exact RationalArgmin.rationalLE_congr (GaussianCoefficientL1.qL1_congr same).eqSymm (.eqRefl _)
    (geometric_coefficient q N (monus L i) R hN hh)

def prefixLaw (q N L R i : PTm n) : Fm PTm n := le i (succ L) ⟶
  rationalLE (prefixNorm (buffer q N L R) i) (budget R N (monus (succ L) i))
@[simp] theorem subst_prefixLaw {m : ℕ} (σ : Fin n → PTm m) (q N L R i : PTm n) :
    (prefixLaw q N L R i).subst σ = prefixLaw (Syn.subst σ q) (Syn.subst σ N)
      (Syn.subst σ L) (Syn.subst σ R) (Syn.subst σ i) := by simp [prefixLaw]

theorem prefix_zero (q N L R : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] prefixLaw q N L R zero := by
  refine .impI ?_
  exact RationalArgmin.rationalLE_congr
    ((GaussianCoefficientL1.prefix_zero _).eqTrans GaussianRationalLinearProduct.scalar_zero_code.eqSymm).eqSymm
    (.eqRefl _) (fraction_order zero one (R*R) (N*pw two (monus (succ L) zero))
      (le_refl one) (budget_denominator R N _ hN.wk)
      (le_congr (by ipra_ring) (by ipra_ring) (zero_le (R*R))))

theorem prefix_step (q N L R i : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hh : Γ ⊢[PRAAx] le (two*R) N) (hi : Γ ⊢[PRAAx] le (succ i) (succ L))
    (ih : Γ ⊢[PRAAx] prefixLaw q N L R i) : Γ ⊢[PRAAx]
    rationalLE (prefixNorm (buffer q N L R) (succ i)) (budget R N (monus (succ L) (succ i))) := by
  have inside : Γ ⊢[PRAAx] le i L := (succ_monus_succ i L).eqSymm.eqTrans hi
  have old := Prf.impE ih (le_trans inside (le_succ_self L))
  have oldEq := budget_congr (Γ := Γ) (.eqRefl R) (.eqRefl N)
    (GaussianRationalPowerExpansion.remaining_before L i inside)
  have oldBound := RationalArgmin.rationalLE_congr (.eqRefl _) oldEq old
  have newBound := entry_geometric q N L R i inside hN hh
  have joined := GaussianRationalSyntheticBounds.add_monotone _ _ _ _ oldBound newBound
  have finalEq := (budget_step R N (monus L i) hN).eqTrans
    (budget_congr (.eqRefl _) (.eqRefl _) (succ_monus_succ L i).eqSymm)
  exact RationalArgmin.rationalLE_congr (GaussianCoefficientL1.prefix_succ _ _).eqSymm finalEq joined

/-- Genuine guarded QF induction over the original descending stored
coefficient indices, uniformly in original sampling precision and degree. -/
theorem prefix_bound (q N L R i : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hh : Γ ⊢[PRAAx] le (two*R) N) (hi : Γ ⊢[PRAAx] le i (succ L)) : Γ ⊢[PRAAx]
    rationalLE (prefixNorm (buffer q N L R) i) (budget R N (monus (succ L) i)) := by
  have ns : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] le (two*Syn.shift R) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hh.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift q) (Syn.shift N) (Syn.shift L) (Syn.shift R) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact prefix_zero q N L R hN
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact .impI (prefix_step _ _ _ _ _ ns.wk.wk hs.wk.wk Prf.hyp0 Prf.hyp1)
  have rule : Γ ⊢[PRAAx] prefixLaw q N L R i := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE i
  exact .impE rule hi

theorem zero_entries (q N L R : PTm n) : Γ ⊢[PRAAx]
    qL1 (entry (buffer q N L R) (succ L)) ≐ GaussianRationalSyntheticBounds.natCode zero ⋏
      qL1 (entry (buffer q N L R) (degree L)) ≐ GaussianRationalSyntheticBounds.natCode zero := by
  have linearShape : Γ ⊢[PRAAx] monus (degree L) (succ L) ≐ one :=
    (GaussianRationalPowerExpansion.remaining_before (succ L) (succ L) (le_refl _)).eqTrans
      ((congrSucc (monus_self (succ L))).eqTrans (.eqRefl _))
  have constantShape := monus_self (Γ := Γ) (degree L)
  have linearRange : Γ ⊢[PRAAx] le (succ L) (degree L) := le_succ_self (succ L)
  have lin := (entry_at q N L R (succ L) linearRange).eqTrans
    ((GaussianRationalSyntheticDivision.qmul_congr
      ((GaussianGammaZetaCoefficientPolynomial.coefficient_congr (.eqRefl _) (.eqRefl _) linearShape).eqTrans
        (GaussianGammaZetaCoefficientPolynomial.coefficient_one q N)) (.eqRefl _)).eqTrans
          (GaussianRationalSyntheticDivision.qmul_zero_left _))
  have con := (entry_at q N L R (degree L) (le_refl _)).eqTrans
    ((GaussianRationalSyntheticDivision.qmul_congr
      ((GaussianGammaZetaCoefficientPolynomial.coefficient_congr (.eqRefl _) (.eqRefl _) constantShape).eqTrans
        (GaussianGammaZetaCoefficientPolynomial.coefficient_zero q N)) (.eqRefl _)).eqTrans
          (GaussianRationalSyntheticDivision.qmul_zero_left _))
  exact .andI ((GaussianCoefficientL1.qL1_congr lin).eqTrans GaussianRationalLinearProduct.qzero_norm)
    ((GaussianCoefficientL1.qL1_congr con).eqTrans GaussianRationalLinearProduct.qzero_norm)

theorem full_norm_reduction (q N L R : PTm n) : Γ ⊢[PRAAx]
    GaussianCoefficientL1.coefficientNorm (buffer q N L R) ≐ prefixNorm (buffer q N L R) (succ L) := by
  have z := zero_entries (Γ := Γ) q N L R
  have last : Γ ⊢[PRAAx] GaussianCoefficientL1.coefficientNorm (buffer q N L R) ≐ prefixNorm (buffer q N L R) (degree L) :=
    (GaussianRationalLinearProduct.norm_length _ _ (GaussianRationalPolynomialDilation.dilated_length _ _ _)).eqTrans
      ((GaussianCoefficientL1.prefix_succ _ _).eqTrans
        ((RationalAlgebra.add_congr (.eqRefl _) z.andE₂).eqTrans
          (GaussianRationalLinearProduct.scalar_add_zero _ (RationalFiniteSum.sum_well_formed _ _ _))))
  exact last.eqTrans ((GaussianCoefficientL1.prefix_succ _ _).eqTrans
    ((RationalAlgebra.add_congr (.eqRefl _) z.andE₁).eqTrans
      (GaussianRationalLinearProduct.scalar_add_zero _ (RationalFiniteSum.sum_well_formed _ _ _))))

theorem original_tail_weighted_norm (q N L R : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hh : Γ ⊢[PRAAx] le (two*R) N) : Γ ⊢[PRAAx]
    rationalLE (weightedNorm (polynomial q N L) (degree L) (radiusPoint R one)) (fraction (R*R) N) := by
  have first := prefix_bound q N L R (succ L) hN hh (le_refl _)
  have finalEq := (budget_congr (Γ := Γ) (.eqRefl R) (.eqRefl N) (monus_self (succ L))).eqTrans
    (RationalNonnegativePowers.fraction_congr (.eqRefl (R*R))
      ((congrMul (.eqRefl N) (pw_zero two)).eqTrans (show Γ ⊢[PRAAx] N*one ≐ N by ipra_ring)))
  exact RationalArgmin.rationalLE_congr (full_norm_reduction q N L R).eqSymm finalEq first

theorem original_sampled_zeta_polynomial_weighted_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ (le (two*var 3) (var 1) ⟶
      rationalLE (weightedNorm (polynomial (var 0) (var 1) (var 2)) (degree (var 2)) (radiusPoint (var 3) one))
        (fraction (var 3*var 3) (var 1)))) :=
  closeUniv 4 (.impI (.impI (original_tail_weighted_norm _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaWeightedNorm
