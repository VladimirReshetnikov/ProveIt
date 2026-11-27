import IPRADerivations.Analysis.RationalArithmetic.Representations.GaussianRationalReconstruction
import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.GaussianEuclideanResidualRadius
import IPRADerivations.Analysis.Polynomials.Coefficients.Norms.GaussianCoefficientNormOrder

/-!
# Listed zeros and exact radii of the actual reconstructed product

The actual backwards factor fold reaches the factor z-z at a computed
runtime index. Its zero then propagates through the remaining actual
factors by quantifier-free induction. The actual reconstructed polynomial
therefore vanishes at every listed point, including repeated and
noncanonical input codes. Original Euclidean coefficient bounds give the
exact radius A+2. Exact rational distance estimates retain independent
point and radius denominators, with no canonical original-point guard.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianReconstructionRoots

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalReconstruction
  (reconstruct factors factorsF factorData product factors_succ subst_factors)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (qzero qadd represents canonical_unique qadd_represents represents_congr represents_rescale positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric
  (bounded distanceBounded qsub qsub_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qadd_congr qmul_congr qsub_congr rescale_to)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (bound_congr bounded_sum)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra
  (equal_of_values re_add im_add re_sub im_sub re_zero im_zero)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (scale zeroCode)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Once the actual factor fold has reached zero, every later step is
zero, regardless of the remaining point codes. -/
theorem zero_after (S N z K r : PTm n)
    (h : Γ ⊢[PRAAx] factors S N z K ≐ qzero) : Γ ⊢[PRAAx] factors S N z (K+r) ≐ qzero := by
  have all : Γ ⊢[PRAAx] .all (factors (Syn.shift S) (Syn.shift N) (Syn.shift z) (Syn.shift K+var 0) ≐ qzero) := by
    ipra_qfind [subst_factors, GaussianRationalHorner.subst_qzero]
    · exact (congrAp2 factorsF (add_zero K) (.eqRefl _)).eqTrans h
    · exact (congrAp2 factorsF (add_succ _ _) (.eqRefl _)).eqTrans
        ((factors_succ _ _ _ _).eqTrans ((qmul_congr (.eqRefl _) Prf.hyp0).eqTrans
          (GaussianRationalSyntheticDivision.qmul_zero_right _)))
  ipra_simpa_inst [Fm.subst_eq,subst_factors,GaussianRationalHorner.subst_qzero,PTm.subst_add] using all.allE r

/-- The actual reverse factor fold hits its listed zero at its computed
step N-i, rather than assuming a factorization or evaluation equation. -/
theorem factor_hit_zero (S N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    factors S N (entry S i) (succ (monus N (succ i))) ≐ qzero := by
  have index : Γ ⊢[PRAAx] monus N (succ (monus N (succ i))) ≐ i :=
    (congrMonus (AnalyticNumberTheory.Totatives.split_lt hi) (.eqRefl _)).eqTrans (add_monus' _ _)
  exact (factors_succ S N (entry S i) (monus N (succ i))).eqTrans
    ((qmul_congr ((qsub_congr (.eqRefl _) (entry_congr (.eqRefl _) index)).eqTrans
      (GaussianCoefficientNormOrder.qsub_self _)) (.eqRefl _)).eqTrans
        (GaussianRationalSyntheticDivision.qmul_zero_left _))

theorem product_listed_zero (S N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    product S N (entry S i) ≐ qzero := by
  have decomposition : Γ ⊢[PRAAx] succ (monus N (succ i))+i ≐ N :=
    (AnalyticNumberTheory.Totatives.split_lt hi).eqSymm
  exact (congrAp2 factorsF decomposition.eqSymm (.eqRefl _)).eqTrans
    (zero_after S N (entry S i) (succ (monus N (succ i))) i (factor_hit_zero S N i hi))

theorem listed_root_zero (S N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    GaussianRationalHorner.evaluate (reconstruct S N N) (entry S i) ≐ qzero :=
  (GaussianRationalReconstruction.product_evaluation S N (entry S i)).eqTrans (product_listed_zero S N i hi)

/-- Original coefficient Euclidean bounds and the actual listed-zero
result give the exact source radius, with no incoming root bound. -/
theorem listed_radius (S N A i : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hA : Γ ⊢[PRAAx] le one A)
    (hC : Γ ⊢[PRAAx] GaussianEuclideanResidualRadius.coefficientBounds (reconstruct S N N) A)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx] bounded (entry S i) (A+two) one :=
  GaussianEuclideanResidualRadius.residual_radius _ _ _ _ hN hA
    (GaussianRationalReconstruction.reconstruct_length S N N)
    (GaussianRationalReconstruction.reconstruct_monic S N N) hC
    (bound_congr (listed_root_zero S N i hi).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianMonicResidualRadius.zero_bounded one one (le_refl _)))

theorem all_listed_radii (S N A : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hA : Γ ⊢[PRAAx] le one A)
    (hC : Γ ⊢[PRAAx] GaussianEuclideanResidualRadius.coefficientBounds (reconstruct S N N) A) : Γ ⊢[PRAAx]
    .all (lt (var 0) (Syn.shift N) ⟶ bounded (entry (Syn.shift S) (var 0)) (Syn.shift A+two) one) := by
  refine .allI (.impI ?_)
  have nShift : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hN.shift
  have aShift : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift A) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hA.shift
  have cShift : Γ.map Fm.shift ⊢[PRAAx] GaussianEuclideanResidualRadius.coefficientBounds
      (reconstruct (Syn.shift S) (Syn.shift N) (Syn.shift N)) (Syn.shift A) := by
    simpa only [Fm.shift,GaussianEuclideanResidualRadius.subst_coefficientBounds,
      GaussianRationalReconstruction.subst_reconstruct,Syn.shift] using hC.shift
  exact listed_radius _ _ _ _ nShift.wk aShift.wk cShift.wk Prf.hyp0

/-! Exact metric estimates for arbitrary original point codes. -/

theorem difference_chain_from_representations (z y w a b c E : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hz : Γ ⊢[PRAAx] represents z a E)
    (hy : Γ ⊢[PRAAx] represents y b E) (hw : Γ ⊢[PRAAx] represents w c E) : Γ ⊢[PRAAx]
    qadd (qsub z y) (qsub y w) ≐ qsub z w := by
  have lhs := qadd_represents _ _ _ _ _ hE
    (qsub_represents _ _ _ _ _ hE hz hy) (qsub_represents _ _ _ _ _ hE hy hw)
  have rhs := qsub_represents z w a c E hE hz hw
  apply canonical_unique _ _ _ _ (GaussianRationalHorner.qadd_canonical _ _)
    (GaussianRationalMetric.qsub_canonical _ _) hE (hrv := rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
  apply equal_of_values <;> simp only [re_add,im_add,re_sub,im_sub] <;> ring

theorem difference_chain (z y w : PTm n) : Γ ⊢[PRAAx]
    qadd (qsub z y) (qsub y w) ≐ qsub z w := by
  let E := rawDen z*rawDen y*rawDen w
  have positive : Γ ⊢[PRAAx] le one E := positive_product _ _
    (positive_product _ _ (raw_den_positive z) (raw_den_positive y)) (raw_den_positive w)
  have hz := rescale_to z (rawGaussian z) (rawDen z) (rawDen y*rawDen w) E (raw_represents (Γ := Γ) z)
    (by unfold E; ipra_ring)
  have hy := rescale_to y (rawGaussian y) (rawDen y) (rawDen z*rawDen w) E (raw_represents (Γ := Γ) y)
    (by unfold E; ipra_ring)
  have hw := rescale_to w (rawGaussian w) (rawDen w) (rawDen z*rawDen y) E (raw_represents (Γ := Γ) w)
    (by unfold E; ipra_ring)
  exact difference_chain_from_representations _ _ _ _ _ _ E positive hz hy hw

theorem distance_triangle (z y w A B C D : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hzy : Γ ⊢[PRAAx] distanceBounded z y A B)
    (hyw : Γ ⊢[PRAAx] distanceBounded y w C D) : Γ ⊢[PRAAx]
    distanceBounded z w (A*D+C*B) (B*D) :=
  bound_congr (difference_chain z y w) (.eqRefl _) (.eqRefl _)
    (bounded_sum _ _ _ _ _ _ hB hD hzy hyw)

/-- Distance to the canonical zero and norm are the same comparison even
when the original point is not its canonical recoding. -/
theorem distance_zero_iff (z A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    Fm.iff (distanceBounded z qzero A B) (bounded z A B) := by
  have d := raw_den_positive (Γ := Γ) z
  have rep := qsub_represents z qzero (rawGaussian z) zeroCode (rawDen z) d
    (raw_represents (Γ := Γ) z) (GaussianRationalHorner.zero_represents _)
  have diff : Γ ⊢[PRAAx] represents (qsub z qzero) (rawGaussian z) (rawDen z) :=
    represents_congr (.eqRefl _) (by
      apply equal_of_values <;> simp only [re_sub,im_sub,re_zero,im_zero] <;> ring) (.eqRefl _) rep
  exact (GaussianRationalMetric.bounded_iff _ _ _ _ _ d hB diff).iffTrans
    (GaussianRationalMetric.bounded_iff _ _ _ _ _ d hB (raw_represents z)).iffSymm

theorem norm_from_distance (z z0 A B C D : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hdist : Γ ⊢[PRAAx] distanceBounded z z0 A B)
    (hbase : Γ ⊢[PRAAx] bounded z0 C D) : Γ ⊢[PRAAx]
    bounded z (A*D+C*B) (B*D) :=
  (distance_zero_iff _ _ _ (positive_product _ _ hB hD)).iffMp
    (distance_triangle _ _ _ _ _ _ _ hB hD hdist ((distance_zero_iff _ _ _ hD).iffMpr hbase))

theorem reconstructed_listed_root_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (var 1) ⟶
      GaussianRationalHorner.evaluate (reconstruct (var 0) (var 1) (var 1)) (entry (var 0) (var 2)) ≐ qzero) :=
  closeUniv 3 (.impI (listed_root_zero _ _ _ Prf.hyp0))

theorem reconstructed_root_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ le one (var 2) ⟶
      GaussianEuclideanResidualRadius.coefficientBounds (reconstruct (var 0) (var 1) (var 1)) (var 2) ⟶
        lt (var 3) (var 1) ⟶ bounded (entry (var 0) (var 3)) (var 2+two) one) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (listed_radius _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem original_distance_triangle_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 4) ⟶ le one (var 6) ⟶ distanceBounded (var 0) (var 1) (var 3) (var 4) ⟶
      distanceBounded (var 1) (var 2) (var 5) (var 6) ⟶
        distanceBounded (var 0) (var 2) (var 3*var 6+var 5*var 4) (var 4*var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (distance_triangle _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem original_norm_from_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 3) ⟶ le one (var 5) ⟶ distanceBounded (var 0) (var 1) (var 2) (var 3) ⟶
      bounded (var 1) (var 4) (var 5) ⟶ bounded (var 0) (var 2*var 5+var 4*var 3) (var 3*var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (norm_from_distance _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianReconstructionRoots
