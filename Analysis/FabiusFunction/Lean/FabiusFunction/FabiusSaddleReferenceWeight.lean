import FabiusFunction.FabiusSaddleExpansionCoefficients
import FabiusFunction.GaussianPolynomialTailAllOrders

/-!
# Uniform Gaussian weight for finite Fabius saddle references

This module packages the finite reference polynomial used in the all-orders
saddle expansion and proves that its Gaussian tail weight is uniformly
bounded.  The estimate is uniform in the periodic saddle phase and in every
substitution parameter of norm at most one.
-/

set_option autoImplicit false

open Filter Asymptotics Finset

namespace Fabius

open SaddleExpansion Polynomial

noncomputable section

private def negativeLaplaceBoundedExponentJetContinuousMap'
    (n : ℕ) : C(ℝ, ℂ) where
  toFun t := (negativeLaplaceBoundedExponentJet n t : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    (contDiff_infty_negativeLaplaceBoundedExponentJet n).continuous

private def negativeLaplaceExponentPolynomialContinuous'
    (m : ℕ) : Polynomial C(ℝ, ℂ) :=
  match m with
  | 0 => 0
  | n + 1 =>
      Polynomial.C
          ((Complex.I ^ (n + 1) / ((n + 1).factorial : ℕ)) •
            negativeLaplaceBoundedExponentJetContinuousMap' n) *
            Polynomial.X ^ (n + 1) +
        Polynomial.C (ContinuousMap.const ℝ
          (Complex.I ^ (n + 3) * (negativeLaplaceJetSlope (n + 2) : ℂ) /
            ((n + 3).factorial : ℕ))) * Polynomial.X ^ (n + 3)

private theorem negativeLaplaceExponentPolynomialContinuous'_map
    (m : ℕ) (t : ℝ) :
    (negativeLaplaceExponentPolynomialContinuous' m).map
        (ContinuousMap.evalAlgHom ℚ ℂ t).toRingHom =
      negativeLaplaceExponentPolynomial m t := by
  cases m with
  | zero => simp [negativeLaplaceExponentPolynomialContinuous',
      negativeLaplaceExponentPolynomial]
  | succ n =>
      simp [negativeLaplaceExponentPolynomialContinuous',
        negativeLaplaceExponentPolynomial,
        negativeLaplaceBoundedExponentJetContinuousMap']
      rw [← Polynomial.C_mul]
      congr 1
      ring

theorem continuous_negativeLaplaceExpCoeff_coeff (n d : ℕ) :
    Continuous (fun t : ℝ =>
      (expCoeff (fun m => negativeLaplaceExponentPolynomial m t) n).coeff d) := by
  let p : Polynomial C(ℝ, ℂ) :=
    expCoeff negativeLaplaceExponentPolynomialContinuous' n
  let c : C(ℝ, ℂ) := p.coeff d
  have hc (t : ℝ) : c t =
      (expCoeff (fun m => negativeLaplaceExponentPolynomial m t) n).coeff d := by
    change ((expCoeff negativeLaplaceExponentPolynomialContinuous' n).coeff d) t = _
    calc
      ((expCoeff negativeLaplaceExponentPolynomialContinuous' n).coeff d) t =
          ((expCoeff negativeLaplaceExponentPolynomialContinuous' n).map
            (ContinuousMap.evalAlgHom ℚ ℂ t).toRingHom).coeff d := by simp
      _ = (expCoeff (fun m => negativeLaplaceExponentPolynomial m t) n).coeff d := by
        change ((Polynomial.mapAlgHom (ContinuousMap.evalAlgHom ℚ ℂ t))
          (expCoeff negativeLaplaceExponentPolynomialContinuous' n)).coeff d = _
        rw [map_expCoeff
          (Polynomial.mapAlgHom (ContinuousMap.evalAlgHom ℚ ℂ t))
          negativeLaplaceExponentPolynomialContinuous' n]
        congr 1
        apply expCoeff_congr n
        intro m _hm
        exact negativeLaplaceExponentPolynomialContinuous'_map m t
  have hfun : (c : ℝ → ℂ) = fun t : ℝ =>
      (expCoeff (fun m => negativeLaplaceExponentPolynomial m t) n).coeff d := by
    funext t
    exact hc t
  rw [← hfun]
  exact c.continuous

theorem negativeLaplaceExpCoeff_coeff_periodic (n d : ℕ) :
    Function.Periodic (fun t : ℝ =>
      (expCoeff (fun m => negativeLaplaceExponentPolynomial m t) n).coeff d) 1 := by
  intro t
  exact congrArg (fun p : Polynomial ℂ => p.coeff d)
    (negativeLaplaceExpCoeff_periodic n t)

theorem isBounded_range_negativeLaplaceExpCoeff_coeff (n d : ℕ) :
    Bornology.IsBounded (Set.range fun t : ℝ =>
      (expCoeff (fun m => negativeLaplaceExponentPolynomial m t) n).coeff d) :=
  (negativeLaplaceExpCoeff_coeff_periodic n d).isBounded_of_continuous
    one_ne_zero (continuous_negativeLaplaceExpCoeff_coeff n d)

private theorem negativeLaplaceExpCoeff_eq_map (n : ℕ) (t : ℝ) :
    (expCoeff negativeLaplaceExponentPolynomialContinuous' n).map
        (ContinuousMap.evalAlgHom ℚ ℂ t).toRingHom =
      expCoeff (fun m => negativeLaplaceExponentPolynomial m t) n := by
  change (Polynomial.mapAlgHom (ContinuousMap.evalAlgHom ℚ ℂ t))
      (expCoeff negativeLaplaceExponentPolynomialContinuous' n) = _
  calc
    _ = expCoeff (fun m =>
        (Polynomial.mapAlgHom (ContinuousMap.evalAlgHom ℚ ℂ t))
          (negativeLaplaceExponentPolynomialContinuous' m)) n :=
      map_expCoeff
        (Polynomial.mapAlgHom (ContinuousMap.evalAlgHom ℚ ℂ t))
        negativeLaplaceExponentPolynomialContinuous' n
    _ = _ := by
      apply expCoeff_congr n
      intro m _hm
      exact negativeLaplaceExponentPolynomialContinuous'_map m t

namespace SaddleExpansion

/-- The finite polynomial in the Gaussian variable obtained by truncating the
formal saddle exponential after `K` terms and substituting `eps` for its
small parameter. -/
noncomputable def fabiusSaddleReferencePolynomial
    (K : ℕ) (t : ℝ) (eps : ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range K,
    Polynomial.C (eps ^ k) *
      expCoeff (fun m => negativeLaplaceExponentPolynomial m t) k

private def fabiusSaddleReferenceDegree (K : ℕ) : ℕ :=
  ∑ k ∈ Finset.range K,
    (expCoeff negativeLaplaceExponentPolynomialContinuous' k).natDegree

private theorem natDegree_fabiusSaddleReferencePolynomial_le
    (K : ℕ) (t : ℝ) (eps : ℂ) :
    (fabiusSaddleReferencePolynomial K t eps).natDegree ≤
      fabiusSaddleReferenceDegree K := by
  unfold fabiusSaddleReferencePolynomial fabiusSaddleReferenceDegree
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [← negativeLaplaceExpCoeff_eq_map k t]
  refine Polynomial.natDegree_map_le.trans ?_
  exact Finset.single_le_sum
    (fun j _hj => Nat.zero_le
      (expCoeff negativeLaplaceExponentPolynomialContinuous' j).natDegree) hk

private theorem gaussianPolynomialTailWeight_isBigO_of_degree_coeff
    {α : Type*} (l : Filter α) (D : ℕ) (p : α → Polynomial ℂ)
    (hdeg : ∀ i, (p i).natDegree ≤ D)
    (hcoeff : ∀ d ≤ D,
      (fun i => (p i).coeff d) =O[l] (fun _i => (1 : ℂ))) :
    (fun i => gaussianPolynomialTailWeight (p i)) =O[l]
      (fun _i => (1 : ℝ)) := by
  have hsum :
      (fun i => ∑ d ∈ Finset.range (D + 1),
        ‖(p i).coeff d‖ * (8 * d.factorial : ℝ)) =O[l]
          (fun _i => (1 : ℝ)) := by
    apply IsBigO.sum
    intro d hd
    have hdD : d ≤ D := by simpa using Finset.mem_range.mp hd
    have hdO := (hcoeff d hdD).norm_left
    have hdO' : (fun i => ‖(p i).coeff d‖) =O[l]
        (fun _i => (1 : ℝ)) := by simpa using hdO
    have hc : (fun _i : α => (8 * d.factorial : ℝ)) =O[l]
        (fun _i => (1 : ℝ)) :=
      isBigO_const_const (8 * d.factorial : ℝ)
        (one_ne_zero : (1 : ℝ) ≠ 0) l
    simpa only [one_mul] using hdO'.mul hc
  apply hsum.congr_left
  intro i
  symm
  unfold gaussianPolynomialTailWeight
  rw [Finset.sum_subset (by
    intro d hd
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le
      ((Polynomial.le_natDegree_of_mem_supp d hd).trans (hdeg i)))]
  intro d _hd hnot
  have hz : (p i).coeff d = 0 := by
    simpa [Polynomial.mem_support_iff] using hnot
  simp [hz]

private theorem negativeLaplaceExpCoeff_coeff_comp_isBigO
    {α : Type*} (l : Filter α) (n d : ℕ) (t : α → ℝ) :
    (fun i =>
      (expCoeff (fun m => negativeLaplaceExponentPolynomial m (t i)) n).coeff d)
      =O[l] (fun _i => (1 : ℂ)) := by
  obtain ⟨C, hC⟩ :=
    (isBounded_range_negativeLaplaceExpCoeff_coeff n d).exists_norm_le
  apply IsBigO.of_bound C
  filter_upwards [] with i
  simpa using hC _ ⟨t i, rfl⟩

/-- A finite Fabius saddle reference polynomial has uniformly bounded
Gaussian tail weight whenever the substituted small parameter has norm at
most one eventually.  The phase `t` is arbitrary: periodicity supplies a
global coefficient bound. -/
theorem gaussianPolynomialTailWeight_fabiusSaddleReferencePolynomial_isBigO
    {α : Type*} (l : Filter α) (K : ℕ) (t : α → ℝ) (eps : α → ℂ)
    (heps : ∀ᶠ i in l, ‖eps i‖ ≤ 1) :
    (fun i => gaussianPolynomialTailWeight
      (fabiusSaddleReferencePolynomial K (t i) (eps i))) =O[l]
        (fun _i => (1 : ℝ)) := by
  apply gaussianPolynomialTailWeight_isBigO_of_degree_coeff l
    (fabiusSaddleReferenceDegree K)
  · intro i
    exact natDegree_fabiusSaddleReferencePolynomial_le K (t i) (eps i)
  · intro d _hd
    unfold fabiusSaddleReferencePolynomial
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
    apply IsBigO.sum
    intro k hk
    have hepsO : eps =O[l] (fun _i => (1 : ℂ)) := by
      apply IsBigO.of_bound 1
      filter_upwards [heps] with i hi
      simpa using hi
    simpa only [one_pow, one_mul] using
      (hepsO.pow k).mul
        (negativeLaplaceExpCoeff_coeff_comp_isBigO l k d t)

end SaddleExpansion

end

end Fabius
