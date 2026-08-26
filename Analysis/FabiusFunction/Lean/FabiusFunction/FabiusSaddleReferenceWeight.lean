import FabiusFunction.FabiusSaddleExpansionCoefficients
import FabiusFunction.GaussianPolynomialTailAllOrders
import FabiusFunction.SaddleExpansionFiniteRemainder

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

private theorem map_exponentTruncPolynomial
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (E : ℕ → A) (L : ℕ) :
    (exponentTruncPolynomial E L).map f.toRingHom =
      exponentTruncPolynomial (fun n => f (E n)) L := by
  ext d
  simp [exponentTruncPolynomial, PowerSeries.coeff_trunc,
    coeff_exponentSeries]
  split_ifs <;> simp

private theorem map_exp_trunc
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (L : ℕ) :
    (PowerSeries.trunc L (PowerSeries.exp A)).map f.toRingHom =
      PowerSeries.trunc L (PowerSeries.exp B) := by
  ext d
  simp [PowerSeries.coeff_trunc, PowerSeries.coeff_exp]
  split_ifs <;> simp

private theorem map_finiteExpSubstitutionPolynomial
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (E : ℕ → A) (L : ℕ) :
    (finiteExpSubstitutionPolynomial E L).map f.toRingHom =
      finiteExpSubstitutionPolynomial (fun n => f (E n)) L := by
  unfold finiteExpSubstitutionPolynomial
  rw [Polynomial.map_comp, map_exp_trunc, map_exponentTruncPolynomial]

private theorem map_expCoeffTruncPolynomial
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (E : ℕ → A) (L : ℕ) :
    (expCoeffTruncPolynomial E L).map f.toRingHom =
      expCoeffTruncPolynomial (fun n => f (E n)) L := by
  unfold expCoeffTruncPolynomial
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [Polynomial.map_monomial]
  congr 1
  exact map_expCoeff f E k

private theorem map_finiteExpSubstitutionDefect
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (E : ℕ → A) (L : ℕ) :
    (finiteExpSubstitutionDefect E L).map f.toRingHom =
      finiteExpSubstitutionDefect (fun n => f (E n)) L := by
  unfold finiteExpSubstitutionDefect
  rw [Polynomial.map_sub, map_finiteExpSubstitutionPolynomial,
    map_expCoeffTruncPolynomial]

private theorem map_finiteExpSubstitutionQuotient
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (E : ℕ → A) (L : ℕ) :
    (finiteExpSubstitutionQuotient E L).map f.toRingHom =
      finiteExpSubstitutionQuotient (fun n => f (E n)) L := by
  unfold finiteExpSubstitutionQuotient
  rw [SaddleExpansion.map_iterate_divX, map_finiteExpSubstitutionDefect]

/-- For fixed order `n` and degree `d`, the map sending the saddle phase `t`
to the degree-`d` coefficient of the polynomial
`expCoeff (fun m => negativeLaplaceExponentPolynomial m t) n` is continuous.
The proof runs the same `expCoeff` recursion over the ring `C(ℝ, ℂ)` of
continuous functions and evaluates. -/
theorem continuous_negativeLaplaceExpCoeff_coeff (n d : ℕ) :
    Continuous (fun t : ℝ =>
      (expCoeff (fun m => negativeLaplaceExponentPolynomial m t) n).coeff d) := by
  let p : Polynomial C(ℝ, ℂ) :=
    expCoeff negativeLaplaceExponentPolynomialContinuous n
  let c : C(ℝ, ℂ) := p.coeff d
  have hc (t : ℝ) : c t =
      (expCoeff (fun m => negativeLaplaceExponentPolynomial m t) n).coeff d := by
    change ((expCoeff negativeLaplaceExponentPolynomialContinuous n).coeff d) t = _
    calc
      ((expCoeff negativeLaplaceExponentPolynomialContinuous n).coeff d) t =
          ((expCoeff negativeLaplaceExponentPolynomialContinuous n).map
            (ContinuousMap.evalAlgHom ℚ ℂ t).toRingHom).coeff d := by simp
      _ = (expCoeff (fun m => negativeLaplaceExponentPolynomial m t) n).coeff d := by
        change ((Polynomial.mapAlgHom (ContinuousMap.evalAlgHom ℚ ℂ t))
          (expCoeff negativeLaplaceExponentPolynomialContinuous n)).coeff d = _
        rw [map_expCoeff
          (Polynomial.mapAlgHom (ContinuousMap.evalAlgHom ℚ ℂ t))
          negativeLaplaceExponentPolynomialContinuous n]
        congr 1
        apply expCoeff_congr n
        intro m _hm
        exact negativeLaplaceExponentPolynomialContinuous_map m t
  have hfun : (c : ℝ → ℂ) = fun t : ℝ =>
      (expCoeff (fun m => negativeLaplaceExponentPolynomial m t) n).coeff d := by
    funext t
    exact hc t
  rw [← hfun]
  exact c.continuous

/-- Each such coefficient is periodic in the phase with period `1`, read off
from the periodicity of the whole polynomial `expCoeff` in
`negativeLaplaceExpCoeff_periodic`. -/
theorem negativeLaplaceExpCoeff_coeff_periodic (n d : ℕ) :
    Function.Periodic (fun t : ℝ =>
      (expCoeff (fun m => negativeLaplaceExponentPolynomial m t) n).coeff d) 1 := by
  intro t
  exact congrArg (fun p : Polynomial ℂ => p.coeff d)
    (negativeLaplaceExpCoeff_periodic n t)

/-- Continuity together with period `1` makes the phase-dependent
coefficient bounded: for fixed `n` and `d` the range of
`t ↦ (expCoeff (fun m => negativeLaplaceExponentPolynomial m t) n).coeff d`
is a bounded subset of `ℂ`.  This is the uniform coefficient bound behind
`gaussianPolynomialTailWeight_fabiusSaddleReferencePolynomial_isBigO` later
in this file. -/
theorem isBounded_range_negativeLaplaceExpCoeff_coeff (n d : ℕ) :
    Bornology.IsBounded (Set.range fun t : ℝ =>
      (expCoeff (fun m => negativeLaplaceExponentPolynomial m t) n).coeff d) :=
  (negativeLaplaceExpCoeff_coeff_periodic n d).isBounded_of_continuous
    one_ne_zero (continuous_negativeLaplaceExpCoeff_coeff n d)

private theorem negativeLaplaceExpCoeff_eq_map (n : ℕ) (t : ℝ) :
    (expCoeff negativeLaplaceExponentPolynomialContinuous n).map
        (ContinuousMap.evalAlgHom ℚ ℂ t).toRingHom =
      expCoeff (fun m => negativeLaplaceExponentPolynomial m t) n := by
  change (Polynomial.mapAlgHom (ContinuousMap.evalAlgHom ℚ ℂ t))
      (expCoeff negativeLaplaceExponentPolynomialContinuous n) = _
  calc
    _ = expCoeff (fun m =>
        (Polynomial.mapAlgHom (ContinuousMap.evalAlgHom ℚ ℂ t))
          (negativeLaplaceExponentPolynomialContinuous m)) n :=
      map_expCoeff
        (Polynomial.mapAlgHom (ContinuousMap.evalAlgHom ℚ ℂ t))
        negativeLaplaceExponentPolynomialContinuous n
    _ = _ := by
      apply expCoeff_congr n
      intro m _hm
      exact negativeLaplaceExponentPolynomialContinuous_map m t

private def negativeLaplaceFiniteExpQuotientContinuous
    (L : ℕ) : Polynomial (Polynomial C(ℝ, ℂ)) :=
  finiteExpSubstitutionQuotient
    negativeLaplaceExponentPolynomialContinuous L

private theorem negativeLaplaceFiniteExpQuotientContinuous_map
    (L : ℕ) (t : ℝ) :
    (negativeLaplaceFiniteExpQuotientContinuous L).map
        (Polynomial.mapAlgHom (ContinuousMap.evalAlgHom ℚ ℂ t)).toRingHom =
      finiteExpSubstitutionQuotient
        (fun m => negativeLaplaceExponentPolynomial m t) L := by
  unfold negativeLaplaceFiniteExpQuotientContinuous
  let f : Polynomial C(ℝ, ℂ) →ₐ[ℚ] Polynomial ℂ :=
    Polynomial.mapAlgHom (ContinuousMap.evalAlgHom ℚ ℂ t)
  change (finiteExpSubstitutionQuotient
      negativeLaplaceExponentPolynomialContinuous L).map f.toRingHom = _
  have hmap : (finiteExpSubstitutionQuotient
      negativeLaplaceExponentPolynomialContinuous L).map f.toRingHom =
      finiteExpSubstitutionQuotient
        (fun m => f (negativeLaplaceExponentPolynomialContinuous m)) L :=
    map_finiteExpSubstitutionQuotient f
      negativeLaplaceExponentPolynomialContinuous L
  calc
    _ = finiteExpSubstitutionQuotient
        (fun m => f (negativeLaplaceExponentPolynomialContinuous m)) L := hmap
    _ = _ := by
      congr 1
      funext m
      change (negativeLaplaceExponentPolynomialContinuous m).map
          (ContinuousMap.evalAlgHom ℚ ℂ t).toRingHom = _
      exact negativeLaplaceExponentPolynomialContinuous_map m t

private theorem negativeLaplaceFiniteExpQuotient_periodic (L : ℕ) :
    Function.Periodic (fun t : ℝ =>
      finiteExpSubstitutionQuotient
        (fun m => negativeLaplaceExponentPolynomial m t) L) 1 := by
  intro t
  apply congrArg (fun E : ℕ → Polynomial ℂ =>
    finiteExpSubstitutionQuotient E L)
  funext m
  exact negativeLaplaceExponentPolynomial_periodic m t

private theorem continuous_negativeLaplaceFiniteExpQuotient_coeff_coeff
    (L a d : ℕ) :
    Continuous (fun t : ℝ =>
      ((finiteExpSubstitutionQuotient
        (fun m => negativeLaplaceExponentPolynomial m t) L).coeff a).coeff d) := by
  let c : C(ℝ, ℂ) :=
    ((negativeLaplaceFiniteExpQuotientContinuous L).coeff a).coeff d
  have hc (t : ℝ) : c t =
      ((finiteExpSubstitutionQuotient
        (fun m => negativeLaplaceExponentPolynomial m t) L).coeff a).coeff d := by
    change (((negativeLaplaceFiniteExpQuotientContinuous L).coeff a).coeff d) t = _
    calc
      (((negativeLaplaceFiniteExpQuotientContinuous L).coeff a).coeff d) t =
          ((((negativeLaplaceFiniteExpQuotientContinuous L).map
            (Polynomial.mapAlgHom
              (ContinuousMap.evalAlgHom ℚ ℂ t)).toRingHom).coeff a).coeff d) := by
        simp
      _ = _ := by
        rw [negativeLaplaceFiniteExpQuotientContinuous_map]
  have hfun : (c : ℝ → ℂ) = fun t : ℝ =>
      ((finiteExpSubstitutionQuotient
        (fun m => negativeLaplaceExponentPolynomial m t) L).coeff a).coeff d := by
    funext t
    exact hc t
  rw [← hfun]
  exact c.continuous

private theorem negativeLaplaceFiniteExpQuotient_coeff_coeff_periodic
    (L a d : ℕ) :
    Function.Periodic (fun t : ℝ =>
      ((finiteExpSubstitutionQuotient
        (fun m => negativeLaplaceExponentPolynomial m t) L).coeff a).coeff d) 1 := by
  intro t
  exact congrArg (fun p : Polynomial (Polynomial ℂ) => (p.coeff a).coeff d)
    (negativeLaplaceFiniteExpQuotient_periodic L t)

private theorem isBounded_range_negativeLaplaceFiniteExpQuotient_coeff_coeff
    (L a d : ℕ) :
    Bornology.IsBounded (Set.range fun t : ℝ =>
      ((finiteExpSubstitutionQuotient
        (fun m => negativeLaplaceExponentPolynomial m t) L).coeff a).coeff d) :=
  (negativeLaplaceFiniteExpQuotient_coeff_coeff_periodic L a d).isBounded_of_continuous
    one_ne_zero
    (continuous_negativeLaplaceFiniteExpQuotient_coeff_coeff L a d)

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
    (expCoeff negativeLaplaceExponentPolynomialContinuous k).natDegree

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
      (expCoeff negativeLaplaceExponentPolynomialContinuous j).natDegree) hk

/-- A fixed-degree polynomial family with uniformly bounded coefficients has
uniformly bounded factorial Gaussian coefficient weight. -/
theorem gaussianPolynomialTailWeight_isBigO_of_degree_coeff
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

/-- The finite-exponential defect quotient, evaluated at the small parameter,
as a polynomial in the Gaussian variable. -/
noncomputable def fabiusSaddleFiniteExpQuotientPolynomial
    (L : ℕ) (t : ℝ) (eps : ℂ) : Polynomial ℂ :=
  (finiteExpSubstitutionQuotient
    (fun m => negativeLaplaceExponentPolynomial m t) L).eval
      (Polynomial.C eps)

private def fabiusSaddleFiniteExpQuotientOuterDegree (L : ℕ) : ℕ :=
  (negativeLaplaceFiniteExpQuotientContinuous L).natDegree

private def fabiusSaddleFiniteExpQuotientDegree (L : ℕ) : ℕ :=
  ∑ a ∈ Finset.range (fabiusSaddleFiniteExpQuotientOuterDegree L + 1),
    ((negativeLaplaceFiniteExpQuotientContinuous L).coeff a).natDegree

private theorem natDegree_negativeLaplaceFiniteExpQuotient_le
    (L : ℕ) (t : ℝ) :
    (finiteExpSubstitutionQuotient
      (fun m => negativeLaplaceExponentPolynomial m t) L).natDegree ≤
        fabiusSaddleFiniteExpQuotientOuterDegree L := by
  rw [← negativeLaplaceFiniteExpQuotientContinuous_map L t]
  exact Polynomial.natDegree_map_le

private theorem natDegree_negativeLaplaceFiniteExpQuotient_coeff_le
    (L a : ℕ) (t : ℝ) :
    ((finiteExpSubstitutionQuotient
      (fun m => negativeLaplaceExponentPolynomial m t) L).coeff a).natDegree ≤
        ((negativeLaplaceFiniteExpQuotientContinuous L).coeff a).natDegree := by
  have hmap := congrArg (fun p : Polynomial (Polynomial ℂ) => p.coeff a)
    (negativeLaplaceFiniteExpQuotientContinuous_map L t)
  rw [Polynomial.coeff_map] at hmap
  rw [← hmap]
  exact Polynomial.natDegree_map_le

private theorem natDegree_fabiusSaddleFiniteExpQuotientPolynomial_le
    (L : ℕ) (t : ℝ) (eps : ℂ) :
    (fabiusSaddleFiniteExpQuotientPolynomial L t eps).natDegree ≤
      fabiusSaddleFiniteExpQuotientDegree L := by
  let Q : Polynomial (Polynomial ℂ) :=
    finiteExpSubstitutionQuotient
      (fun m => negativeLaplaceExponentPolynomial m t) L
  have hQ : Q.natDegree < fabiusSaddleFiniteExpQuotientOuterDegree L + 1 :=
    Nat.lt_succ_of_le (natDegree_negativeLaplaceFiniteExpQuotient_le L t)
  unfold fabiusSaddleFiniteExpQuotientPolynomial
  change (Q.eval (Polynomial.C eps)).natDegree ≤ _
  rw [Polynomial.eval_eq_sum_range' hQ]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro a ha
  refine Polynomial.natDegree_mul_le.trans ?_
  have hcoeff := natDegree_negativeLaplaceFiniteExpQuotient_coeff_le L a t
  have hpow : (Polynomial.C eps ^ a).natDegree ≤ 0 := by
    simp
  calc
    (Q.coeff a).natDegree + (Polynomial.C eps ^ a).natDegree ≤
        ((negativeLaplaceFiniteExpQuotientContinuous L).coeff a).natDegree + 0 :=
      Nat.add_le_add hcoeff hpow
    _ = ((negativeLaplaceFiniteExpQuotientContinuous L).coeff a).natDegree :=
      Nat.add_zero _
    _ ≤ fabiusSaddleFiniteExpQuotientDegree L := by
      unfold fabiusSaddleFiniteExpQuotientDegree
      exact Finset.single_le_sum
        (fun j _hj => Nat.zero_le
          ((negativeLaplaceFiniteExpQuotientContinuous L).coeff j).natDegree) ha

private theorem negativeLaplaceFiniteExpQuotient_coeff_coeff_comp_isBigO
    {α : Type*} (l : Filter α) (L a d : ℕ) (t : α → ℝ) :
    (fun i => ((finiteExpSubstitutionQuotient
      (fun m => negativeLaplaceExponentPolynomial m (t i)) L).coeff a).coeff d)
      =O[l] (fun _i => (1 : ℂ)) := by
  obtain ⟨C, hC⟩ :=
    (isBounded_range_negativeLaplaceFiniteExpQuotient_coeff_coeff L a d).exists_norm_le
  apply IsBigO.of_bound C
  filter_upwards [] with i
  simpa using hC _ ⟨t i, rfl⟩

/-- The evaluated canonical finite-exponential defect quotient also has
uniformly bounded Gaussian tail weight for every fixed truncation order. -/
theorem gaussianPolynomialTailWeight_fabiusSaddleFiniteExpQuotientPolynomial_isBigO
    {α : Type*} (l : Filter α) (L : ℕ) (t : α → ℝ) (eps : α → ℂ)
    (heps : ∀ᶠ i in l, ‖eps i‖ ≤ 1) :
    (fun i => gaussianPolynomialTailWeight
      (fabiusSaddleFiniteExpQuotientPolynomial L (t i) (eps i))) =O[l]
        (fun _i => (1 : ℝ)) := by
  apply gaussianPolynomialTailWeight_isBigO_of_degree_coeff l
    (fabiusSaddleFiniteExpQuotientDegree L)
  · intro i
    exact natDegree_fabiusSaddleFiniteExpQuotientPolynomial_le L (t i) (eps i)
  · intro d _hd
    let Q : α → Polynomial (Polynomial ℂ) := fun i =>
      finiteExpSubstitutionQuotient
        (fun m => negativeLaplaceExponentPolynomial m (t i)) L
    have hQ (i : α) : (Q i).natDegree <
        fabiusSaddleFiniteExpQuotientOuterDegree L + 1 :=
      Nat.lt_succ_of_le
        (natDegree_negativeLaplaceFiniteExpQuotient_le L (t i))
    have hepsO : eps =O[l] (fun _i => (1 : ℂ)) := by
      apply IsBigO.of_bound 1
      filter_upwards [heps] with i hi
      simpa using hi
    have hsum :
        (fun i => ∑ a ∈
          Finset.range (fabiusSaddleFiniteExpQuotientOuterDegree L + 1),
            ((Q i).coeff a).coeff d * eps i ^ a) =O[l]
          (fun _i => (1 : ℂ)) := by
      apply IsBigO.sum
      intro a _ha
      simpa only [one_pow, one_mul] using
        (negativeLaplaceFiniteExpQuotient_coeff_coeff_comp_isBigO
          l L a d t).mul (hepsO.pow a)
    apply hsum.congr_left
    intro i
    symm
    unfold fabiusSaddleFiniteExpQuotientPolynomial
    change ((Q i).eval (Polynomial.C (eps i))).coeff d = _
    rw [Polynomial.eval_eq_sum_range' (hQ i), Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [← Polynomial.C_pow, Polynomial.coeff_mul_C]

end SaddleExpansion

end

end Fabius
