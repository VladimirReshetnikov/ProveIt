import GowersSzemeredi.Proofs10Induced
import GowersSzemeredi.Proofs10MainParameters
import GowersSzemeredi.Proofs10Extraction
import GowersSzemeredi.Proofs10Regular
import GowersSzemeredi.Proofs10Selection
import GowersSzemeredi.Proofs10Shift
import GowersSzemeredi.Proofs05_10
import GowersSzemeredi.Proofs01_03
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import GowersSzemeredi.Proofs00ExponentialBounds

/-!
# The main multifunction Bogolyubov theorem

This module proves the quantitative estimates and structural conclusion in
Gowers's Theorem 10.13.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private abbrev Theorem1013Quad (X : Type*) := Fin 4 → X

private def theorem1013QuadDomain {N : Nat} {X : Type*}
    (D : MultifunctionDomain N X) : MultifunctionDomain N (Theorem1013Quad X) where
  index q := D.index (q 0) - D.index (q 1) - D.index (q 2) + D.index (q 3)

private def theorem1013QuadPhase {N : Nat} {X : Type*}
    (phi : X → ZMod N) : Theorem1013Quad X → ZMod N :=
  fun q ↦ phi (q 0) - phi (q 1) - phi (q 2) + phi (q 3)

private def theorem1013FinFourEquiv (X : Type*) :
    (Fin 4 → X) ≃ X × X × X × X where
  toFun q := (q 0, q 1, q 2, q 3)
  invFun q := ![q.1, q.2.1, q.2.2.1, q.2.2.2]
  left_inv q := by
    funext i
    fin_cases i <;> rfl
  right_inv q := by
    rcases q with ⟨a, b, c, d⟩
    rfl

private lemma theorem1013_quad_card (X : Type*) [Fintype X] :
    Fintype.card (Theorem1013Quad X) = Fintype.card X ^ 4 := by norm_num

private lemma theorem1013_sum_fin_four {X R : Type*}
    [Fintype X] [AddCommMonoid R] (F : (Fin 4 → X) → R) :
    ∑ q, F q = ∑ a : X, ∑ b : X, ∑ c : X, ∑ d : X, F ![a, b, c, d] := by
  have h := Fintype.sum_equiv (theorem1013FinFourEquiv X) F
    (fun q : X × X × X × X ↦ F ![q.1, q.2.1, q.2.2.1, q.2.2.2])
    (fun q ↦ congrArg F ((theorem1013FinFourEquiv X).left_inv q).symm)
  simpa only [Fintype.sum_prod_type] using h

private lemma theorem1013_quad_fibre_cap {N M : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X)
    (hfibre : ∀ s, (D.fibre s).card ≤ M) (s : ZMod N) :
    ((theorem1013QuadDomain D).fibre s).card ≤
      M * Fintype.card X ^ 3 := by
  simp only [MultifunctionDomain.fibre, Finset.card_filter]
  rw [theorem1013_sum_fin_four]
  -- for fixed `a, b, c` the last coordinate ranges over one fibre of `D`
  calc _ ≤ ∑ _a : X, ∑ _b : X, ∑ _c : X, M := by
        gcongr with a _ b _ c _
        refine Eq.trans_le ?_ (hfibre (s - D.index a + D.index b + D.index c))
        simp only [MultifunctionDomain.fibre, Finset.card_filter]
        refine Finset.sum_congr rfl fun d _ => if_congr ?_ rfl rfl
        dsimp [theorem1013QuadDomain]
        constructor <;> intro h <;> linear_combination h
    _ = M * Fintype.card X ^ 3 := by simp; ring

private lemma theorem1013_quad_domain_bounds {N M : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (alpha : Real)
    (halpha : 0 < alpha) (halphaOne : alpha ≤ 1) (hM : 0 < M)
    (hfibre : ∀ s, (D.fibre s).card ≤ M)
    (hcard : (Fintype.card X : Real) = alpha * M * N) :
    Section10DomainBounds (theorem1013QuadDomain D) alpha
      (M * Fintype.card X ^ 3) := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hXReal : (0 : Real) < Fintype.card X := by
    rw [hcard]
    positivity
  have hX : 0 < Fintype.card X := by exact_mod_cast hXReal
  refine ⟨halpha, halphaOne, Nat.mul_pos hM (pow_pos hX 3), ?_, ?_⟩
  · rw [theorem1013_quad_card]
    push_cast
    rw [hcard]
    ring
  · exact theorem1013_quad_fibre_cap D hfibre

private def theorem1013ArrayEquiv (X : Type*) :
    (Fin 4 → Fin 4 → X) ≃ (Fin 16 → X) where
  toFun q := ![
    q 0 0, q 0 3, q 1 0, q 1 3, q 2 1, q 2 2, q 3 1, q 3 2,
    q 0 1, q 0 2, q 1 1, q 1 2, q 2 0, q 2 3, q 3 0, q 3 3]
  invFun v := ![
    ![v 0, v 8, v 9, v 1],
    ![v 2, v 10, v 11, v 3],
    ![v 12, v 4, v 5, v 13],
    ![v 14, v 6, v 7, v 15]]
  left_inv q := by
    funext i j
    fin_cases i <;> fin_cases j <;> rfl
  right_inv v := by
    funext i
    fin_cases i <;> rfl

private lemma theorem1013_hasEqualHalfSums_eight {G : Type*} [AddCommMonoid G]
    (f : Fin (2 * 8) → G) :
    HasEqualHalfSums f ↔
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 =
        f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 := by
  have hleft :
      (Finset.univ.filter (fun i : Fin (2 * 8) ↦ (i : Nat) < 8)) =
        {0, 1, 2, 3, 4, 5, 6, 7} := by
    decide
  have hright :
      (Finset.univ.filter (fun i : Fin (2 * 8) ↦ 8 ≤ (i : Nat))) =
        {8, 9, 10, 11, 12, 13, 14, 15} := by
    decide
  unfold HasEqualHalfSums
  rw [hleft, hright]
  simp [add_assoc]

private lemma theorem1013_array_relation {G X : Type*} [AddCommGroup G]
    (f : X → G) (q : Fin 4 → Fin 4 → X) :
    HasEqualHalfSums (k := 2) (fun i ↦
        f (q i 0) - f (q i 1) - f (q i 2) + f (q i 3)) ↔
      HasEqualHalfSums (k := 8) (fun i ↦ f (theorem1013ArrayEquiv X q i)) := by
  rw [hasEqualHalfSums_two, theorem1013_hasEqualHalfSums_eight]
  dsimp [theorem1013ArrayEquiv]
  constructor <;> intro h
  · apply sub_eq_zero.mp
    have hz := sub_eq_zero.mpr h
    convert hz using 1
    all_goals abel
  · apply sub_eq_zero.mp
    have hz := sub_eq_zero.mpr h
    convert hz using 1
    all_goals abel

private lemma theorem1013_quad_additive_count {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X) :
    domainAdditiveTupleCount (theorem1013QuadDomain D) 2 =
      domainAdditiveTupleCount D 8 := by
  unfold domainAdditiveTupleCount countWhere
  apply Finset.card_equiv (theorem1013ArrayEquiv X)
  intro q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change
    HasEqualHalfSums (k := 2) (fun i ↦
      D.index (q i 0) - D.index (q i 1) - D.index (q i 2) + D.index (q i 3)) ↔
      HasEqualHalfSums (k := 8) (fun i ↦ D.index (theorem1013ArrayEquiv X q i))
  exact theorem1013_array_relation D.index q

private lemma theorem1013_quad_phi_additive_count {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) :
    domainPhiAdditiveTupleCount (theorem1013QuadDomain D)
        (theorem1013QuadPhase phi) 2 =
      domainPhiAdditiveTupleCount D phi 8 := by
  unfold domainPhiAdditiveTupleCount countWhere
  apply Finset.card_equiv (theorem1013ArrayEquiv X)
  intro q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change
    (HasEqualHalfSums (k := 2) (fun i ↦
        D.index (q i 0) - D.index (q i 1) - D.index (q i 2) + D.index (q i 3)) ∧
      HasEqualHalfSums (k := 2) (fun i ↦
        phi (q i 0) - phi (q i 1) - phi (q i 2) + phi (q i 3))) ↔
      (HasEqualHalfSums (k := 8) (fun i ↦ D.index (theorem1013ArrayEquiv X q i)) ∧
        HasEqualHalfSums (k := 8) (fun i ↦ phi (theorem1013ArrayEquiv X q i)))
  exact and_congr (theorem1013_array_relation D.index q)
    (theorem1013_array_relation phi q)

private lemma theorem1013_quad_approx_hom {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (phi : X → ZMod N) (eta : Real)
    (happrox : DomainApproxHomOfOrder D phi eta 8) :
    DomainApproxHomOfOrder (theorem1013QuadDomain D)
      (theorem1013QuadPhase phi) eta 2 := by
  unfold DomainApproxHomOfOrder at happrox ⊢
  rw [theorem1013_quad_additive_count, theorem1013_quad_phi_additive_count]
  exact happrox

private def theorem1013DifferenceDomain {N : Nat} {X : Type*}
    (D : MultifunctionDomain N X) : MultifunctionDomain N (X × X) where
  index xy := D.index xy.1 - D.index xy.2

private lemma theorem1013_difference_fibre_function {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (s : ZMod N) :
    domainFibreCountFunction (theorem1013DifferenceDomain D) s =
      correlation (domainFibreCountFunction D) (domainFibreCountFunction D) s := by
  change
    (((theorem1013DifferenceDomain D).fibre s).card : Complex) =
      ∑ t : ZMod N,
        ((D.fibre t).card : Complex) * star ((D.fibre (t - s)).card : Complex)
  norm_cast
  -- group the pairs `(x, y)` by the index of `x`
  rw [Finset.card_eq_sum_card_fiberwise (f := fun xy : X × X ↦ D.index xy.1)
    (t := Finset.univ) (by simp)]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [← Finset.card_product]
  congr 1
  ext ⟨x, y⟩
  simp only [MultifunctionDomain.fibre, theorem1013DifferenceDomain, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_product]
  exact ⟨fun ⟨h1, h2⟩ ↦ ⟨h2, by linear_combination h2 - h1⟩,
    fun ⟨h1, h2⟩ ↦ ⟨by linear_combination h1 - h2, h1⟩⟩

private lemma theorem1013_quad_fibre_function {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (s : ZMod N) :
    domainFibreCountFunction (theorem1013QuadDomain D) s =
      correlation
        (correlation (domainFibreCountFunction D) (domainFibreCountFunction D))
        (correlation (domainFibreCountFunction D) (domainFibreCountFunction D)) s := by
  -- a quadruple `q` is the pair of pairs `((q 0, q 1), (q 2, q 3))`
  have hcard : ((theorem1013QuadDomain D).fibre s).card =
      ((theorem1013DifferenceDomain (theorem1013DifferenceDomain D)).fibre s).card := by
    refine Finset.card_equiv ((theorem1013FinFourEquiv X).trans
      (Equiv.prodAssoc X X (X × X)).symm) fun q => ?_
    simp [MultifunctionDomain.fibre, theorem1013QuadDomain, theorem1013DifferenceDomain,
      theorem1013FinFourEquiv]
    constructor <;> intro h <;> rw [← h] <;> abel
  change (((theorem1013QuadDomain D).fibre s).card : Complex) = _
  rw [hcard, ← funext (theorem1013_difference_fibre_function D)]
  exact theorem1013_difference_fibre_function _ s

private lemma theorem1013_quad_fourier {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (r : ZMod N) :
    fourier (domainFibreCountFunction (theorem1013QuadDomain D)) r =
      ((‖fourier (domainFibreCountFunction D) r‖ ^ 4 : Real) : Complex) := by
  have hfun :
      domainFibreCountFunction (theorem1013QuadDomain D) =
        correlation
          (correlation (domainFibreCountFunction D) (domainFibreCountFunction D))
          (correlation (domainFibreCountFunction D) (domainFibreCountFunction D)) := by
    funext s
    exact theorem1013_quad_fibre_function D s
  rw [hfun, identity_2_1_holds, identity_2_1_holds, Complex.star_def, Complex.mul_conj']
  norm_cast
  rw [norm_mul]
  change (‖fourier (domainFibreCountFunction D) r‖ *
      ‖star (fourier (domainFibreCountFunction D) r)‖) ^ 2 = _
  rw [norm_star]
  ring

private lemma theorem1013_fourier_energy {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) :
    (∑ r : ZMod N, ‖fourier (domainFibreCountFunction D) r‖ ^ 2) =
      (N : Real) * ∑ s : ZMod N, ((D.fibre s).card : Real) ^ 2 := by
  rw [identity_2_3_holds]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  simp [domainFibreCountFunction]

private lemma theorem1013_fibre_square_sum_le {N M : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X)
    (hfibre : ∀ s, (D.fibre s).card ≤ M) :
    (∑ s : ZMod N, ((D.fibre s).card : Real) ^ 2) ≤
      (M : Real) * Fintype.card X := by
  calc
    (∑ s : ZMod N, ((D.fibre s).card : Real) ^ 2) ≤
        ∑ s : ZMod N, (M : Real) * ((D.fibre s).card : Real) := by
      apply Finset.sum_le_sum
      intro s _
      have hs : ((D.fibre s).card : Real) ≤ M := by exact_mod_cast hfibre s
      nlinarith [show (0 : Real) ≤ (D.fibre s).card by positivity]
    _ = (M : Real) * ∑ s : ZMod N, ((D.fibre s).card : Real) := by
      exact (Finset.mul_sum Finset.univ
        (fun s : ZMod N => ((D.fibre s).card : Real)) (M : Real)).symm
    _ = (M : Real) * Fintype.card X := by
      rw [← Nat.cast_sum, theorem1013Parameters_sum_fibre_cards]

/-- Parseval and the uniform fibre cap give the large-spectrum estimate in
Theorem 10.13. -/
theorem theorem10_13_spectrum_bound {N M : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (alpha : Real)
    (halpha : 0 < alpha) (hM : 0 < M)
    (hfibre : ∀ s, (D.fibre s).card ≤ M)
    (hcard : (Fintype.card X : Real) = alpha * M * N) :
    ((domainLargeSpectrum D (section10Lambda alpha * M * N)).card : Real) ≤
      section10SpectrumBound alpha := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hlambda : 0 < section10Lambda alpha := by unfold section10Lambda; positivity
  have hbound : alpha / section10Lambda alpha ^ 2 = section10SpectrumBound alpha := by
    rw [section10Lambda, section10SpectrumBound, mul_pow, ← Real.rpow_mul_natCast halpha.le,
      Real.rpow_neg halpha.le, Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)]
    norm_num [Real.rpow_natCast]
    field_simp [ne_of_gt halpha]
  rw [← hbound, le_div_iff₀ (by positivity)]
  -- Parseval: the large spectrum carries at most the whole Fourier energy
  refine le_of_mul_le_mul_right (?_ : _ ≤ alpha * ((M : Real) ^ 2 * N ^ 2)) (by positivity)
  calc _ = ∑ _r ∈ domainLargeSpectrum D (section10Lambda alpha * M * N),
        (section10Lambda alpha * M * N) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ ∑ r ∈ domainLargeSpectrum D (section10Lambda alpha * M * N),
        ‖fourier (domainFibreCountFunction D) r‖ ^ 2 := by
        gcongr with r hr
        simpa [domainLargeSpectrum] using hr
    _ ≤ ∑ r, ‖fourier (domainFibreCountFunction D) r‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ ↦ sq_nonneg _
    _ ≤ (N : Real) * ((M : Real) * Fintype.card X) := by
        rw [theorem1013_fourier_energy]
        exact mul_le_mul_of_nonneg_left (theorem1013_fibre_square_sum_le D hfibre) hN.le
    _ = alpha * ((M : Real) ^ 2 * N ^ 2) := by rw [hcard]; ring

theorem theorem10_13_zeta_bound (alpha : Real) (halpha : 0 < alpha) :
    let k := section10SpectrumParameter alpha
    let epsilon := section10BohrRadius alpha
    section10Zeta alpha ≤
      (2 : Real) ^ (-((k : Real) + 4)) * epsilon ^ k / k :=
  theorem10_13_zeta_le_parameterRadius alpha halpha

attribute [simp] exponential_add

attribute [simp] cor57_norm_exponential

private lemma theorem1013_fourier_norm_le_card {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (r : ZMod N) :
    ‖fourier (domainFibreCountFunction D) r‖ ≤ Fintype.card X := by
  rw [fourier, ZMod.dft_apply, ← theorem1013Parameters_sum_fibre_cards D, Nat.cast_sum]
  simpa only [domainFibreCountFunction, smul_eq_mul, norm_mul, AddChar.norm_apply,
    Complex.norm_natCast, one_mul] using
      norm_sum_le Finset.univ
        (fun s : ZMod N => ZMod.stdAddChar (-(s * r)) • domainFibreCountFunction D s)

private lemma theorem1013_fourier_energy_upper {N M : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (alpha : Real)
    (hfibre : ∀ s, (D.fibre s).card ≤ M)
    (hcard : (Fintype.card X : Real) = alpha * M * N) :
    (∑ r : ZMod N, ‖fourier (domainFibreCountFunction D) r‖ ^ 2) ≤
      alpha * (M : Real) ^ 2 * (N : Real) ^ 2 := by
  rw [theorem1013_fourier_energy]
  calc
    (N : Real) * ∑ s : ZMod N, ((D.fibre s).card : Real) ^ 2 ≤
        (N : Real) * ((M : Real) * Fintype.card X) := by
      exact mul_le_mul_of_nonneg_left
        (theorem1013_fibre_square_sum_le D hfibre) (by positivity)
    _ = alpha * (M : Real) ^ 2 * (N : Real) ^ 2 := by rw [hcard]; ring

private lemma theorem1013_small_spectrum_tail {N M : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (alpha : Real)
    (hfibre : ∀ s, (D.fibre s).card ≤ M)
    (hcard : (Fintype.card X : Real) = alpha * M * N) :
    let lambda := section10Lambda alpha
    let K := domainLargeSpectrum D (lambda * M * N)
    (∑ r ∈ (Finset.univ.filter fun r : ZMod N ↦ r ∉ K),
        ‖fourier (domainFibreCountFunction D) r‖ ^ 4) ≤
      alpha * lambda ^ 2 * (M : Real) ^ 4 * (N : Real) ^ 4 := by
  intro lambda K
  -- off the large spectrum `‖ĝ r‖ ^ 4 ≤ (λ M N) ^ 2 ‖ĝ r‖ ^ 2`; then use Parseval
  calc _ ≤ ∑ r ∈ (Finset.univ.filter fun r : ZMod N ↦ r ∉ K),
        (lambda * M * N) ^ 2 * ‖fourier (domainFibreCountFunction D) r‖ ^ 2 := by
        refine Finset.sum_le_sum fun r hr ↦ ?_
        have h : ‖fourier (domainFibreCountFunction D) r‖ < lambda * M * N := by
          simpa [K, domainLargeSpectrum] using (Finset.mem_filter.mp hr).2
        nlinarith [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) h.le 2)
          (sq_nonneg ‖fourier (domainFibreCountFunction D) r‖)]
    _ ≤ (lambda * M * N) ^ 2 * (alpha * M ^ 2 * N ^ 2) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (le_trans (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) fun _ _ _ ↦ sq_nonneg _)
          (theorem1013_fourier_energy_upper D alpha hfibre hcard)) (sq_nonneg _)
    _ = _ := by ring

private lemma theorem1013_lambda_sq (alpha : Real) (halpha : 0 < alpha) :
    section10Lambda alpha ^ 2 =
      (2 : Real) ^ (-(74 : Real)) * alpha ^ (11 : Nat) := by
  unfold section10Lambda
  rw [mul_pow]
  have hpow : (alpha ^ ((11 : Real) / 2)) ^ (2 : Nat) = alpha ^ (11 : Nat) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul halpha.le]
    norm_num [Real.rpow_natCast]
  rw [hpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (show (0 : Real) ≤ 2 by norm_num)]
  norm_num

private lemma theorem1013_spectrum_bound_eq (alpha : Real) (halpha : 0 < alpha) :
    section10SpectrumBound alpha =
      alpha / section10Lambda alpha ^ 2 := by
  rw [theorem1013_lambda_sq alpha halpha]
  unfold section10SpectrumBound
  rw [Real.rpow_neg halpha.le, Real.rpow_neg (show (0 : Real) ≤ 2 by norm_num)]
  norm_num [Real.rpow_natCast]
  field_simp [ne_of_gt halpha]

private lemma theorem1013_weighted_phase_sum {N M : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (alpha : Real)
    (halpha : 0 < alpha) (hM : 0 < M)
    (hfibre : ∀ s, (D.fibre s).card ≤ M)
    (hcard : (Fintype.card X : Real) = alpha * M * N)
    (d : ZMod N)
    (hd : d ∈ bohr
      (domainLargeSpectrum D
        (section10Lambda alpha * M * N)) (section10BohrRadius alpha)) :
    (∑ r : ZMod N,
        ‖fourier (domainFibreCountFunction D) r‖ ^ 4 *
          ‖exponential (r * d) - 1‖) ≤
      4 * alpha * section10Lambda alpha ^ 2 *
        (M : Real) ^ 4 * (N : Real) ^ 4 := by
  have hlambda : 0 < section10Lambda alpha := by unfold section10Lambda; positivity
  have hepsilon := theorem10_13_bohrRadius_pos alpha halpha
  have htail := theorem1013_small_spectrum_tail D alpha hfibre hcard
  dsimp only at htail
  have hbound : section10SpectrumBound alpha * ((alpha * M * N) ^ 4 *
      (2 * Real.pi * section10BohrRadius alpha)) =
      2 * alpha * section10Lambda alpha ^ 2 * M ^ 4 * N ^ 4 := by
    rw [theorem1013_spectrum_bound_eq alpha halpha, section10BohrRadius,
      Real.rpow_neg halpha.le, Real.rpow_ofNat]
    field_simp [ne_of_gt halpha, ne_of_gt hlambda, Real.pi_ne_zero]
  have hK := theorem10_13_spectrum_bound D alpha halpha hM hfibre hcard
  set K := domainLargeSpectrum D (section10Lambda alpha * M * N)
  -- on the large spectrum use the Bohr phase bound, off it the trivial bound `2`
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ K), Finset.filter_univ_mem]
  calc _ ≤ ∑ _r ∈ K, (alpha * M * N) ^ 4 * (2 * Real.pi * section10BohrRadius alpha) +
        ∑ r ∈ Finset.univ.filter (· ∉ K), 2 * ‖fourier (domainFibreCountFunction D) r‖ ^ 4 := by
        refine add_le_add (Finset.sum_le_sum fun r hr ↦ ?_) (Finset.sum_le_sum fun r _ ↦ ?_)
        · exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _)
            (by simpa [hcard] using theorem1013_fourier_norm_le_card D r) 4)
            (bohr_phase_bound _ _ d hd r hr) (norm_nonneg _) (by positivity)
        · nlinarith [norm_exponential_sub_one_le_two (r * d),
            pow_nonneg (norm_nonneg (fourier (domainFibreCountFunction D) r)) 4]
    _ ≤ _ := by
        rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
        linarith [mul_le_mul_of_nonneg_right hK (by positivity : (0 : Real) ≤
          (alpha * M * N) ^ 4 * (2 * Real.pi * section10BohrRadius alpha))]

private lemma theorem1013_quad_shift_fourier {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (s d : ZMod N) :
    (((theorem1013QuadDomain D).fibre (s + d)).card : Complex) -
        (((theorem1013QuadDomain D).fibre s).card : Complex) =
      (N : Complex)⁻¹ * ∑ r : ZMod N,
        ((‖fourier (domainFibreCountFunction D) r‖ ^ 4 : Real) : Complex) *
          exponential (r * s) * (exponential (r * d) - 1) := by
  let h := domainFibreCountFunction (theorem1013QuadDomain D)
  change h (s + d) - h s = _
  rw [identity_2_4_holds N h (s + d), identity_2_4_holds N h s, ← mul_sub,
    ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [theorem1013_quad_fourier, mul_add, exponential_add]
  ring

private lemma theorem1013_quad_shift_bound {N M : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (alpha : Real)
    (halpha : 0 < alpha) (hM : 0 < M)
    (hfibre : ∀ s, (D.fibre s).card ≤ M)
    (hcard : (Fintype.card X : Real) = alpha * M * N)
    (s d : ZMod N)
    (hd : d ∈ bohr
      (domainLargeSpectrum D (section10Lambda alpha * M * N))
      (section10BohrRadius alpha)) :
    |(((theorem1013QuadDomain D).fibre (s + d)).card : Real) -
        ((theorem1013QuadDomain D).fibre s).card| ≤
      4 * alpha * section10Lambda alpha ^ 2 *
        (M : Real) ^ 4 * (N : Real) ^ 3 := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  push_cast
  rw [theorem1013_quad_shift_fourier, norm_mul, norm_inv, Complex.norm_natCast]
  calc _ ≤ (N : Real)⁻¹ * ∑ r : ZMod N,
        ‖fourier (domainFibreCountFunction D) r‖ ^ 4 * ‖exponential (r * d) - 1‖ := by
        gcongr
        refine (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun r _ ↦ ?_)
        simp
    _ ≤ (N : Real)⁻¹ * (4 * alpha * section10Lambda alpha ^ 2 * M ^ 4 * N ^ 4) := by
        gcongr
        exact theorem1013_weighted_phase_sum D alpha halpha hM hfibre hcard d hd
    _ = _ := by field_simp [ne_of_gt hN]

private def theorem1013Sigma (alpha : Real) : Real :=
  4 * section10Lambda alpha ^ 2 / alpha ^ 2

private lemma theorem1013_quad_invariant {N M : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (alpha : Real)
    (halpha : 0 < alpha) (hM : 0 < M)
    (hfibre : ∀ s, (D.fibre s).card ≤ M)
    (hcard : (Fintype.card X : Real) = alpha * M * N) :
    DomainInvariant (theorem1013QuadDomain D)
      (bohr (domainLargeSpectrum D (section10Lambda alpha * M * N))
        (section10BohrRadius alpha))
      (theorem1013Sigma alpha * (M * Fintype.card X ^ 3)) := by
  intro s d hd
  refine (theorem1013_quad_shift_bound D alpha halpha hM hfibre hcard s d hd).trans_eq ?_
  rw [theorem1013Sigma, hcard]
  field_simp [ne_of_gt halpha]

@[simp] private lemma theorem1013_centeredAbs_neg {N : Nat} [NeZero N]
    (x : ZMod N) : centeredAbs (-x) = centeredAbs x := by
  unfold centeredAbs
  exact ZMod.natAbs_valMinAbs_neg x

private lemma theorem1013_bohr_symmetric {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (epsilon : Real) :
    IsSymmetricModSet (bohr K epsilon) := by
  intro d
  constructor <;> intro hd
  · rw [bohr, Finset.mem_filter] at hd ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    intro r hr
    simpa only [mul_neg, theorem1013_centeredAbs_neg] using hd.2 r hr
  · have hneg : -d ∈ bohr K epsilon := hd
    rw [bohr, Finset.mem_filter] at hneg ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    intro r hr
    have := hneg.2 r hr
    simpa only [mul_neg, theorem1013_centeredAbs_neg, neg_neg] using this

private lemma theorem1013_quad_setup {N M : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (phi : X → ZMod N) (alpha : Real)
    (halpha : 0 < alpha) (halphaSixth : alpha ≤ 1 / 6) (hM : 0 < M)
    (hfibre : ∀ s, (D.fibre s).card ≤ M)
    (hcard : (Fintype.card X : Real) = alpha * M * N)
    (happrox : DomainApproxHomOfOrder D phi ((2 : Real) ^ (-(43 : Real))) 8) :
    Section10Setup (theorem1013QuadDomain D) (theorem1013QuadPhase phi)
      (bohr (domainLargeSpectrum D (section10Lambda alpha * M * N))
        (section10BohrRadius alpha)) alpha
      (M * Fintype.card X ^ 3) (theorem1013Sigma alpha)
      ((2 : Real) ^ (-(43 : Real))) :=
  ⟨theorem1013_quad_domain_bounds D alpha halpha (by linarith) hM hfibre hcard,
    by unfold theorem1013Sigma section10Lambda; positivity, by positivity,
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num),
    theorem1013_bohr_symmetric _ _,
    by simpa only [Nat.cast_mul, Nat.cast_pow] using
        theorem1013_quad_invariant D alpha halpha hM hfibre hcard,
    theorem1013_quad_approx_hom D phi _ happrox⟩

private def theorem1013Eta : Real := (2 : Real) ^ (-(43 : Real))

private def theorem1013Rho (alpha : Real) : Real := alpha ^ 2 / 32

private def theorem1013Theta : Real :=
  10 * theorem1013Eta ^ ((1 : Real) / 5)

private lemma theorem1013_theta_small :
    6 * Real.sqrt theorem1013Theta < 1 := by
  have heta : 0 ≤ theorem1013Eta := by unfold theorem1013Eta; positivity
  have h5 : theorem1013Theta ^ 5 = 100000 * theorem1013Eta := by
    rw [theorem1013Theta, mul_pow, ← Real.rpow_mul_natCast heta]
    norm_num
  have htheta : theorem1013Theta < 1 / 36 := lt_of_pow_lt_pow_left₀ 5 (by norm_num) (by
    rw [h5, theorem1013Eta, Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)]
    norm_num [Real.rpow_natCast])
  linarith [(Real.sqrt_lt' (x := theorem1013Theta) (by norm_num : (0 : Real) < 1 / 6)).mpr
    (by linarith)]

private lemma theorem1013_theta_le_eighth :
    theorem1013Theta ≤ 1 / 8 := by
  have hthetaNonneg : 0 ≤ theorem1013Theta := by
    unfold theorem1013Theta theorem1013Eta
    positivity
  have hsquare : (Real.sqrt theorem1013Theta) ^ 2 = theorem1013Theta :=
    Real.sq_sqrt hthetaNonneg
  have hsqrtNonneg := Real.sqrt_nonneg theorem1013Theta
  nlinarith [theorem1013_theta_small]

private lemma theorem1013_sigma_eq (alpha : Real) (halpha : 0 < alpha) :
    theorem1013Sigma alpha =
      (2 : Real) ^ (-(72 : Real)) * alpha ^ (9 : Nat) := by
  unfold theorem1013Sigma
  rw [theorem1013_lambda_sq alpha halpha, Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)]
  norm_num [Real.rpow_natCast]
  field_simp [ne_of_gt halpha]
  ring

private lemma theorem1013_rho_bounds (alpha : Real)
    (halpha : 0 < alpha) (halphaSixth : alpha ≤ 1 / 6) :
    0 < theorem1013Rho alpha ∧ theorem1013Rho alpha ≤ alpha / 192 ∧
      theorem1013Rho alpha ≤ alpha ^ 2 / 32 := by
  unfold theorem1013Rho
  constructor
  · positivity
  constructor
  · nlinarith [sq_nonneg alpha]
  · rfl

private lemma theorem1013_sigma_le_eta_alpha_sq (alpha : Real)
    (halpha : 0 < alpha) (halphaSixth : alpha ≤ 1 / 6) :
    theorem1013Sigma alpha ≤ theorem1013Eta * alpha ^ 2 := by
  rw [theorem1013_sigma_eq alpha halpha, theorem1013Eta]
  exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
    (pow_le_pow_of_le_one halpha.le (by linarith) (by norm_num)) (by positivity) (by positivity)

private lemma theorem1013_sigma_le_regular (alpha : Real)
    (halpha : 0 < alpha) (_halphaSixth : alpha ≤ 1 / 6) :
    theorem1013Sigma alpha ≤
      theorem1013Eta * theorem1013Rho alpha ^ 4 * alpha / 384 := by
  rw [theorem1013_sigma_eq alpha halpha]
  unfold theorem1013Eta theorem1013Rho
  rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2),
    Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)]
  norm_num [Real.rpow_natCast]
  have hpow : alpha ^ (9 : Nat) = alpha ^ 9 := rfl
  rw [hpow]
  nlinarith [pow_nonneg halpha.le 9]

private lemma theorem1013_sigma_le_extraction (alpha : Real)
    (halpha : 0 < alpha) (halphaSixth : alpha ≤ 1 / 6) :
    theorem1013Sigma alpha ≤
      theorem1013Eta * theorem1013Rho alpha * alpha ^ 2 / 16 := by
  rw [theorem1013_sigma_eq alpha halpha]
  unfold theorem1013Eta theorem1013Rho
  rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2),
    Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)]
  norm_num [Real.rpow_natCast]
  have halphaOne : alpha ≤ 1 := by linarith
  have hpow : alpha ^ (9 : Nat) ≤ alpha ^ 4 := by
    calc
      alpha ^ (9 : Nat) = alpha ^ 4 * alpha ^ 5 := by ring
      _ ≤ alpha ^ 4 * 1 := by
        gcongr
        exact pow_le_one₀ halpha.le halphaOne
      _ = alpha ^ 4 := by ring
  nlinarith [hpow]

private lemma theorem1013_sigma_lt_fibre (alpha : Real)
    (halpha : 0 < alpha) (halphaSixth : alpha ≤ 1 / 6) :
    theorem1013Sigma alpha < alpha ^ 2 / 16 := by
  have h : theorem1013Eta < 1 / 16 := by
    rw [theorem1013Eta, Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)]
    norm_num [Real.rpow_natCast]
  linarith [theorem1013_sigma_le_eta_alpha_sq alpha halpha halphaSixth,
    mul_lt_mul_of_pos_right h (sq_pos_of_pos halpha)]

private lemma section10_regular_translated_fibre_nonempty {N M : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (phi : X → ZMod N)
    (B : Finset (ZMod N)) (alpha sigma eta rho : Real)
    (x : X) (W : Finset X)
    (hsetup : Section10Setup D phi B alpha M sigma eta)
    (hregular : IsSection10RegularComponent D phi B x alpha eta rho M N W)
    (hsigma : sigma < alpha ^ 2 / 16) :
    ∀ w, w ∈ W → ∀ d, d ∈ B → (D.fibre (D.index w + d)).Nonempty := by
  intro w hw d hd
  rcases hsetup with ⟨hbounds, _, _, _, _, hinvariant, _⟩
  have hM : (0 : Real) < M := by exact_mod_cast hbounds.2.2.1
  have hsource : alpha ^ 2 * M / 16 ≤ (D.fibre (D.index w)).card := by
    simpa only [MultifunctionDomain.fibreSize] using hregular.2.2.2.2.2.1 w hw
  have htarget : (0 : Real) < (D.fibre (D.index w + d)).card := by
    linarith [(abs_le.mp (hinvariant (D.index w) d hd)).1, mul_lt_mul_of_pos_right hsigma hM]
  exact Finset.card_pos.mp (by exact_mod_cast htarget)

private lemma section10_regular_shift_regular {N M : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (phi : X → ZMod N)
    (B : Finset (ZMod N)) (alpha sigma eta rho : Real)
    (x : X) (W : Finset X)
    (hsetup : Section10Setup D phi B alpha M sigma eta)
    (hregular : IsSection10RegularComponent D phi B x alpha eta rho M N W) :
    IsSection10ShiftRegular D W B eta := by
  rcases hsetup with ⟨_, _, _, _, hsymmetric, _, _⟩
  rcases hregular with ⟨hsaturated, _, _, _, hvaries, _, hoverlap⟩
  exact ⟨hsaturated, hsymmetric, hvaries, hoverlap⟩

private def theorem1013Tail {X : Type*} (q : Theorem1013Quad X) : X × X × X :=
  (q 1, q 2, q 3)

private lemma theorem1013_exists_large_tail_fibre {X : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    (W : Finset (Theorem1013Quad X)) :
    ∃ p : X × X × X,
      (W.card : Real) ≤ (Fintype.card X : Real) ^ 3 *
        ((W.filter fun q ↦ theorem1013Tail q = p).card : Real) := by
  have hX : (0 : Real) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
  have hT : ((Finset.univ : Finset (X × X × X)).card : Real) = (Fintype.card X : Real) ^ 3 := by
    simp [Fintype.card_prod]
    ring
  obtain ⟨p, -, hp⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty
    (f := fun _ => (W.card : Real) / Fintype.card X ^ 3)
    (g := fun p => ((W.filter fun q ↦ theorem1013Tail q = p).card : Real)) (le_of_eq (by
      rw [Finset.sum_const, nsmul_eq_mul, hT, mul_div_cancel₀ _ (pow_ne_zero 3 hX.ne'),
        ← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise (s := W) (t := Finset.univ)
          (f := theorem1013Tail) fun q _ => Finset.mem_univ _]))
  exact ⟨p, (div_le_iff₀' (pow_pos hX 3)).mp hp⟩

private noncomputable def theorem1013Slice {X : Type*} [DecidableEq X]
    (W : Finset (Theorem1013Quad X)) (p : X × X × X) : Finset X :=
  (W.filter fun q ↦ theorem1013Tail q = p).image fun q ↦ q 0

private def theorem1013OfHead {X : Type*} (p : X × X × X) (y : X) :
    Theorem1013Quad X := ![y, p.1, p.2.1, p.2.2]

private lemma theorem1013_of_head_mem {X : Type*} [Fintype X] [DecidableEq X]
    (W : Finset (Theorem1013Quad X)) (p : X × X × X) (y : X)
    (hy : y ∈ theorem1013Slice W p) : theorem1013OfHead p y ∈ W := by
  rw [theorem1013Slice, Finset.mem_image] at hy
  obtain ⟨q, hq, hqy⟩ := hy
  have htail := (Finset.mem_filter.mp hq).2
  have hqeq : q = theorem1013OfHead p y := by
    funext i
    fin_cases i
    · exact hqy
    · simpa [theorem1013Tail, theorem1013OfHead] using congrArg Prod.fst htail
    · simpa [theorem1013Tail, theorem1013OfHead] using
        congrArg (fun t ↦ t.2.1) htail
    · simpa [theorem1013Tail, theorem1013OfHead] using
        congrArg (fun t ↦ t.2.2) htail
  rw [← hqeq]
  exact (Finset.mem_filter.mp hq).1

private lemma theorem1013_slice_card {X : Type*} [Fintype X] [DecidableEq X]
    (W : Finset (Theorem1013Quad X)) (p : X × X × X) :
    (theorem1013Slice W p).card =
      (W.filter fun q ↦ theorem1013Tail q = p).card := by
  refine Finset.card_image_of_injOn fun q₁ hq₁ q₂ hq₂ hzero => ?_
  have ht := (Finset.mem_filter.mp hq₁).2.trans (Finset.mem_filter.mp hq₂).2.symm
  simp only [theorem1013Tail, Prod.mk.injEq] at ht
  funext i
  fin_cases i
  exacts [hzero, ht.1, ht.2.1, ht.2.2]

/-- The proof-supported local model retains five powers of the density.
The denominator and every spectrum and Bohr parameter are unchanged. -/
def theorem_10_13_power_five : Prop :=
  forall (N M : Nat) [NeZero N] (X : Type*) [Fintype X] [DecidableEq X]
      (D : MultifunctionDomain N X) (phi : X -> ZMod N) (alpha : Real),
    0 < alpha -> alpha <= 1 / 6 -> 0 < M ->
    (forall s, (D.fibre s).card <= M) ->
    (Fintype.card X : Real) = alpha * M * N ->
    DomainApproxHomOfOrder D phi ((2 : Real) ^ (-(43 : Real))) 8 ->
    let lambda := section10Lambda alpha
    let K := domainLargeSpectrum D (lambda * M * N)
    let k := section10SpectrumParameter alpha
    let epsilon := section10BohrRadius alpha
    let zeta := section10Zeta alpha
    (K.card : Real) <= section10SpectrumBound alpha /\
      zeta <= (2 : Real) ^ (-((k : Real) + 4)) * epsilon ^ k / k /\
      exists Y : Finset X, exists psi1 : ZMod N -> ZMod N,
        alpha ^ 5 * Fintype.card X / 20000 <= Y.card /\
        HasBohrDifferenceModel D phi K zeta Y psi1

/-- Strengthen the corrected Theorem 10.13 set-size bound from
`alpha^6/20000` to `alpha^5/20000`. -/
theorem theorem_10_13_power_five_holds : theorem_10_13_power_five := by
  intro N M _ X _ _ D phi alpha halpha halphaSixth hM hfibre hcard happrox
  dsimp only
  refine ⟨theorem10_13_spectrum_bound D alpha halpha hM hfibre hcard,
    theorem10_13_zeta_bound alpha halpha, ?_⟩
  let D₄ : MultifunctionDomain N (Theorem1013Quad X) := theorem1013QuadDomain D
  let phi₄ : Theorem1013Quad X → ZMod N := theorem1013QuadPhase phi
  let K : Finset (ZMod N) :=
    domainLargeSpectrum D (section10Lambda alpha * M * N)
  let epsilon : Real := section10BohrRadius alpha
  let B : Finset (ZMod N) := bohr K epsilon
  let L : Nat := M * Fintype.card X ^ 3
  let eta : Real := theorem1013Eta
  let rho : Real := theorem1013Rho alpha
  let sigma : Real := theorem1013Sigma alpha
  let theta : Real := theorem1013Theta
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  -- Lemmas 10.3, 10.5 and 10.6 for the domain of quadruples
  have hsetup : Section10Setup D₄ phi₄ B alpha L sigma eta :=
    theorem1013_quad_setup D phi alpha halpha halphaSixth hM hfibre hcard happrox
  have hsigmaAlpha : sigma ≤ eta * alpha ^ 2 :=
    theorem1013_sigma_le_eta_alpha_sq alpha halpha halphaSixth
  obtain ⟨x, hanchor⟩ :=
    lemma_10_3_holds N (Theorem1013Quad X) D₄ phi₄ B alpha L sigma eta hsetup hsigmaAlpha
  have hrho := theorem1013_rho_bounds alpha halpha halphaSixth
  obtain ⟨W, hregular⟩ :=
    lemma_10_5_holds N (Theorem1013Quad X) D₄ phi₄ B alpha rho L sigma eta x
      hsetup hsigmaAlpha hanchor hrho.1 hrho.2.1 hrho.2.2
      (theorem1013_sigma_le_regular alpha halpha halphaSixth)
  obtain ⟨B', psi, hlocal⟩ :=
    lemma_10_6_holds N (Theorem1013Quad X) D₄ phi₄ B alpha rho L sigma eta x W
      hsetup hanchor hregular hrho.2.2
      (theorem1013_sigma_le_extraction alpha halpha halphaSixth)
  change IsSection10LocalDifferenceModel D₄ phi₄ W B B' psi theta at hlocal
  have hL : (0 : Real) < L := by exact_mod_cast hsetup.1.2.2.1
  have hWnonempty : W.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp (lt_of_lt_of_le
    (by have := hrho.1; positivity) hregular.2.2.2.1))
  have hsqrt : 6 * Real.sqrt theta < 1 := theorem1013_theta_small
  -- Lemma 10.9, Corollary 10.11 and Lemma 10.12
  have hpsi : FreimanHom 2 B' psi :=
    lemma_10_9_holds N (Theorem1013Quad X) D₄ phi₄ W B B' psi eta hWnonempty
      (section10_regular_shift_regular D₄ phi₄ B alpha sigma eta rho x W hsetup hregular)
      hlocal hsqrt
  have hK : K.Nonempty := theorem10_13_largeSpectrum_nonempty D alpha halpha halphaSixth hcard
  have hepsilon : 0 < epsilon := theorem10_13_bohrRadius_pos alpha halpha
  have hepsilonOne : epsilon ≤ 1 := theorem10_13_bohrRadius_le_one alpha halpha halphaSixth
  obtain ⟨-, psi₁, hpsi₁, hinduced⟩ := corollary_10_11_holds N K epsilon hK hepsilon
    hepsilonOne B' psi hlocal.1 (le_trans (mul_le_mul_of_nonneg_right (by linarith
      [(theorem1013_theta_le_eighth : theta ≤ 1 / 8)]) (Nat.cast_nonneg _)) hlocal.2.1) hpsi
  have hdiff := lemma_10_12_holds N (Theorem1013Quad X) D₄ phi₄
    K epsilon theta W B' psi psi₁ hK hepsilon hepsilonOne (by linarith)
    (fun w hw d hd ↦ section10_regular_translated_fibre_nonempty _ _ _ _ _ _ _ _ _ hsetup
      hregular (theorem1013_sigma_lt_fibre alpha halpha halphaSixth) w hw d (hlocal.1 hd))
    hlocal hpsi₁ hinduced
  -- by Lemma 10.7, `W₁` is most of `W`; `Y` is the slice of `W₁` over a popular tail
  let W₁ : Finset (Theorem1013Quad X) := section10RegularSet D₄ phi₄ W B' psi theta
  have hW₁lower : (1 - Real.sqrt theta) * (W.card : Real) ≤ W₁.card :=
    lemma_10_7_holds N (Theorem1013Quad X) D₄ phi₄ W B B' psi eta hlocal
  have hXpos : (0 : Real) < Fintype.card X := by rw [hcard]; positivity
  haveI : Nonempty X := Fintype.card_pos_iff.mp (by exact_mod_cast hXpos)
  obtain ⟨p, hp⟩ := theorem1013_exists_large_tail_fibre W₁
  have hYlarge : alpha ^ 5 * Fintype.card X / 20000 ≤ (theorem1013Slice W₁ p).card := by
    rw [theorem1013_slice_card]
    refine le_of_mul_le_mul_right ?_ (pow_pos hXpos 3)
    calc alpha ^ 5 * Fintype.card X / 20000 * (Fintype.card X : Real) ^ 3 ≤
        (5 / 6 : Real) * (rho ^ 2 * alpha ^ 2 * L * N / 16) := by
          simp only [rho, theorem1013Rho, L, Nat.cast_mul, Nat.cast_pow, hcard]
          linarith [(by positivity : 0 ≤ alpha ^ 9 * (M : Real) ^ 4 * N ^ 4)]
      _ ≤ (1 - Real.sqrt theta) * W.card :=
          mul_le_mul (by linarith) hregular.2.2.2.1 (by positivity) (by linarith)
      _ ≤ W₁.card := hW₁lower
      _ ≤ _ := hp.trans_eq (mul_comm _ _)
  -- the difference model on `W₁` restricts to the slice: `zeta` is small enough for `|K|`
  have hzeta := theorem10_13_zeta_le_actualSpectrumRadius alpha halpha halphaSixth K
    (theorem10_13_spectrum_bound D alpha halpha hM hfibre hcard) hK
  have hCsub : bohr K (section10Zeta alpha) ⊆
      bohr K ((2 : Real) ^ (-((K.card : Real) + 4)) * epsilon ^ K.card / K.card) := fun c hc ↦ by
    simp only [bohr, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact fun r hr ↦ (hc r hr).trans (by gcongr)
  refine ⟨theorem1013Slice W₁ p, psi₁, hYlarge,
    IsAddFreimanHom.subset (Finset.coe_subset.mpr hCsub) hpsi₁ (Set.mapsTo_univ _ _),
    fun y hy z hz hyz ↦ ?_⟩
  have hhead (f : X → ZMod N) : (f y - f p.1 - f p.2.1 + f p.2.2) -
      (f z - f p.1 - f p.2.1 + f p.2.2) = f y - f z := by abel
  have hindex : D₄.index (theorem1013OfHead p y) - D₄.index (theorem1013OfHead p z) =
      D.index y - D.index z := hhead D.index
  have hphase : phi₄ (theorem1013OfHead p y) - phi₄ (theorem1013OfHead p z) =
      phi y - phi z := hhead phi
  have h := hdiff _ (theorem1013_of_head_mem W₁ p y hy) _ (theorem1013_of_head_mem W₁ p z hz)
    (hindex ▸ hCsub hyz)
  rwa [hindex, hphase] at h

/-- The original corrected catalogue statement follows from the stronger
five-power conclusion by density monotonicity. -/
theorem theorem_10_13_holds : theorem_10_13 := by
  intro N M _ X _ _ D phi alpha halpha halphaSixth hM hfibre hcard happrox
  obtain ⟨hK, hzeta, Y, psi, hY, hmodel⟩ :=
    theorem_10_13_power_five_holds N M X D phi alpha halpha halphaSixth hM hfibre hcard happrox
  refine ⟨hK, hzeta, Y, psi, ?_, hmodel⟩
  have hαone : alpha ≤ 1 := by linarith
  have hp : alpha ^ 6 ≤ alpha ^ 5 :=
    pow_le_pow_of_le_one halpha.le hαone (by omega)
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (Fintype.card X)))
    (by norm_num : (0 : Real) ≤ 20000)).trans hY

end LeanProofs.GowersSzemeredi
