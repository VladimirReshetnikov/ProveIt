import GowersSzemeredi.Proofs10Induced
import GowersSzemeredi.Proofs10MainParameters
import GowersSzemeredi.Proofs10Extraction
import GowersSzemeredi.Proofs10Regular
import GowersSzemeredi.Proofs10Selection
import GowersSzemeredi.Proofs10Shift
import GowersSzemeredi.Proofs05_10
import GowersSzemeredi.Proofs01_03
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

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
    Fintype.card (Theorem1013Quad X) = Fintype.card X ^ 4 := by
  rw [Fintype.card_congr (theorem1013FinFourEquiv X)]
  simp only [Fintype.card_prod]
  ring

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
  classical
  have hcard :
      ((theorem1013QuadDomain D).fibre s).card =
        ∑ q : Theorem1013Quad X,
          if (theorem1013QuadDomain D).index q = s then 1 else 0 := by
    simp [MultifunctionDomain.fibre]
  rw [hcard, theorem1013_sum_fin_four]
  have hone (a b c : X) :
      (∑ d : X,
        if (theorem1013QuadDomain D).index ![a, b, c, d] = s then 1 else 0) ≤ M := by
    let t : ZMod N := s - D.index a + D.index b + D.index c
    have heq :
        (∑ d : X,
          if (theorem1013QuadDomain D).index ![a, b, c, d] = s then 1 else 0) =
          (D.fibre t).card := by
      rw [show (D.fibre t).card = ∑ d : X, if D.index d = t then 1 else 0 by
        simp [MultifunctionDomain.fibre]]
      apply Finset.sum_congr rfl
      intro d _
      congr 1
      apply propext
      dsimp [theorem1013QuadDomain, t]
      constructor <;> intro h
      · rw [← h]
        abel
      · rw [h]
        abel
    rw [heq]
    exact hfibre t
  calc
    (∑ a : X, ∑ b : X, ∑ c : X, ∑ d : X,
        if (theorem1013QuadDomain D).index ![a, b, c, d] = s then 1 else 0) ≤
        ∑ _a : X, ∑ _b : X, ∑ _c : X, M := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum
      intro c _
      exact hone a b c
    _ = M * Fintype.card X ^ 3 := by
      simp
      ring

private lemma theorem1013_quad_domain_bounds {N M : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (alpha : Real)
    (halpha : 0 < alpha) (halphaOne : alpha ≤ 1) (hM : 0 < M)
    (hfibre : ∀ s, (D.fibre s).card ≤ M)
    (hcard : (Fintype.card X : Real) = alpha * M * N) :
    Section10DomainBounds (theorem1013QuadDomain D) alpha
      (M * Fintype.card X ^ 3) := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hMReal : (0 : Real) < M := by exact_mod_cast hM
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

private lemma theorem1013_hasEqualHalfSums_two {G : Type*} [AddCommMonoid G]
    (f : Fin (2 * 2) → G) :
    HasEqualHalfSums f ↔ f 0 + f 1 = f 2 + f 3 := by
  have hleft :
      (Finset.univ.filter (fun i : Fin (2 * 2) ↦ (i : Nat) < 2)) = {0, 1} := by
    decide
  have hright :
      (Finset.univ.filter (fun i : Fin (2 * 2) ↦ 2 ≤ (i : Nat))) = {2, 3} := by
    decide
  unfold HasEqualHalfSums
  rw [hleft, hright]
  simp

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
  rw [theorem1013_hasEqualHalfSums_two, theorem1013_hasEqualHalfSums_eight]
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
  classical
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
  classical
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
  classical
  change
    (((theorem1013DifferenceDomain D).fibre s).card : Complex) =
      ∑ t : ZMod N,
        ((D.fibre t).card : Complex) * star ((D.fibre (t - s)).card : Complex)
  norm_cast
  rw [show ((theorem1013DifferenceDomain D).fibre s).card =
      ∑ xy : X × X,
        if D.index xy.1 - D.index xy.2 = s then 1 else 0 by
    simp [MultifunctionDomain.fibre, theorem1013DifferenceDomain]]
  have hfibreCard (t : ZMod N) :
      (D.fibre t).card = ∑ x : X, if D.index x = t then 1 else 0 := by
    simp [MultifunctionDomain.fibre]
  simp_rw [hfibreCard]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_eq_single (D.index x)]
  · simp
    by_cases h : D.index x - D.index y = s
    · have hy : D.index y = D.index x - s := by
        rw [← h]
        abel
      simp [hy]
    · have hy : D.index y ≠ D.index x - s := by
        intro hy
        apply h
        rw [hy]
        abel
      simp [h, hy]
  · intro t _ ht
    simp [Ne.symm ht]
  · simp

private def theorem1013QuadPairEquiv (X : Type*) :
    Theorem1013Quad X ≃ (X × X) × (X × X) where
  toFun q := ((q 0, q 1), (q 2, q 3))
  invFun q := ![q.1.1, q.1.2, q.2.1, q.2.2]
  left_inv q := by
    funext i
    fin_cases i <;> rfl
  right_inv q := by
    rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    rfl

private lemma theorem1013_quad_fibre_function {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (s : ZMod N) :
    domainFibreCountFunction (theorem1013QuadDomain D) s =
      correlation
        (correlation (domainFibreCountFunction D) (domainFibreCountFunction D))
        (correlation (domainFibreCountFunction D) (domainFibreCountFunction D)) s := by
  classical
  have hcard :
      ((theorem1013QuadDomain D).fibre s).card =
        ((theorem1013DifferenceDomain (theorem1013DifferenceDomain D)).fibre s).card := by
    unfold MultifunctionDomain.fibre
    apply Finset.card_equiv (theorem1013QuadPairEquiv X)
    intro q
    simp [theorem1013QuadDomain, theorem1013DifferenceDomain,
      theorem1013QuadPairEquiv]
    constructor <;> intro h <;> rw [← h] <;> abel
  change
    (((theorem1013QuadDomain D).fibre s).card : Complex) = _
  rw [hcard]
  change domainFibreCountFunction
      (theorem1013DifferenceDomain (theorem1013DifferenceDomain D)) s = _
  calc
    domainFibreCountFunction
        (theorem1013DifferenceDomain (theorem1013DifferenceDomain D)) s =
        correlation
          (domainFibreCountFunction (theorem1013DifferenceDomain D))
          (domainFibreCountFunction (theorem1013DifferenceDomain D)) s :=
      theorem1013_difference_fibre_function (theorem1013DifferenceDomain D) s
    _ = _ := by
      apply congrArg (fun f : ZMod N → Complex ↦ correlation f f s)
      funext t
      exact theorem1013_difference_fibre_function D t

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
  rw [hfun, identity_2_1_holds, identity_2_1_holds]
  rw [Complex.star_def, Complex.mul_conj']
  norm_cast
  rw [norm_mul]
  change (‖fourier (domainFibreCountFunction D) r‖ *
      ‖star (fourier (domainFibreCountFunction D) r)‖) ^ 2 = _
  rw [norm_star]
  ring

private lemma theorem1013_sum_fibre_cards {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) :
    (∑ s : ZMod N, (D.fibre s).card) = Fintype.card X := by
  rw [Fintype.card]
  exact (Finset.card_eq_sum_card_fiberwise (s := Finset.univ)
    (t := Finset.univ) (f := D.index) (by simp)).symm

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
      rw [← Nat.cast_sum, theorem1013_sum_fibre_cards]

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
  let lambda := section10Lambda alpha
  let K := domainLargeSpectrum D (lambda * M * N)
  have hlambda : 0 < lambda := by
    dsimp [lambda, section10Lambda]
    positivity
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hMreal : (0 : Real) < M := by exact_mod_cast hM
  have hlarge (r : ZMod N) (hr : r ∈ K) :
      lambda * M * N ≤ ‖fourier (domainFibreCountFunction D) r‖ := by
    simpa [K, domainLargeSpectrum] using hr
  have hlower :
      (K.card : Real) * (lambda * M * N) ^ 2 ≤
        ∑ r : ZMod N, ‖fourier (domainFibreCountFunction D) r‖ ^ 2 := by
    calc
      (K.card : Real) * (lambda * M * N) ^ 2 =
          ∑ _r ∈ K, (lambda * M * N) ^ 2 := by simp
      _ ≤ ∑ r ∈ K, ‖fourier (domainFibreCountFunction D) r‖ ^ 2 := by
        gcongr with r hr
        exact hlarge r hr
      _ ≤ ∑ r : ZMod N, ‖fourier (domainFibreCountFunction D) r‖ ^ 2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => sq_nonneg _)
  rw [theorem1013_fourier_energy] at hlower
  have hupper := theorem1013_fibre_square_sum_le D hfibre
  have henergy :
      (K.card : Real) * (lambda * M * N) ^ 2 ≤
        alpha * (M : Real) ^ 2 * (N : Real) ^ 2 := by
    calc
      (K.card : Real) * (lambda * M * N) ^ 2 ≤
          (N : Real) * ∑ s : ZMod N, ((D.fibre s).card : Real) ^ 2 := hlower
      _ ≤ (N : Real) * ((M : Real) * Fintype.card X) := by gcongr
      _ = alpha * (M : Real) ^ 2 * (N : Real) ^ 2 := by rw [hcard]; ring
  have hcancel : (K.card : Real) * lambda ^ 2 ≤ alpha := by
    have hpositive : 0 < ((M : Real) ^ 2 * (N : Real) ^ 2) := by positivity
    have hscaled :
        ((K.card : Real) * lambda ^ 2) * ((M : Real) ^ 2 * (N : Real) ^ 2) ≤
          alpha * ((M : Real) ^ 2 * (N : Real) ^ 2) := by
      calc
        ((K.card : Real) * lambda ^ 2) * ((M : Real) ^ 2 * (N : Real) ^ 2) =
            (K.card : Real) * (lambda * M * N) ^ 2 := by ring
        _ ≤ alpha * (M : Real) ^ 2 * (N : Real) ^ 2 := henergy
        _ = alpha * ((M : Real) ^ 2 * (N : Real) ^ 2) := by ring
    exact le_of_mul_le_mul_right hscaled hpositive
  have hlambda_sq : lambda ^ 2 = (2 : Real) ^ (-(74 : Real)) * alpha ^ 11 := by
    dsimp [lambda, section10Lambda]
    rw [mul_pow]
    have hpow : (alpha ^ ((11 : Real) / 2)) ^ (2 : Nat) = alpha ^ 11 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul halpha.le]
      norm_num
    rw [hpow]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (show (0 : Real) ≤ 2 by norm_num)]
    norm_num
  have hraw : (K.card : Real) ≤ alpha / lambda ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hlambda)).2 hcancel
  change (K.card : Real) ≤ section10SpectrumBound alpha
  calc
    (K.card : Real) ≤ alpha / lambda ^ 2 := hraw
    _ = section10SpectrumBound alpha := by
      rw [hlambda_sq]
      unfold section10SpectrumBound
      rw [Real.rpow_neg (show (0 : Real) ≤ 2 by norm_num),
        Real.rpow_neg halpha.le]
      norm_num [Real.rpow_natCast]
      field_simp [ne_of_gt halpha]

private lemma theorem1013_bohr_radius_eq (alpha : Real) (halpha : 0 < alpha) :
    section10BohrRadius alpha =
      (2 : Real) ^ (-(148 : Real)) * alpha ^ (18 : Nat) / Real.pi := by
  have htwo :
      ((2 : Real) ^ (-(37 : Real))) ^ (4 : Nat) =
        (2 : Real) ^ (-(148 : Real)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (show (0 : Real) ≤ 2 by norm_num)]
    norm_num
  have halphaFour :
      (alpha ^ ((11 : Real) / 2)) ^ (4 : Nat) = alpha ^ (22 : Nat) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul halpha.le]
    norm_num [Real.rpow_natCast]
  have halphaCombine :
      alpha ^ (-(4 : Real)) * alpha ^ (22 : Nat) = alpha ^ (18 : Nat) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add halpha]
    norm_num [Real.rpow_natCast]
  unfold section10BohrRadius section10Lambda
  rw [mul_pow, htwo, halphaFour]
  calc
    alpha ^ (-(4 : Real)) *
          ((2 : Real) ^ (-(148 : Real)) * alpha ^ (22 : Nat)) / Real.pi =
        (2 : Real) ^ (-(148 : Real)) *
          (alpha ^ (-(4 : Real)) * alpha ^ (22 : Nat)) / Real.pi := by ring
    _ = (2 : Real) ^ (-(148 : Real)) * alpha ^ (18 : Nat) / Real.pi := by
      rw [halphaCombine]

private lemma theorem1013_bohr_radius_lower (alpha : Real) (halpha : 0 < alpha) :
    (2 : Real) ^ (-(150 : Real)) * alpha ^ (18 : Nat) ≤
      section10BohrRadius alpha := by
  rw [theorem1013_bohr_radius_eq alpha halpha]
  have hpow : 0 ≤ alpha ^ (18 : Nat) := by positivity
  have hpi : (0 : Real) < Real.pi := Real.pi_pos
  have hrecip : (1 : Real) / 4 ≤ 1 / Real.pi :=
    one_div_le_one_div_of_le hpi Real.pi_le_four
  have hcoeff :
      (2 : Real) ^ (-(150 : Real)) ≤
        (2 : Real) ^ (-(148 : Real)) / Real.pi := by
    calc
      (2 : Real) ^ (-(150 : Real)) =
          (2 : Real) ^ (-(148 : Real)) * (1 / 4) := by
        rw [show (1 / 4 : Real) = (2 : Real) ^ (-(2 : Real)) by
          norm_num [Real.rpow_neg, Real.rpow_two]]
        rw [← Real.rpow_add (show (0 : Real) < 2 by norm_num)]
        norm_num
      _ ≤ (2 : Real) ^ (-(148 : Real)) * (1 / Real.pi) := by gcongr
      _ = (2 : Real) ^ (-(148 : Real)) / Real.pi := by ring
  calc
    (2 : Real) ^ (-(150 : Real)) * alpha ^ (18 : Nat) ≤
        ((2 : Real) ^ (-(148 : Real)) / Real.pi) * alpha ^ (18 : Nat) := by
      gcongr
    _ = (2 : Real) ^ (-(148 : Real)) * alpha ^ (18 : Nat) / Real.pi := by ring

/-- The corrected radius in Theorem 10.13 is small enough for the induced
Bohr homomorphism lemma. -/
theorem theorem10_13_zeta_bound (alpha : Real) (halpha : 0 < alpha) :
    let k := section10SpectrumParameter alpha
    let epsilon := section10BohrRadius alpha
    section10Zeta alpha ≤
      (2 : Real) ^ (-((k : Real) + 4)) * epsilon ^ k / k := by
  dsimp only
  let k := section10SpectrumParameter alpha
  let a : Real := (2 : Real) ^ (-(150 : Real)) * alpha ^ (18 : Nat)
  have hboundPos : 0 < section10SpectrumBound alpha := by
    unfold section10SpectrumBound
    positivity
  have hk : 0 < k := by
    dsimp [k, section10SpectrumParameter]
    exact Nat.ceil_pos.mpr hboundPos
  have hkReal : (1 : Real) ≤ k := by exact_mod_cast hk
  have haPos : 0 < a := by
    dsimp [a]
    positivity
  have hae : a ≤ section10BohrRadius alpha := by
    exact theorem1013_bohr_radius_lower alpha halpha
  have hcoeff :
      (2 : Real) ^ (-(155 : Real) * (k : Real)) ≤
        (2 : Real) ^ (-((k : Real) + 4)) *
          ((2 : Real) ^ (-(150 : Real))) ^ k := by
    rw [← Real.rpow_natCast,
      ← Real.rpow_mul (show (0 : Real) ≤ 2 by norm_num),
      ← Real.rpow_add (show (0 : Real) < 2 by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  have halphaPow :
      (alpha ^ (18 : Nat)) ^ k = alpha ^ (18 * k) := by
    rw [pow_mul]
  have hcoarse :
      (2 : Real) ^ (-(155 : Real) * (k : Real)) * alpha ^ (18 * k) ≤
        (2 : Real) ^ (-((k : Real) + 4)) * a ^ k := by
    calc
      (2 : Real) ^ (-(155 : Real) * (k : Real)) * alpha ^ (18 * k) ≤
          ((2 : Real) ^ (-((k : Real) + 4)) *
            ((2 : Real) ^ (-(150 : Real))) ^ k) * alpha ^ (18 * k) := by
        gcongr
      _ = (2 : Real) ^ (-((k : Real) + 4)) * a ^ k := by
        dsimp [a]
        rw [mul_pow, halphaPow]
        ring
  have hpow : a ^ k ≤ section10BohrRadius alpha ^ k :=
    pow_le_pow_left₀ haPos.le hae k
  unfold section10Zeta
  dsimp only [section10SpectrumParameter] at k ⊢
  change
    (2 : Real) ^ (-(155 : Real) * (k : Real)) * alpha ^ (18 * k) / k ≤
      (2 : Real) ^ (-((k : Real) + 4)) * section10BohrRadius alpha ^ k / k
  calc
    (2 : Real) ^ (-(155 : Real) * (k : Real)) * alpha ^ (18 * k) / k ≤
        ((2 : Real) ^ (-((k : Real) + 4)) * a ^ k) / k := by gcongr
    _ ≤ (2 : Real) ^ (-((k : Real) + 4)) *
        section10BohrRadius alpha ^ k / k := by gcongr

@[simp] private lemma theorem1013_exponential_add {N : Nat} [NeZero N]
    (x y : ZMod N) : exponential (x + y) = exponential x * exponential y := by
  exact AddChar.map_add_eq_mul (ZMod.stdAddChar (N := N)) x y

@[simp] private lemma theorem1013_norm_exponential {N : Nat} [NeZero N]
    (x : ZMod N) : ‖exponential x‖ = 1 := by
  exact (ZMod.stdAddChar (N := N)).norm_apply x

private lemma theorem1013_exponential_eq_exp_valMinAbs {N : Nat} [NeZero N]
    (x : ZMod N) :
    exponential x =
      Complex.exp (Complex.I * (2 * Real.pi * (x.valMinAbs : Real) / N : Real)) := by
  calc
    exponential x = ZMod.stdAddChar ((x.valMinAbs : Int) : ZMod N) := by
      simp [exponential]
    _ = Complex.exp (2 * Real.pi * Complex.I * (x.valMinAbs : Int) / N) :=
      ZMod.stdAddChar_coe x.valMinAbs
    _ = Complex.exp
        (Complex.I * (2 * Real.pi * (x.valMinAbs : Real) / N : Real)) := by
      congr 1
      push_cast
      ring

private lemma theorem1013_norm_exponential_sub_one_le {N : Nat} [NeZero N]
    (x : ZMod N) :
    ‖exponential x - 1‖ ≤ 2 * Real.pi * centeredAbs x / N := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have habsval : |(x.valMinAbs : Real)| = (centeredAbs x : Real) := by
    rw [centeredAbs, ← Int.cast_abs, Int.abs_eq_natAbs]
    rfl
  rw [theorem1013_exponential_eq_exp_valMinAbs]
  calc
    ‖Complex.exp
        (Complex.I * (2 * Real.pi * (x.valMinAbs : Real) / N : Real)) - 1‖ ≤
        ‖2 * Real.pi * (x.valMinAbs : Real) / N‖ :=
      Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * centeredAbs x / N := by
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : Real) ≤ 2),
        abs_of_pos Real.pi_pos, habsval, abs_of_pos hN]

private lemma theorem1013_bohr_phase_bound {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (epsilon : Real) (d : ZMod N)
    (hd : d ∈ bohr K epsilon) (r : ZMod N) (hr : r ∈ K) :
    ‖exponential (r * d) - 1‖ ≤ 2 * Real.pi * epsilon := by
  rw [bohr, Finset.mem_filter] at hd
  have hcenter := hd.2 r hr
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  calc
    ‖exponential (r * d) - 1‖ ≤
        2 * Real.pi * centeredAbs (r * d) / N :=
      theorem1013_norm_exponential_sub_one_le (r * d)
    _ ≤ 2 * Real.pi * epsilon := by
      apply (div_le_iff₀ hN).2
      nlinarith [Real.pi_pos]

private lemma theorem1013_norm_exponential_sub_one_le_two {N : Nat} [NeZero N]
    (x : ZMod N) : ‖exponential x - 1‖ ≤ 2 := by
  calc
    ‖exponential x - 1‖ ≤ ‖exponential x‖ + ‖(1 : Complex)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [theorem1013_norm_exponential]

private lemma theorem1013_fourier_norm_le_card {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (r : ZMod N) :
    ‖fourier (domainFibreCountFunction D) r‖ ≤ Fintype.card X := by
  rw [fourier, ZMod.dft_apply]
  calc
    ‖∑ s : ZMod N,
        ZMod.stdAddChar (-(s * r)) • domainFibreCountFunction D s‖ ≤
        ∑ s : ZMod N,
          ‖ZMod.stdAddChar (-(s * r)) • domainFibreCountFunction D s‖ :=
      norm_sum_le _ _
    _ = ∑ s : ZMod N, ((D.fibre s).card : Real) := by
      apply Finset.sum_congr rfl
      intro s _
      simp [domainFibreCountFunction]
    _ = Fintype.card X := by
      rw [← Nat.cast_sum, theorem1013_sum_fibre_cards]

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
  dsimp only
  let lambda := section10Lambda alpha
  let K := domainLargeSpectrum D (lambda * M * N)
  have hterm (r : ZMod N) (hr : r ∉ K) :
      ‖fourier (domainFibreCountFunction D) r‖ ^ 4 ≤
        (lambda * M * N) ^ 2 *
          ‖fourier (domainFibreCountFunction D) r‖ ^ 2 := by
    have hrlt : ‖fourier (domainFibreCountFunction D) r‖ < lambda * M * N := by
      simpa [K, domainLargeSpectrum] using hr
    calc
      ‖fourier (domainFibreCountFunction D) r‖ ^ 4 =
          ‖fourier (domainFibreCountFunction D) r‖ ^ 2 *
            ‖fourier (domainFibreCountFunction D) r‖ ^ 2 := by ring
      _ ≤ (lambda * M * N) ^ 2 *
          ‖fourier (domainFibreCountFunction D) r‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) hrlt.le 2) (sq_nonneg _)
  calc
    (∑ r ∈ (Finset.univ.filter fun r : ZMod N ↦ r ∉ K),
        ‖fourier (domainFibreCountFunction D) r‖ ^ 4) ≤
        ∑ r ∈ (Finset.univ.filter fun r : ZMod N ↦ r ∉ K),
          (lambda * M * N) ^ 2 *
            ‖fourier (domainFibreCountFunction D) r‖ ^ 2 := by
      gcongr with r hr
      exact hterm r (Finset.mem_filter.mp hr).2
    _ = (lambda * M * N) ^ 2 *
        ∑ r ∈ (Finset.univ.filter fun r : ZMod N ↦ r ∉ K),
          ‖fourier (domainFibreCountFunction D) r‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ (lambda * M * N) ^ 2 *
        ∑ r : ZMod N, ‖fourier (domainFibreCountFunction D) r‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ ↦ sq_nonneg _)
      · positivity
    _ ≤ (lambda * M * N) ^ 2 *
        (alpha * (M : Real) ^ 2 * (N : Real) ^ 2) := by
      gcongr
      exact theorem1013_fourier_energy_upper D alpha hfibre hcard
    _ = alpha * lambda ^ 2 * (M : Real) ^ 4 * (N : Real) ^ 4 := by ring

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
  let lambda := section10Lambda alpha
  let K := domainLargeSpectrum D (lambda * M * N)
  let epsilon := section10BohrRadius alpha
  let F : ZMod N → Real := fun r ↦
    ‖fourier (domainFibreCountFunction D) r‖ ^ 4
  let w : ZMod N → Real := fun r ↦ F r * ‖exponential (r * d) - 1‖
  have hlambda : 0 < lambda := by
    dsimp [lambda, section10Lambda]
    positivity
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon, section10BohrRadius]
    positivity
  have hmain :
      ∑ r ∈ (Finset.univ.filter fun r : ZMod N ↦ r ∈ K), w r ≤
        2 * alpha * lambda ^ 2 * (M : Real) ^ 4 * (N : Real) ^ 4 := by
    calc
      ∑ r ∈ (Finset.univ.filter fun r : ZMod N ↦ r ∈ K), w r ≤
          ∑ _r ∈ (Finset.univ.filter fun r : ZMod N ↦ r ∈ K),
            (alpha * M * N) ^ 4 * (2 * Real.pi * epsilon) := by
        apply Finset.sum_le_sum
        intro r hr
        have hrK : r ∈ K := (Finset.mem_filter.mp hr).2
        dsimp [w, F]
        apply mul_le_mul
        · exact pow_le_pow_left₀ (norm_nonneg _)
            (by simpa [hcard] using theorem1013_fourier_norm_le_card D r) 4
        · exact theorem1013_bohr_phase_bound K epsilon d
            (by simpa [K, epsilon, lambda] using hd) r hrK
        · positivity
        · positivity
      _ = (K.card : Real) * ((alpha * M * N) ^ 4 *
          (2 * Real.pi * epsilon)) := by simp
      _ ≤ section10SpectrumBound alpha * ((alpha * M * N) ^ 4 *
          (2 * Real.pi * epsilon)) := by
        exact mul_le_mul_of_nonneg_right
          (theorem10_13_spectrum_bound D alpha halpha hM hfibre hcard)
          (mul_nonneg (pow_nonneg (by positivity : 0 ≤ alpha * (M : Real) * N) 4)
            (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hepsilon.le))
      _ = 2 * alpha * lambda ^ 2 * (M : Real) ^ 4 * (N : Real) ^ 4 := by
        rw [theorem1013_spectrum_bound_eq alpha halpha]
        dsimp [epsilon]
        unfold section10BohrRadius
        have haNeg : alpha ^ (-(4 : Real)) = (alpha ^ (4 : Nat))⁻¹ := by
          rw [Real.rpow_neg halpha.le]
          norm_num [Real.rpow_natCast]
        rw [haNeg]
        field_simp [ne_of_gt halpha, ne_of_gt hlambda, Real.pi_ne_zero]
        ring
  have htailPhase :
      ∑ r ∈ (Finset.univ.filter fun r : ZMod N ↦ r ∉ K), w r ≤
        2 * ∑ r ∈ (Finset.univ.filter fun r : ZMod N ↦ r ∉ K), F r := by
    calc
      ∑ r ∈ (Finset.univ.filter fun r : ZMod N ↦ r ∉ K), w r ≤
          ∑ r ∈ (Finset.univ.filter fun r : ZMod N ↦ r ∉ K), 2 * F r := by
        apply Finset.sum_le_sum
        intro r _
        dsimp [w, F]
        nlinarith [theorem1013_norm_exponential_sub_one_le_two (r * d),
          pow_nonneg (norm_nonneg (fourier (domainFibreCountFunction D) r)) 4]
      _ = 2 * ∑ r ∈ (Finset.univ.filter fun r : ZMod N ↦ r ∉ K), F r := by
        rw [Finset.mul_sum]
  have htail :
      ∑ r ∈ (Finset.univ.filter fun r : ZMod N ↦ r ∉ K), F r ≤
        alpha * lambda ^ 2 * (M : Real) ^ 4 * (N : Real) ^ 4 := by
    simpa [F, K, lambda] using
      theorem1013_small_spectrum_tail D alpha hfibre hcard
  have hsplit :
      (∑ r : ZMod N, w r) =
        (∑ r ∈ (Finset.univ.filter fun r : ZMod N ↦ r ∈ K), w r) +
          ∑ r ∈ (Finset.univ.filter fun r : ZMod N ↦ r ∉ K), w r := by
    simpa only [Finset.mem_univ, true_and] using
      (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (ZMod N))
        (fun r ↦ r ∈ K) w).symm
  change (∑ r : ZMod N, w r) ≤ _
  rw [hsplit]
  calc
    (∑ r ∈ (Finset.univ.filter fun r : ZMod N ↦ r ∈ K), w r) +
        ∑ r ∈ (Finset.univ.filter fun r : ZMod N ↦ r ∉ K), w r ≤
        2 * alpha * lambda ^ 2 * (M : Real) ^ 4 * (N : Real) ^ 4 +
          2 * ∑ r ∈ (Finset.univ.filter fun r : ZMod N ↦ r ∉ K), F r :=
      add_le_add hmain htailPhase
    _ ≤ 2 * alpha * lambda ^ 2 * (M : Real) ^ 4 * (N : Real) ^ 4 +
        2 * (alpha * lambda ^ 2 * (M : Real) ^ 4 * (N : Real) ^ 4) := by
      gcongr
    _ = 4 * alpha * section10Lambda alpha ^ 2 *
        (M : Real) ^ 4 * (N : Real) ^ 4 := by
      dsimp [lambda]
      ring

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
  rw [identity_2_4_holds N h (s + d), identity_2_4_holds N h s]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  apply congrArg ((N : Complex)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro r _
  rw [theorem1013_quad_fourier]
  have hexp : exponential (r * (s + d)) =
      exponential (r * s) * exponential (r * d) := by
    rw [show r * (s + d) = r * s + r * d by ring, theorem1013_exponential_add]
  rw [hexp]
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
  have hweighted :=
    theorem1013_weighted_phase_sum D alpha halpha hM hfibre hcard d hd
  have hnorm :
      ‖(((theorem1013QuadDomain D).fibre (s + d)).card : Complex) -
          (((theorem1013QuadDomain D).fibre s).card : Complex)‖ ≤
        4 * alpha * section10Lambda alpha ^ 2 *
          (M : Real) ^ 4 * (N : Real) ^ 3 := by
    rw [theorem1013_quad_shift_fourier]
    calc
      ‖(N : Complex)⁻¹ * ∑ r : ZMod N,
          ((‖fourier (domainFibreCountFunction D) r‖ ^ 4 : Real) : Complex) *
            exponential (r * s) * (exponential (r * d) - 1)‖ =
          (N : Real)⁻¹ * ‖∑ r : ZMod N,
            ((‖fourier (domainFibreCountFunction D) r‖ ^ 4 : Real) : Complex) *
              exponential (r * s) * (exponential (r * d) - 1)‖ := by
        rw [norm_mul, norm_inv, Complex.norm_natCast]
      _ ≤ (N : Real)⁻¹ * ∑ r : ZMod N,
          ‖((‖fourier (domainFibreCountFunction D) r‖ ^ 4 : Real) : Complex) *
            exponential (r * s) * (exponential (r * d) - 1)‖ := by
        gcongr
        exact norm_sum_le _ _
      _ = (N : Real)⁻¹ * ∑ r : ZMod N,
          ‖fourier (domainFibreCountFunction D) r‖ ^ 4 *
            ‖exponential (r * d) - 1‖ := by
        congr 1
        apply Finset.sum_congr rfl
        intro r _
        rw [norm_mul, norm_mul, theorem1013_norm_exponential,
          Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)]
        ring
      _ ≤ (N : Real)⁻¹ *
          (4 * alpha * section10Lambda alpha ^ 2 *
            (M : Real) ^ 4 * (N : Real) ^ 4) := by
        gcongr
      _ = 4 * alpha * section10Lambda alpha ^ 2 *
          (M : Real) ^ 4 * (N : Real) ^ 3 := by
        field_simp [ne_of_gt hN]
  calc
    |(((theorem1013QuadDomain D).fibre (s + d)).card : Real) -
        ((theorem1013QuadDomain D).fibre s).card| =
        ‖(((((theorem1013QuadDomain D).fibre (s + d)).card : Real) -
          ((theorem1013QuadDomain D).fibre s).card : Real) : Complex)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ =
        ‖(((theorem1013QuadDomain D).fibre (s + d)).card : Complex) -
          (((theorem1013QuadDomain D).fibre s).card : Complex)‖ := by
      congr 1
      rw [Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_natCast]
    _ ≤ 4 * alpha * section10Lambda alpha ^ 2 *
        (M : Real) ^ 4 * (N : Real) ^ 3 := hnorm

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
  have h := theorem1013_quad_shift_bound D alpha halpha hM hfibre hcard s d hd
  calc
    |(((theorem1013QuadDomain D).fibre (s + d)).card : Real) -
        ((theorem1013QuadDomain D).fibre s).card| ≤
        4 * alpha * section10Lambda alpha ^ 2 *
          (M : Real) ^ 4 * (N : Real) ^ 3 := h
    _ = theorem1013Sigma alpha * (M * Fintype.card X ^ 3) := by
      unfold theorem1013Sigma
      rw [hcard]
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
      ((2 : Real) ^ (-(43 : Real))) := by
  refine ⟨theorem1013_quad_domain_bounds D alpha halpha (by linarith) hM hfibre hcard,
    ?_, ?_, ?_, theorem1013_bohr_symmetric _ _, ?_, ?_⟩
  · unfold theorem1013Sigma section10Lambda
    positivity
  · positivity
  · calc
      (2 : Real) ^ (-(43 : Real)) ≤ (2 : Real) ^ (0 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 1 := by norm_num
  · simpa only [Nat.cast_mul, Nat.cast_pow] using
      theorem1013_quad_invariant D alpha halpha hM hfibre hcard
  · exact theorem1013_quad_approx_hom D phi _ happrox

private def theorem1013Eta : Real := (2 : Real) ^ (-(43 : Real))

private def theorem1013Rho (alpha : Real) : Real := alpha ^ 2 / 32

private def theorem1013Theta : Real :=
  10 * theorem1013Eta ^ ((1 : Real) / 5)

private lemma theorem1013_theta_small :
    6 * Real.sqrt theorem1013Theta < 1 := by
  have heta : 0 < theorem1013Eta := by
    unfold theorem1013Eta
    positivity
  have ht : 0 < theorem1013Eta ^ ((1 : Real) / 5) :=
    Real.rpow_pos_of_pos heta _
  have hpow :
      (theorem1013Eta ^ ((1 : Real) / 5)) ^ (5 : Nat) = theorem1013Eta := by
    have h := Real.rpow_mul_natCast heta.le ((1 : Real) / 5) 5
    calc
      (theorem1013Eta ^ ((1 : Real) / 5)) ^ (5 : Nat) =
          theorem1013Eta ^ ((1 : Real) / 5 * (5 : Nat)) := h.symm
      _ = theorem1013Eta := by norm_num [Real.rpow_one]
  have hthetaPow : theorem1013Theta ^ (5 : Nat) =
      100000 * theorem1013Eta := by
    unfold theorem1013Theta
    rw [mul_pow, hpow]
    norm_num
  have hcompare :
      theorem1013Theta ^ (5 : Nat) < (1 / 36 : Real) ^ (5 : Nat) := by
    rw [hthetaPow]
    unfold theorem1013Eta
    rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)]
    norm_num [Real.rpow_natCast]
  have htheta : theorem1013Theta < 1 / 36 := by
    exact lt_of_pow_lt_pow_left₀ 5 (by norm_num) hcompare
  have hthetaNonneg : 0 ≤ theorem1013Theta := by
    unfold theorem1013Theta
    positivity
  have hsquare : (Real.sqrt theorem1013Theta) ^ 2 = theorem1013Theta :=
    Real.sq_sqrt hthetaNonneg
  have hsqrtNonneg := Real.sqrt_nonneg theorem1013Theta
  nlinarith

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
  rw [theorem1013_lambda_sq alpha halpha]
  rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)]
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
  have halphaOne : alpha ≤ 1 := by linarith
  have hpow : alpha ^ (9 : Nat) ≤ alpha ^ 2 := by
    calc
      alpha ^ (9 : Nat) = alpha ^ 2 * alpha ^ 7 := by ring
      _ ≤ alpha ^ 2 * 1 := by
        gcongr
        exact pow_le_one₀ halpha.le halphaOne
      _ = alpha ^ 2 := by ring
  rw [theorem1013_sigma_eq alpha halpha]
  unfold theorem1013Eta
  calc
    (2 : Real) ^ (-(72 : Real)) * alpha ^ (9 : Nat) ≤
        (2 : Real) ^ (-(72 : Real)) * alpha ^ 2 := by gcongr
    _ ≤ (2 : Real) ^ (-(43 : Real)) * alpha ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
        (sq_nonneg alpha)

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
  have halphaOne : alpha ≤ 1 := by linarith
  have hpow : alpha ^ (9 : Nat) ≤ alpha ^ 2 := by
    calc
      alpha ^ (9 : Nat) = alpha ^ 2 * alpha ^ 7 := by ring
      _ ≤ alpha ^ 2 * 1 := by
        gcongr
        exact pow_le_one₀ halpha.le halphaOne
      _ = alpha ^ 2 := by ring
  rw [theorem1013_sigma_eq alpha halpha]
  calc
    (2 : Real) ^ (-(72 : Real)) * alpha ^ (9 : Nat) ≤
        (2 : Real) ^ (-(72 : Real)) * alpha ^ 2 := by gcongr
    _ < (1 / 16 : Real) * alpha ^ 2 := by
      apply mul_lt_mul_of_pos_right _ (sq_pos_of_pos halpha)
      rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)]
      norm_num [Real.rpow_natCast]
    _ = alpha ^ 2 / 16 := by ring

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
  rcases hregular with ⟨_, _, _, _, _, hfibreLower, _⟩
  have hM : (0 : Real) < M := by exact_mod_cast hbounds.2.2.1
  have hinv := hinvariant (D.index w) d hd
  have hsource : alpha ^ 2 * M / 16 ≤ (D.fibre (D.index w)).card := by
    simpa only [MultifunctionDomain.fibreSize] using hfibreLower w hw
  have htarget : (0 : Real) < (D.fibre (D.index w + d)).card := by
    have hinv' :
        |((D.fibre (D.index w)).card : Real) -
            (D.fibre (D.index w + d)).card| ≤ sigma * M := by
      simpa only [abs_sub_comm] using hinv
    have hdiff :
        ((D.fibre (D.index w)).card : Real) -
            (D.fibre (D.index w + d)).card ≤ sigma * M := by
      exact (le_abs_self _).trans hinv'
    have hsigmam : sigma * M < alpha ^ 2 * M / 16 := by
      calc
        sigma * M < (alpha ^ 2 / 16) * M :=
          mul_lt_mul_of_pos_right hsigma hM
        _ = alpha ^ 2 * M / 16 := by ring
    nlinarith
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
  classical
  let T : Finset (X × X × X) := Finset.univ
  let F : X × X × X → Finset (Theorem1013Quad X) := fun p ↦
    W.filter fun q ↦ theorem1013Tail q = p
  have hT : T.Nonempty := Finset.univ_nonempty
  have hTcard : (T.card : Real) = (Fintype.card X : Real) ^ 3 := by
    dsimp [T]
    simp [Fintype.card_prod]
    ring
  have hTcardPos : (0 : Real) < T.card := by positivity
  have hsumNat : (∑ p ∈ T, (F p).card) = W.card := by
    exact (Finset.card_eq_sum_card_fiberwise (s := W) (t := T)
      (f := theorem1013Tail) (by simp [T])).symm
  have hsum : (∑ p ∈ T, ((F p).card : Real)) = W.card := by
    exact_mod_cast hsumNat
  have havg :
      (∑ _p ∈ T, (W.card : Real) / T.card) ≤
        ∑ p ∈ T, ((F p).card : Real) := by
    rw [hsum]
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp [ne_of_gt hTcardPos]
    rfl
  obtain ⟨p, hpT, hp⟩ := Finset.exists_le_of_sum_le hT havg
  refine ⟨p, ?_⟩
  have hp' : (W.card : Real) ≤ (T.card : Real) * (F p).card :=
    by simpa only [mul_comm] using (div_le_iff₀ hTcardPos).mp hp
  simpa only [hTcard, F] using hp'

private noncomputable def theorem1013Slice {X : Type*} [DecidableEq X]
    (W : Finset (Theorem1013Quad X)) (p : X × X × X) : Finset X :=
  (W.filter fun q ↦ theorem1013Tail q = p).image fun q ↦ q 0

private def theorem1013OfHead {X : Type*} (p : X × X × X) (y : X) :
    Theorem1013Quad X := ![y, p.1, p.2.1, p.2.2]

private lemma theorem1013_of_head_mem {X : Type*} [Fintype X] [DecidableEq X]
    (W : Finset (Theorem1013Quad X)) (p : X × X × X) (y : X)
    (hy : y ∈ theorem1013Slice W p) : theorem1013OfHead p y ∈ W := by
  classical
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
  classical
  unfold theorem1013Slice
  apply Finset.card_image_iff.mpr
  intro q₁ hq₁ q₂ hq₂ hzero
  have ht₁ := (Finset.mem_filter.mp hq₁).2
  have ht₂ := (Finset.mem_filter.mp hq₂).2
  have ht : theorem1013Tail q₁ = theorem1013Tail q₂ := ht₁.trans ht₂.symm
  change (q₁ 1, q₁ 2, q₁ 3) = (q₂ 1, q₂ 2, q₂ 3) at ht
  have hone : q₁ 1 = q₂ 1 := congrArg Prod.fst ht
  have htail : (q₁ 2, q₁ 3) = (q₂ 2, q₂ 3) := congrArg Prod.snd ht
  have htwo : q₁ 2 = q₂ 2 := congrArg Prod.fst htail
  have hthree : q₁ 3 = q₂ 3 := congrArg Prod.snd htail
  funext i
  fin_cases i
  · exact hzero
  · exact hone
  · exact htwo
  · exact hthree

/-- **Gowers, Theorem 10.13.** -/
theorem theorem_10_13_holds : theorem_10_13 := by
  classical
  intro N M _ X _ _ D phi alpha halpha halphaSixth hM hfibre hcard happrox
  dsimp only
  refine ⟨theorem10_13_spectrum_bound D alpha halpha hM hfibre hcard,
    theorem10_13_zeta_bound alpha halpha, ?_⟩
  let D₄ : MultifunctionDomain N (Theorem1013Quad X) := theorem1013QuadDomain D
  let phi₄ : Theorem1013Quad X → ZMod N := theorem1013QuadPhase phi
  let K : Finset (ZMod N) :=
    domainLargeSpectrum D (section10Lambda alpha * M * N)
  let epsilon : Real := section10BohrRadius alpha
  let zeta : Real := section10Zeta alpha
  let B : Finset (ZMod N) := bohr K epsilon
  let L : Nat := M * Fintype.card X ^ 3
  let eta : Real := theorem1013Eta
  let rho : Real := theorem1013Rho alpha
  let sigma : Real := theorem1013Sigma alpha
  let theta : Real := theorem1013Theta
  have hsetup : Section10Setup D₄ phi₄ B alpha L sigma eta := by
    simpa only [D₄, phi₄, K, epsilon, B, L, sigma, eta, theorem1013Eta] using
      theorem1013_quad_setup D phi alpha halpha halphaSixth hM hfibre hcard happrox
  have hsigmaAlpha : sigma ≤ eta * alpha ^ 2 := by
    simpa only [sigma, eta] using
      theorem1013_sigma_le_eta_alpha_sq alpha halpha halphaSixth
  obtain ⟨x, hanchor⟩ :=
    lemma_10_3_holds N (Theorem1013Quad X) D₄ phi₄ B alpha L sigma eta
      hsetup hsigmaAlpha
  have hrho := theorem1013_rho_bounds alpha halpha halphaSixth
  have hsigmaRegular : sigma ≤ eta * rho ^ 4 * alpha / 384 := by
    simpa only [sigma, eta, rho] using
      theorem1013_sigma_le_regular alpha halpha halphaSixth
  obtain ⟨W, hregular⟩ :=
    lemma_10_5_holds N (Theorem1013Quad X) D₄ phi₄ B alpha rho L sigma eta x
      hsetup hsigmaAlpha hanchor hrho.1 hrho.2.1 hrho.2.2 hsigmaRegular
  have hsigmaExtraction : sigma ≤ eta * rho * alpha ^ 2 / 16 := by
    simpa only [sigma, eta, rho] using
      theorem1013_sigma_le_extraction alpha halpha halphaSixth
  obtain ⟨B', psi, hlocal⟩ :=
    lemma_10_6_holds N (Theorem1013Quad X) D₄ phi₄ B alpha rho L sigma eta x W
      hsetup hanchor hregular hrho.2.2 hsigmaExtraction
  change IsSection10LocalDifferenceModel D₄ phi₄ W B B' psi theta at hlocal
  have hshift : IsSection10ShiftRegular D₄ W B eta :=
    section10_regular_shift_regular D₄ phi₄ B alpha sigma eta rho x W hsetup hregular
  have hWnonempty : W.Nonempty := by
    have hlower := hregular.2.2.2.1
    have hL : (0 : Real) < L := by exact_mod_cast hsetup.1.2.2.1
    have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    have hpositive : 0 < rho ^ 2 * alpha ^ 2 * L * N / 16 := by
      have : 0 < rho := hrho.1
      positivity
    exact Finset.card_pos.mp (by exact_mod_cast hpositive.trans_le hlower)
  have hpsi : FreimanHom 2 B' psi := by
    apply lemma_10_9_holds N (Theorem1013Quad X) D₄ phi₄ W B B' psi eta
    · exact hWnonempty
    · exact hshift
    · simpa only [theta, eta, theorem1013Theta, theorem1013Eta] using hlocal
    · change 6 * Real.sqrt theorem1013Theta < 1
      exact theorem1013_theta_small
  have hK : K.Nonempty := by
    simpa only [K] using
      theorem10_13_largeSpectrum_nonempty D alpha halpha halphaSixth hcard
  have hepsilon : 0 < epsilon := by
    simpa only [epsilon] using theorem10_13_bohrRadius_pos alpha halpha
  have hepsilonOne : epsilon ≤ 1 := by
    simpa only [epsilon] using
      theorem10_13_bohrRadius_le_one alpha halpha halphaSixth
  have hBdense : (7 / 8 : Real) * B.card ≤ B'.card := by
    have hdense := hlocal.2.1
    have htheta : theta ≤ 1 / 8 := by
      simpa only [theta] using theorem1013_theta_le_eighth
    nlinarith
  have hcor := corollary_10_11_holds N K epsilon hK hepsilon hepsilonOne
    B' psi hlocal.1 hBdense hpsi
  rcases hcor with ⟨hCsub, psi₁, hpsi₁, hinduced⟩
  have hsqrtRelaxed : Real.sqrt theta < 5 / 16 := by
    change Real.sqrt theorem1013Theta < 5 / 16
    linarith [theorem1013_theta_small]
  have hsigmaFibre : sigma < alpha ^ 2 / 16 := by
    simpa only [sigma] using
      theorem1013_sigma_lt_fibre alpha halpha halphaSixth
  have htranslated : ∀ w, w ∈ W → ∀ d, d ∈ B' →
      (D₄.fibre (D₄.index w + d)).Nonempty := by
    intro w hw d hd
    exact section10_regular_translated_fibre_nonempty D₄ phi₄ B alpha sigma eta rho
      x W hsetup hregular hsigmaFibre w hw d (hlocal.1 hd)
  have hdiff := lemma_10_12_holds N (Theorem1013Quad X) D₄ phi₄
    K epsilon theta W B' psi psi₁ hK hepsilon hepsilonOne hsqrtRelaxed
    htranslated hlocal hpsi₁ hinduced
  let zeta₀ : Real := (2 : Real) ^ (-((K.card : Real) + 4)) *
    epsilon ^ K.card / K.card
  let C₀ : Finset (ZMod N) := bohr K zeta₀
  let W₁ : Finset (Theorem1013Quad X) :=
    section10RegularSet D₄ phi₄ W B' psi theta
  change ∀ w₁, w₁ ∈ W₁ → ∀ w₂, w₂ ∈ W₁ →
    D₄.index w₁ - D₄.index w₂ ∈ C₀ →
      phi₄ w₁ - phi₄ w₂ = psi₁ (D₄.index w₁ - D₄.index w₂) at hdiff
  have hAE := lemma_10_7_holds N (Theorem1013Quad X) D₄ phi₄ W B B' psi eta
    (by simpa only [theta, eta, theorem1013Theta, theorem1013Eta] using hlocal)
  change AlmostEvery (1 - Real.sqrt theta) W (fun w ↦
    AlmostEvery (1 - Real.sqrt theta) B' (fun d ↦
      AlmostEvery (1 - theta) (D₄.fibre (D₄.index w + d)) (fun z ↦
        phi₄ z - phi₄ w = psi d))) at hAE
  have hW₁lower : (1 - Real.sqrt theta) * (W.card : Real) ≤ W₁.card := by
    simpa only [AlmostEvery, W₁, section10RegularSet] using hAE
  have hquadCard : (Fintype.card (Theorem1013Quad X) : Real) =
      alpha * L * N := hsetup.1.2.2.2.1
  have hregularLower : rho ^ 2 * alpha ^ 2 * L * N / 16 ≤ W.card :=
    hregular.2.2.2.1
  have hW₁target :
      alpha ^ 6 * Fintype.card (Theorem1013Quad X) / 20000 ≤ W₁.card := by
    have hfactor : (5 / 6 : Real) < 1 - Real.sqrt theta := by
      have h := theorem1013_theta_small
      change 6 * Real.sqrt theta < 1 at h
      linarith
    have hbase : 0 ≤ alpha ^ 6 * (L : Real) * N := by positivity
    have halphaScaled :
        alpha * (alpha ^ 6 * (L : Real) * N) ≤
          (1 / 6 : Real) * (alpha ^ 6 * (L : Real) * N) :=
      mul_le_mul_of_nonneg_right halphaSixth hbase
    have hnumeric :
        alpha ^ 6 * Fintype.card (Theorem1013Quad X) / 20000 ≤
          (5 / 6 : Real) * (rho ^ 2 * alpha ^ 2 * L * N / 16) := by
      rw [hquadCard]
      dsimp only [rho, theorem1013Rho]
      nlinarith
    calc
      alpha ^ 6 * Fintype.card (Theorem1013Quad X) / 20000 ≤
          (5 / 6 : Real) * (rho ^ 2 * alpha ^ 2 * L * N / 16) := hnumeric
      _ ≤ (5 / 6 : Real) * W.card := by gcongr
      _ ≤ (1 - Real.sqrt theta) * W.card := by
        exact mul_le_mul_of_nonneg_right hfactor.le (by positivity)
      _ ≤ W₁.card := hW₁lower
  have hXcardPosReal : (0 : Real) < Fintype.card X := by
    rw [hcard]
    have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    have hMReal : (0 : Real) < M := by exact_mod_cast hM
    positivity
  have hXcardPos : 0 < Fintype.card X := by exact_mod_cast hXcardPosReal
  letI : Nonempty X := Fintype.card_pos_iff.mp hXcardPos
  obtain ⟨p, hp⟩ := theorem1013_exists_large_tail_fibre W₁
  let S : Finset (Theorem1013Quad X) :=
    W₁.filter fun q ↦ theorem1013Tail q = p
  let Y : Finset X := theorem1013Slice W₁ p
  have hYcard : Y.card = S.card := by
    simpa only [Y, S] using theorem1013_slice_card W₁ p
  have hYlarge : alpha ^ 6 * Fintype.card X / 20000 ≤ Y.card := by
    have hcubePos : (0 : Real) < (Fintype.card X : Real) ^ 3 := by positivity
    have hscaled :
        (alpha ^ 6 * Fintype.card X / 20000) *
            (Fintype.card X : Real) ^ 3 ≤
          (S.card : Real) * (Fintype.card X : Real) ^ 3 := by
      calc
        (alpha ^ 6 * Fintype.card X / 20000) *
              (Fintype.card X : Real) ^ 3 =
            alpha ^ 6 * Fintype.card (Theorem1013Quad X) / 20000 := by
          rw [theorem1013_quad_card]
          push_cast
          ring
        _ ≤ (W₁.card : Real) := hW₁target
        _ ≤ (Fintype.card X : Real) ^ 3 * (S.card : Real) := by
          simpa only [S] using hp
        _ = (S.card : Real) * (Fintype.card X : Real) ^ 3 := by ring
    rw [hYcard]
    exact le_of_mul_le_mul_right hscaled hcubePos
  have hzetaActual : zeta ≤ zeta₀ := by
    simpa only [zeta, zeta₀, epsilon] using
      theorem10_13_zeta_le_actualSpectrumRadius alpha halpha halphaSixth K
        (theorem10_13_spectrum_bound D alpha halpha hM hfibre hcard) hK
  have hCsubFinal : bohr K zeta ⊆ C₀ := by
    intro c hc
    change c ∈ bohr K zeta₀
    rw [bohr, Finset.mem_filter] at hc ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    intro r hr
    exact (hc.2 r hr).trans
      (mul_le_mul_of_nonneg_right hzetaActual (by positivity))
  have hpsiFinal : FreimanHom 2 (bohr K zeta) psi₁ := by
    unfold FreimanHom at hpsi₁ ⊢
    apply hpsi₁.subset
    · intro c hc
      exact hCsubFinal hc
    · intro c hc
      exact Set.mem_univ _
  refine ⟨Y, psi₁, hYlarge, hpsiFinal, ?_⟩
  intro y hy z hz hyz
  let qy : Theorem1013Quad X := theorem1013OfHead p y
  let qz : Theorem1013Quad X := theorem1013OfHead p z
  have hqy : qy ∈ W₁ := by
    exact theorem1013_of_head_mem W₁ p y (by simpa only [Y] using hy)
  have hqz : qz ∈ W₁ := by
    exact theorem1013_of_head_mem W₁ p z (by simpa only [Y] using hz)
  have hindex : D₄.index qy - D₄.index qz = D.index y - D.index z := by
    dsimp only [D₄, qy, qz, theorem1013QuadDomain, theorem1013OfHead]
    simp [sub_eq_add_neg]
  have hphase : phi₄ qy - phi₄ qz = phi y - phi z := by
    dsimp only [phi₄, qy, qz, theorem1013QuadPhase, theorem1013OfHead]
    simp [sub_eq_add_neg]
  have hc₀ : D₄.index qy - D₄.index qz ∈ C₀ := by
    rw [hindex]
    exact hCsubFinal hyz
  have h := hdiff qy hqy qz hqz hc₀
  calc
    phi y - phi z = phi₄ qy - phi₄ qz := hphase.symm
    _ = psi₁ (D₄.index qy - D₄.index qz) := h
    _ = psi₁ (D.index y - D.index z) := by rw [hindex]

end LeanProofs.GowersSzemeredi
