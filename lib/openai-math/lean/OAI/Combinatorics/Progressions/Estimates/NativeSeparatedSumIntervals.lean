/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.NativeMixedSeparatedFamily
import OAI.Combinatorics.Progressions.Geometry.CubeSignalCoordinates

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_absorb_pair_missing_coordinate_errors (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} {D : RationalFilteredNilmanifold L s d}
      {E : RationalFilteredNilmanifold M s e} {p : ℝ}
      (T : D.Niltest (fun _ : Fin (s + 1) => 1))
      (U : E.Niltest (fun _ : Fin (s + 1) => 1)), T.ComplexityLE p → U.ComplexityLE p →
      ∀ {G X : Type*} (H : Finset G), H.Nonempty →
      ∀ (S : G → Finset X), (∀ h ∈ H, (S h).Nonempty) →
      ∀ (sample : G → X → Fin (s + 1) → ℤ) (f : G → X → ℂ),
      (∀ h ∈ H, ∀ x ∈ S h, ‖f h x‖ ≤ 1) →
      (∀ h ∈ H, Real.exp (-p) ≤
        ‖𝔼 x ∈ S h, f h x * star (T.eval (sample h x)) * star (U.eval (sample h x))‖) →
      ∃ A : Fin (s + 1) → (Fin (s + 1) → ℤ) → ℂ,
        (∀ i x, ‖A i x‖ ≤ 1) ∧
        (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
        ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (H.card : ℝ) ≤ (H'.card : ℝ) ∧
          ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 x ∈ S h, f h x * ∏ i, A i (sample h x)‖ := by
  obtain ⟨a, _, habsorb⟩ := exists_absorb_missing_coordinate_error s
  let X : Polynomial ℕ := Polynomial.X
  let Q := (2 * X + Polynomial.C a) ^ a
  let R := (X + Q + 2 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + R)
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E p T U hT hU G Ω H hH S hS sample f hf hcorr
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hT.1.1
  let q := (2 * p + a) ^ a
  let t := p + q + 2
  let r := (t + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith
  have hqt : q ≤ t := by dsimp [t]; linarith
  have htotal : q + r ≤ (p + C) ^ C := by
    simpa [X, Q, R, q, t, r, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + C) ^ C := by linarith
  let V := U.expNormalize p
  have hV : V.ComplexityLE p := U.expNormalize_complexity hU
  have hVnorm (x : Fin (s + 1) → ℤ) : ‖V.eval x‖ ≤ 1 :=
    (V.norm_eval_le x).trans (U.expNormalize_norm hU)
  let g (h : G) (x : Ω) := f h x * star (V.eval (sample h x))
  have hg : ∀ h ∈ H, ∀ x ∈ S h, ‖g h x‖ ≤ 1 := by
    intro h hh x hx
    dsimp only [g]
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf h hh x hx)).trans (hVnorm _)
  have hgcorr : ∀ h ∈ H, Real.exp (-(2 * p)) ≤
      ‖𝔼 x ∈ S h, g h x * star (T.eval (sample h x))‖ := by
    intro h hh
    have heq : (𝔼 x ∈ S h, g h x * star (T.eval (sample h x))) =
        (Real.exp (-p) : ℂ) *
          (𝔼 x ∈ S h, f h x * star (T.eval (sample h x)) * star (U.eval (sample h x))) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      simp only [g, V, RationalFilteredNilmanifold.Niltest.expNormalize_eval,
        star_mul, Complex.star_def, Complex.conj_ofReal]
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    calc
      _ = Real.exp (-p) * Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcorr h hh) (Real.exp_nonneg _)
  obtain ⟨A, hA, hAind, H₁, hsub₁, hH₁, hsize₁, hcorr₁⟩ :=
    habsorb T (hT.mono (by linarith : p ≤ 2 * p)) H hH S hS sample g hg hgcorr
  let g₁ (h : G) (x : Ω) := f h x * ∏ i, A i (sample h x)
  have hg₁ : ∀ h ∈ H₁, ∀ x ∈ S h, ‖g₁ h x‖ ≤ 1 := by
    intro h hh x hx
    dsimp only [g₁]
    rw [norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) (hf h (hsub₁ hh) x hx)).trans
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hA i _)
  have hgcorr₁ : ∀ h ∈ H₁, Real.exp (-t) ≤
      ‖𝔼 x ∈ S h, g₁ h x * star (V.eval (sample h x))‖ := by
    intro h hh
    have heq : (𝔼 x ∈ S h, g h x * ∏ i, A i (sample h x)) =
        (𝔼 x ∈ S h, g₁ h x * star (V.eval (sample h x))) := by
      apply Finset.expect_congr rfl
      intro x _
      exact mul_right_comm _ _ _
    rw [← heq]
    exact (Real.exp_le_exp.mpr (neg_le_neg hqt)).trans (hcorr₁ h hh)
  obtain ⟨B, hB, hBind, H₂, hsub₂, hH₂, hsize₂, hcorr₂⟩ :=
    habsorb V (hV.mono hpt) H₁ hH₁ S (fun h hh => hS h (hsub₁ hh)) sample g₁ hg₁ hgcorr₁
  refine ⟨(fun i x => A i x * B i x), ?_, ?_, H₂, hsub₂.trans hsub₁, hH₂, ?_, ?_⟩
  · intro i x
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hA i x)).trans (hB i x)
  · intro i x y hxy
    change A i x * B i x = A i y * B i y
    rw [hAind i x y hxy, hBind i x y hxy]
  · calc
      _ ≤ Real.exp (-(q + r)) * (H.card : ℝ) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg htotal)) (Nat.cast_nonneg _)
      _ = Real.exp (-r) * (Real.exp (-q) * (H.card : ℝ)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-r) * (H₁.card : ℝ) := mul_le_mul_of_nonneg_left hsize₁ (Real.exp_nonneg _)
      _ ≤ _ := hsize₂
  · intro h hh
    simpa only [g₁, Finset.prod_mul_distrib, mul_assoc] using
      (Real.exp_le_exp.mpr (neg_le_neg hrC)).trans (hcorr₂ h hh)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_fullCube_proper_factors {G : Type*} [AddCommGroup G] {d : ℕ}
    (f : G → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1) :
    ∃ A : Fin (d + 3) → (Fin (d + 3) → G) → ℂ,
      (∀ i x, ‖A i x‖ ≤ 1) ∧
      (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
      ∀ x, fullCubeSignal f x = conjugationPower (d + 2) (f (∑ i, x i)) * ∏ i, A i x := by
  classical
  let S : Finset (Fin (d + 2) → Bool) := Finset.univ.erase (fun _ => true)
  let F (ω : S) (x : Fin (d + 3) → G) := conjugationPower (booleanWeight ω.val)
    (f (x 1 + cubeShift (fun j => x ((1 : Fin (d + 3)).succAbove j)) ω.val))
  have hF : ∀ ω x, ‖F ω x‖ ≤ 1 := by
    intro ω x
    exact (conjugationPower_norm _ _).trans_le (hf _)
  have hFi : ∀ ω, ∃ i, ∀ x y, (∀ k, k ≠ i → x k = y k) → F ω x = F ω y := by
    intro ω
    obtain ⟨j, hj⟩ := exists_false_of_ne_true (Finset.mem_erase.mp ω.property).1
    refine ⟨(1 : Fin (d + 3)).succAbove j, ?_⟩
    intro x y hxy
    exact congrArg (fun z => conjugationPower (booleanWeight ω.val) (f z))
      (fullCube_input_independent ω.val j hj x y hxy)
  obtain ⟨A, hA, hAi, hprod⟩ := exists_missing_coordinate_product_factors F hF hFi
  refine ⟨A, hA, hAi, ?_⟩
  intro x
  have hsum : x 1 + (∑ j : Fin (d + 2), x ((1 : Fin (d + 3)).succAbove j)) = ∑ i, x i :=
    (Fin.sum_univ_succAbove x 1).symm
  calc
    fullCubeSignal f x = conjugationPower (d + 2) (f (∑ i, x i)) *
        ∏ ω ∈ S, conjugationPower (booleanWeight ω)
          (f (x 1 + cubeShift (fun j => x ((1 : Fin (d + 3)).succAbove j)) ω)) := by
      unfold fullCubeSignal
      rw [cubeProduct_eq_boolean_product]
      rw [← Finset.mul_prod_erase Finset.univ
        (fun ω => conjugationPower (booleanWeight ω)
          (f (x 1 + cubeShift (fun j => x ((1 : Fin (d + 3)).succAbove j)) ω)))
        (Finset.mem_univ (fun _ : Fin (d + 2) => true))]
      rw [booleanWeight_true, cubeShift_true, hsum]
    _ = _ := by
      rw [hprod]
      congr 1
      exact (Finset.prod_coe_sort S (fun ω => conjugationPower (booleanWeight ω)
        (f (x 1 + cubeShift (fun j => x ((1 : Fin (d + 3)).succAbove j)) ω)))).symm

theorem exists_mixedCube_proper_factors {J : Type*} {d : ℕ}
    (η : J → (Fin 2 → ℤ) → ℂ) (hη : ∀ j x, ‖η j x‖ ≤ 1) (w : (Fin d → Bool) → J) :
    ∃ A : Fin (d + 2) → (Fin (d + 2) → ℤ) → ℂ,
      (∀ i x, ‖A i x‖ ≤ 1) ∧
      (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
      ∀ x, mixedCubeObservable η w x =
        conjugationPower d (η (w (fun _ => true)) (correlationInput (x 0) (∑ j : Fin (d + 1), x j.succ))) *
          ∏ i, A i x := by
  classical
  let S : Finset (Fin d → Bool) := Finset.univ.erase (fun _ => true)
  let F (ω : S) (x : Fin (d + 2) → ℤ) :=
    conjugationPower (booleanWeight ω.val) (η (w ω.val) (mixedCubeInput ω.val x))
  have hF : ∀ ω x, ‖F ω x‖ ≤ 1 := by
    intro ω x
    exact (conjugationPower_norm _ _).trans_le (hη _ _)
  have hFi : ∀ ω, ∃ i, ∀ x y, (∀ k, k ≠ i → x k = y k) → F ω x = F ω y := by
    intro ω
    obtain ⟨j, hj⟩ := exists_false_of_ne_true (Finset.mem_erase.mp ω.property).1
    refine ⟨j.succ.succ, ?_⟩
    intro x y hxy
    exact congrArg (fun z => conjugationPower (booleanWeight ω.val) (η (w ω.val) z))
      (mixedCubeInput_independent ω.val j hj x y hxy)
  obtain ⟨A, hA, hAi, hprod⟩ := exists_missing_coordinate_product_factors F hF hFi
  refine ⟨A, hA, hAi, ?_⟩
  intro x
  calc
    mixedCubeObservable η w x =
        conjugationPower d (η (w (fun _ => true)) (correlationInput (x 0) (∑ j : Fin (d + 1), x j.succ))) *
          ∏ ω ∈ S, conjugationPower (booleanWeight ω) (η (w ω) (mixedCubeInput ω x)) := by
      unfold mixedCubeObservable
      rw [← Finset.mul_prod_erase Finset.univ
        (fun ω => conjugationPower (booleanWeight ω) (η (w ω) (mixedCubeInput ω x)))
        (Finset.mem_univ (fun _ : Fin d => true))]
      rw [booleanWeight_true, mixedCubeInput_true]
    _ = _ := by
      rw [hprod]
      congr 1
      exact (Finset.prod_coe_sort S (fun ω => conjugationPower (booleanWeight ω)
        (η (w ω) (mixedCubeInput ω x)))).symm

theorem exists_full_mixed_cube_proper_factors {J : Type*} {d : ℕ}
    (f : ℤ → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1)
    (η : J → (Fin 2 → ℤ) → ℂ) (hη : ∀ j x, ‖η j x‖ ≤ 1) (w : (Fin (d + 1) → Bool) → J) :
    ∃ A : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ,
      (∀ i x, ‖A i x‖ ≤ 1) ∧
      (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
      ∀ x, fullCubeSignal f x * star (mixedCubeObservable η w x) =
        conjugationPower (d + 2) (f (∑ i, x i) *
          η (w (fun _ => true)) (correlationInput (x 0) (∑ j : Fin (d + 2), x j.succ))) *
            ∏ i, A i x := by
  obtain ⟨A, hA, hAi, hAfactor⟩ := exists_fullCube_proper_factors (d := d) f hf
  obtain ⟨B, hB, hBi, hBfactor⟩ := exists_mixedCube_proper_factors η hη w
  refine ⟨(fun i x => A i x * star (B i x)), ?_, ?_, ?_⟩
  · intro i x
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hA i x)).trans (hB i x)
  · intro i x y hxy
    change A i x * star (B i x) = A i y * star (B i y)
    rw [hAi i x y hxy, hBi i x y hxy]
  · intro x
    have hstep (z : ℂ) : conjugationPower (d + 2) z = star (conjugationPower (d + 1) z) := rfl
    rw [hAfactor, hBfactor]
    simp only [Finset.prod_mul_distrib, star_prod, map_mul, hstep, star_mul]
    ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_normalized_cube_weights {J : Type*} {d : ℕ}
    (f : ℤ → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1)
    (η : J → (Fin 2 → ℤ) → ℂ) (hη : ∀ j x, ‖η j x‖ ≤ 1) (w : (Fin (d + 1) → Bool) → J)
    (A : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ) (hA : ∀ i x, ‖A i x‖ ≤ 1)
    (hAi : ∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) :
    ∃ B : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ,
      (∀ i x, ‖B i x‖ ≤ 1) ∧
      (∀ i x y, (∀ k, k ≠ i → x k = y k) → B i x = B i y) ∧
      ∀ x, conjugationPower (d + 3)
          ((fullCubeSignal f x * star (mixedCubeObservable η w x)) * ∏ i, A i x) =
        star (f (∑ i, x i)) *
          star (η (w (fun _ => true)) (correlationInput (x 0) (∑ j : Fin (d + 2), x j.succ))) *
            ∏ i, B i x := by
  obtain ⟨P, hP, hPi, hfactor⟩ := exists_full_mixed_cube_proper_factors f hf η hη w
  refine ⟨(fun i x => conjugationPower (d + 3) (P i x * A i x)), ?_, ?_, ?_⟩
  · intro i x
    change ‖conjugationPower (d + 3) (P i x * A i x)‖ ≤ 1
    rw [conjugationPower_norm, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hP i x)).trans (hA i x)
  · intro i x y hxy
    change conjugationPower (d + 3) (P i x * A i x) = conjugationPower (d + 3) (P i y * A i y)
    rw [hPi i x y hxy, hAi i x y hxy]
  · intro x
    rw [hfactor]
    have hprod : (conjugationPower (d + 2) (f (∑ i, x i) *
        η (w (fun _ => true)) (correlationInput (x 0) (∑ j : Fin (d + 2), x j.succ))) * ∏ i, P i x) *
          (∏ i, A i x) =
        conjugationPower (d + 2) (f (∑ i, x i) *
          η (w (fun _ => true)) (correlationInput (x 0) (∑ j : Fin (d + 2), x j.succ))) *
            ∏ i, P i x * A i x := by
      rw [Finset.prod_mul_distrib]
      ring
    rw [hprod, map_mul, conjugationPower_next_self, map_prod, star_mul]
    ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_absorb_fixed_target_cube_errors (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {J : Type*} [Fintype J] {N : ℕ} [NeZero N] {p q : ℝ}, 0 ≤ q →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) →
      ∀ (M : NativeMixedCorrelation (d + 2) N p f) (η : J → (Fin 2 → ℤ) → ℂ),
      (∀ j x, ‖η j x‖ ≤ 1) → HasFixedTargetCubeIntervals f M η q →
      HasWeightedTargetCubeIntervals f M η ((q + C) ^ C) := by
  obtain ⟨a, _, habsorb⟩ := exists_absorb_pair_missing_coordinate_errors (d + 2)
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + P)
  refine ⟨C, hC, ?_⟩
  intro J _ N _ p q hq f hf M η hη H
  classical
  let r := (q + a) ^ a
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : q + r ≤ (q + C) ^ C := by
    simpa [X, P, r, Polynomial.eval₂_pow] using hbudget q hq
  have hqC : q ≤ (q + C) ^ C := by linarith
  have hrC : r ≤ (q + C) ^ C := by linarith
  obtain ⟨r₀, u, hr₀, hr₀q, hu, huq, E, F, i, b, v, l, w, z, Q, hQ, hdense, hcorr⟩ := H
  let T := ((E b).selectedExpansion (fun _ => i) v).test l
  let U := (F.selectedExpansion v w).test z
  have hT : T.ComplexityLE q := (((E b).selectedExpansion (fun _ => i) v).complexity l).mono hr₀q
  have hU : U.ComplexityLE q := ((F.selectedExpansion v w).complexity z).mono huq
  have hdata (t : Q) := hcorr t.val t.property
  choose hshift start len hlen hend hshort hvol hcor using hdata
  let I (t : Q) := Finset.Ico (start t : ℤ) (start t + len t)
  let sample (t : Q) := mixedDifferencePoint t.val
  let signal (t : Q) (n : ℤ) := cubeProduct f (t.val.2 :: List.ofFn t.val.1) (n : ZMod N) *
    star (mixedCubeObservable η w (sample t n))
  let : Nonempty Q := hQ.to_subtype
  have hI (t : Q) : (I t).Nonempty := Finset.nonempty_Ico.mpr (by
    have hh := hlen t
    change (start t : ℤ) < start t + len t
    omega)
  have hsignal (t : Q) (n : ℤ) : ‖signal t n‖ ≤ 1 := by
    dsimp only [signal]
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (cubeProduct_norm_le_one f hf _ _)).trans
      (mixedCubeObservable_norm_le_one η hη w _)
  obtain ⟨A, hA, hAi, S, _, hS, hSdense, hScor⟩ := habsorb T U hT hU
    Finset.univ Finset.univ_nonempty I (fun t _ => hI t) sample signal
    (fun t _ n _ => hsignal t n) (fun t _ => hcor t)
  let embed : Q ↪ ((Fin (d + 1) → ZMod N) × ZMod N) := ⟨Subtype.val, Subtype.val_injective⟩
  let Q' := S.map embed
  have hQ' : Q'.Nonempty := hS.map
  have hsize : Real.exp (-r) * (Q.card : ℝ) ≤ (Q'.card : ℝ) := by
    simpa only [Q', Finset.card_map, Finset.card_univ, Fintype.card_coe] using hSdense
  refine ⟨w, A, hA, hAi, Q', hQ', ?_, ?_⟩
  · calc
      _ ≤ Real.exp (-(q + r)) * (N : ℝ) ^ (d + 2) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg htotal)) (by positivity)
      _ = Real.exp (-r) * (Real.exp (-q) * (N : ℝ) ^ (d + 2)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-r) * (Q.card : ℝ) := mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := hsize
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := Finset.mem_map.mp ht
    exact ⟨hshift t', start t', len t', hlen t', hend t', hshort t',
      (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hvol t'),
      (Real.exp_le_exp.mpr (neg_le_neg hrC)).trans (hScor t' ht')⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def HasSumTargetIntervals {J : Type*} [Fintype J] {d N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (M : NativeMixedCorrelation (d + 2) N p f)
    (η : J → (Fin 2 → ℤ) → ℂ) (q : ℝ) : Prop :=
  ∃ (j : J) (A : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ),
    (∀ i x, ‖A i x‖ ≤ 1) ∧
    (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
    ∃ Q : Finset ((Fin (d + 1) → ZMod N) × ZMod N), Q.Nonempty ∧
      Real.exp (-q) * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.1 0 ∈ M.shifts ∧ ∃ a len : ℕ,
        0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
        Real.exp (-q) ≤ (len : ℝ) / N ∧ Real.exp (-q) ≤
          ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
            star (f ((∑ k, mixedDifferencePoint t n k : ℤ) : ZMod N)) *
              star (η j (correlationInput (mixedDifferencePoint t n 0)
                (∑ k : Fin (d + 2), mixedDifferencePoint t n k.succ))) *
              ∏ i, A i (mixedDifferencePoint t n)‖

theorem HasSumTargetIntervals.mono {J : Type*} [Fintype J] {d N : ℕ} [NeZero N]
    {p q q' : ℝ} {f : ZMod N → ℂ} {M : NativeMixedCorrelation (d + 2) N p f}
    {η : J → (Fin 2 → ℤ) → ℂ} (H : HasSumTargetIntervals f M η q) (hqq' : q ≤ q') :
    HasSumTargetIntervals f M η q' := by
  obtain ⟨j, A, hA, hAi, Q, hQ, hdense, hcorr⟩ := H
  refine ⟨j, A, hA, hAi, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqq'))
      (pow_nonneg (Nat.cast_nonneg N) _)).trans hdense
  · intro t ht
    obtain ⟨hs, a, len, hlen, hend, hshort, hvol, hc⟩ := hcorr t ht
    exact ⟨hs, a, len, hlen, hend, hshort,
      (Real.exp_le_exp.mpr (neg_le_neg hqq')).trans hvol,
      (Real.exp_le_exp.mpr (neg_le_neg hqq')).trans hc⟩

theorem HasWeightedTargetCubeIntervals.to_sum {J : Type*} [Fintype J] {d N : ℕ} [NeZero N]
    {p q : ℝ} {f : ZMod N → ℂ} {M : NativeMixedCorrelation (d + 2) N p f}
    {η : J → (Fin 2 → ℤ) → ℂ} (H : HasWeightedTargetCubeIntervals f M η q)
    (hf : ∀ z, ‖f z‖ ≤ 1) (hη : ∀ j x, ‖η j x‖ ≤ 1) : HasSumTargetIntervals f M η q := by
  obtain ⟨w, A, hA, hAi, Q, hQ, hdense, hcorr⟩ := H
  obtain ⟨B, hB, hBi, hnorm⟩ := exists_normalized_cube_weights
    (fun z : ℤ => f (z : ZMod N)) (fun z => hf _) η hη w A hA hAi
  refine ⟨w (fun _ => true), B, hB, hBi, Q, hQ, hdense, ?_⟩
  intro t ht
  obtain ⟨hs, a, len, hlen, hend, hshort, hvol, hc⟩ := hcorr t ht
  refine ⟨hs, a, len, hlen, hend, hshort, hvol, ?_⟩
  have hpoint (n : ℤ) :
      conjugationPower (d + 3)
        ((cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N) *
          star (mixedCubeObservable η w (mixedDifferencePoint t n))) * ∏ i, A i (mixedDifferencePoint t n)) =
      star (f ((∑ k, mixedDifferencePoint t n k : ℤ) : ZMod N)) *
        star (η (w (fun _ => true)) (correlationInput (mixedDifferencePoint t n 0)
          (∑ k : Fin (d + 2), mixedDifferencePoint t n k.succ))) *
        ∏ i, B i (mixedDifferencePoint t n) := by
    simpa only [fullCubeSignal_profile] using hnorm (mixedDifferencePoint t n)
  have hc' := hc.trans_eq (norm_expect_conjugationPower (Finset.Ico (a : ℤ) (a + len)) (d + 3)
    (fun n => (cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N) *
      star (mixedCubeObservable η w (mixedDifferencePoint t n))) * ∏ i, A i (mixedDifferencePoint t n))).symm
  simpa only [hpoint] using hc'

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def HasMixedTargetIntervals {J : Type*} {d N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (M : NativeMixedCorrelation (d + 2) N p f)
    (η : J → (Fin (d + 3) → ℤ) → ℂ) (q : ℝ) : Prop :=
  ∃ (j : J) (A : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ),
    (∀ i x, ‖A i x‖ ≤ 1) ∧
    (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
    ∃ Q : Finset ((Fin (d + 1) → ZMod N) × ZMod N), Q.Nonempty ∧
      Real.exp (-q) * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.1 0 ∈ M.shifts ∧ ∃ a len : ℕ,
        0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
        Real.exp (-q) ≤ (len : ℝ) / N ∧ Real.exp (-q) ≤
          ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
            star (f ((∑ k, mixedDifferencePoint t n k : ℤ) : ZMod N)) *
              star (η j (mixedDifferencePoint t n)) * ∏ i, A i (mixedDifferencePoint t n)‖

def HasCommonMixedTargetInterval {J : Type*} {d N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (M : NativeMixedCorrelation (d + 2) N p f)
    (η : J → (Fin (d + 3) → ℤ) → ℂ) (q : ℝ) : Prop :=
  ∃ (j : J) (A : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ),
    (∀ i x, ‖A i x‖ ≤ 1) ∧
    (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
    ∃ a len : ℕ, 0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
      Real.exp (-q) ≤ (len : ℝ) / N ∧
      ∃ Q : Finset ((Fin (d + 1) → ZMod N) × ZMod N), Q.Nonempty ∧
        Real.exp (-q) * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) ∧
        ∀ t ∈ Q, t.1 0 ∈ M.shifts ∧ Real.exp (-q) ≤
          ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
            star (f ((∑ k, mixedDifferencePoint t n k : ℤ) : ZMod N)) *
              star (η j (mixedDifferencePoint t n)) * ∏ i, A i (mixedDifferencePoint t n)‖

theorem HasMixedTargetIntervals.mono {J : Type*} {d N : ℕ} [NeZero N] {p q q' : ℝ}
    {f : ZMod N → ℂ} {M : NativeMixedCorrelation (d + 2) N p f}
    {η : J → (Fin (d + 3) → ℤ) → ℂ} (H : HasMixedTargetIntervals f M η q) (hqq' : q ≤ q') :
    HasMixedTargetIntervals f M η q' := by
  obtain ⟨j, A, hA, hAi, Q, hQ, hdense, hcorr⟩ := H
  refine ⟨j, A, hA, hAi, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqq'))
      (pow_nonneg (Nat.cast_nonneg N) _)).trans hdense
  · intro t ht
    obtain ⟨hs, a, len, hlen, hend, hshort, hvol, hc⟩ := hcorr t ht
    exact ⟨hs, a, len, hlen, hend, hshort,
      (Real.exp_le_exp.mpr (neg_le_neg hqq')).trans hvol,
      (Real.exp_le_exp.mpr (neg_le_neg hqq')).trans hc⟩

theorem HasCommonMixedTargetInterval.mono {J : Type*} {d N : ℕ} [NeZero N] {p q q' : ℝ}
    {f : ZMod N → ℂ} {M : NativeMixedCorrelation (d + 2) N p f}
    {η : J → (Fin (d + 3) → ℤ) → ℂ} (H : HasCommonMixedTargetInterval f M η q) (hqq' : q ≤ q') :
    HasCommonMixedTargetInterval f M η q' := by
  obtain ⟨j, A, hA, hAi, a, len, hlen, hend, hshort, hvol, Q, hQ, hdense, hcorr⟩ := H
  refine ⟨j, A, hA, hAi, a, len, hlen, hend, hshort,
    (Real.exp_le_exp.mpr (neg_le_neg hqq')).trans hvol, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqq'))
      (pow_nonneg (Nat.cast_nonneg N) _)).trans hdense
  · intro t ht
    exact ⟨(hcorr t ht).1, (Real.exp_le_exp.mpr (neg_le_neg hqq')).trans (hcorr t ht).2⟩

end Erdos3

end

section

namespace Erdos3

theorem exists_retained_sum_target_intervals (d : ℕ) {A : ℕ}
    (hI : CyclicNativeInverse (d + 2) A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter
        (fun _ : ReplicatedIndex (mixedCorrelationDegree (d + 2)) => 1) q,
        W.dim ≤ 2 ^ (d + 3) * M.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) e).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence (d + 2) q M.mixed.eval
          (fun k x => W.eval k (fun j => x j.1)) ∧
        HasSumTargetIntervals f M (fun k x => W.eval k (fun j => x j.1)) ((p + C) ^ C) := by
  obtain ⟨a, _, hretained⟩ := exists_retained_target_cube_intervals d hI
  obtain ⟨b, _, habsorb⟩ := exists_absorb_fixed_target_cube_errors d
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  let R := (P + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + R)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let q := (p + a) ^ a
  let r := (q + b) ^ b
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : q + r ≤ (p + C) ^ C := by
    simpa [X, P, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hrC : r ≤ (p + C) ^ C := by linarith
  obtain ⟨q₀, hq₀, hq₀q, M, W, hdim, hsym, E, H⟩ :=
    hretained hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hG
  have hW : ∀ (k : Fin W.outputDim) (x : Fin 2 → ℤ),
      ‖W.eval k (fun j => x j.1)‖ ≤ 1 := fun k x => W.norm_eval k _
  have Hweighted := habsorb hq f hf M (fun k x => W.eval k (fun j => x j.1)) hW H
  exact ⟨q₀, hq₀, hq₀q.trans hqC, M, W, hdim, hsym, E, (Hweighted.to_sum hf hW).mono hrC⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem HasMixedTargetIntervals.common {J : Type*} {d N : ℕ} [NeZero N] {p q : ℝ}
    {f : ZMod N → ℂ} {M : NativeMixedCorrelation (d + 2) N p f}
    {η : J → (Fin (d + 3) → ℤ) → ℂ} (H : HasMixedTargetIntervals f M η q)
    (hq : 0 ≤ q) (hN : Real.exp (2 * q + 8) ≤ (N : ℝ))
    (hf : ∀ x, ‖f x‖ ≤ 1) (hη : ∀ j x, ‖η j x‖ ≤ 1) :
    HasCommonMixedTargetInterval f M η (5 * q + 10) := by
  classical
  obtain ⟨j, A, hA, hAi, Q, hQ, hdense, hcorr⟩ := H
  have hdata (t : Q) := hcorr t.val t.property
  choose hshift start len hlen hend hshort hvol hcor using hdata
  let signal (t : Q) (n : ℤ) :=
    star (f ((∑ k, mixedDifferencePoint t.val n k : ℤ) : ZMod N)) *
      star (η j (mixedDifferencePoint t.val n)) * ∏ i, A i (mixedDifferencePoint t.val n)
  let : Nonempty Q := hQ.to_subtype
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hsignal (t : Q) (n : ℤ) : ‖signal t n‖ ≤ 1 := by
    dsimp only [signal]
    rw [norm_mul, norm_mul, norm_star, norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _)
      ((mul_le_of_le_one_left (norm_nonneg _) (hf _)).trans (hη j _))).trans
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hA i _)
  obtain ⟨S, _, hS, hSdense, a, len', hlen', hend', hshort', hvol', hScor⟩ :=
    exists_common_integer_interval hq hN Finset.univ Finset.univ_nonempty start len
      (fun t _ => hend t) (fun t _ => hshort t)
      (fun t _ => (le_div_iff₀ hNpos).mp (hvol t)) signal
      (fun t _ n => hsignal t n) (fun t _ => hcor t)
  let embed : Q ↪ ((Fin (d + 1) → ZMod N) × ZMod N) := ⟨Subtype.val, Subtype.val_injective⟩
  let Q' := S.map embed
  have hsize : Real.exp (-(4 * q + 10)) * (Q.card : ℝ) ≤ (Q'.card : ℝ) := by
    simpa only [Q', Finset.card_map, Finset.card_univ, Fintype.card_coe] using hSdense
  have hbudget : q + 1 ≤ 5 * q + 10 := by linarith
  refine ⟨j, A, hA, hAi, a, len', hlen', hend', hshort', ?_, Q', hS.map, ?_, ?_⟩
  · apply (le_div_iff₀ hNpos).mpr
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hbudget)) hNpos.le).trans hvol'
  · calc
      _ = Real.exp (-(4 * q + 10)) * (Real.exp (-q) * (N : ℝ) ^ (d + 2)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-(4 * q + 10)) * (Q.card : ℝ) :=
        mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := hsize
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := Finset.mem_map.mp ht
    exact ⟨hshift t', (Real.exp_le_exp.mpr (neg_le_neg hbudget)).trans (hScor t' ht')⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_separated_sum_intervals (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p q r : ℝ}, 0 ≤ q → r ≤ q →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) →
      ∀ (M : NativeMixedCorrelation (d + 2) N p f)
        (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) r),
      (∀ (e : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) k x,
        W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) e).symm j)) = W.eval k x) →
      HasSumTargetIntervals f M (fun k x => W.eval k (fun j => x j.1)) q →
      HasMixedTargetIntervals f M
        (fun k x => (W.tensorPower (d + 2).factorial).eval k
          (mixedReplicatedInput (x 0) (fun j => x j.succ))) ((q + C) ^ C) := by
  obtain ⟨a, _, hseparate⟩ := NativeMultidegreeNilcharacter.exists_mixed_separated_family
    (d + 2) (by omega)
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + P)
  refine ⟨C, hC, ?_⟩
  intro N _ p q r hq hrq f hf M W hsym H
  classical
  let v := (q + a) ^ a
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have htotal : q + v ≤ (q + C) ^ C := by
    simpa [X, P, v, Polynomial.eval₂_pow] using hbudget q hq
  have hqC : q ≤ (q + C) ^ C := by linarith
  have hvC : v ≤ (q + C) ^ C := by linarith
  obtain ⟨j, A, hA, hAi, Q, hQ, hdense, hcorr⟩ := H
  have hdata (t : Q) := hcorr t.val t.property
  choose hshift start len hlen hend hshort hvol hcor using hdata
  let I (t : Q) := Finset.Ico (start t : ℤ) (start t + len t)
  let sample (t : Q) := mixedDifferencePoint t.val
  let signal (t : Q) (n : ℤ) := star (f ((∑ k, sample t n k : ℤ) : ZMod N))
  let : Nonempty Q := hQ.to_subtype
  have hI (t : Q) : (I t).Nonempty := Finset.nonempty_Ico.mpr (by
    have hh := hlen t
    change (start t : ℤ) < start t + len t
    omega)
  obtain ⟨a', B, hB, hBi, S, _, hS, hSdense, hScor⟩ := hseparate (W.mono hrq) hsym
    Finset.univ Finset.univ_nonempty I (fun t _ => hI t) sample signal
    (fun t _ n _ => by simpa only [signal, norm_star] using hf _) j A hA hAi
    (fun t _ => by simpa only [I, signal, sample, mixedReplicatedInput_diagonal, NativeMultidegreeNilcharacter.mono_eval] using hcor t)
  let embed : Q ↪ ((Fin (d + 1) → ZMod N) × ZMod N) := ⟨Subtype.val, Subtype.val_injective⟩
  let Q' := S.map embed
  have hsize : Real.exp (-v) * (Q.card : ℝ) ≤ (Q'.card : ℝ) := by
    simpa only [Q', Finset.card_map, Finset.card_univ, Fintype.card_coe] using hSdense
  have htarget (x : Fin (d + 3) → ℤ) :
      (W.tensorPower (d + 2).factorial).eval (mixedPermutationTensorIndex W.outputDim a')
        (mixedReplicatedInput (x 0) (fun j => x j.succ)) =
      mixedPermutationProduct (W.mono hrq).eval a' x :=
    (W.mixedPermutationProduct_tensorPower a' x).symm
  refine ⟨mixedPermutationTensorIndex W.outputDim a', B, hB, hBi, Q', hS.map, ?_, ?_⟩
  · calc
      _ ≤ Real.exp (-(q + v)) * (N : ℝ) ^ (d + 2) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg htotal)) (by positivity)
      _ = Real.exp (-v) * (Real.exp (-q) * (N : ℝ) ^ (d + 2)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-v) * (Q.card : ℝ) := mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := hsize
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := Finset.mem_map.mp ht
    refine ⟨hshift t', start t', len t', hlen t', hend t', hshort t',
      (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hvol t'), ?_⟩
    simpa only [htarget, I, signal, sample, embed, Function.Embedding.coeFn_mk] using (Real.exp_le_exp.mpr (neg_le_neg hvC)).trans (hScor t' ht')

end Erdos3

end

end OAI
