import OAI.Combinatorics.Progressions.Nilpotent.NiltestVerticalBounds

namespace OAI

section

namespace Erdos3

theorem exists_vertical_pair_precision :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → ∃ q r rho eta : ℝ,
      p ≤ q ∧ p ≤ r ∧ q ≤ (p + C) ^ C ∧ r ≤ (p + C) ^ C ∧
      verticalDecompositionBudget q ≤ (p + C) ^ C ∧
      verticalDecompositionBudget r ≤ (p + C) ^ C ∧
      0 < rho ∧ 0 < eta ∧ rho⁻¹ ≤ Real.exp q ∧ eta⁻¹ ≤ Real.exp r ∧
      rho + Real.exp (verticalDecompositionBudget q) * eta ≤ Real.exp (-p) / 2 ∧
      Real.exp (-((p + C) ^ C)) ≤ (Real.exp (-p) / 2) /
        (Real.exp (verticalDecompositionBudget q) * Real.exp (verticalDecompositionBudget r)) := by
  obtain ⟨c, _, hV⟩ := exists_verticalDecompositionBudget_bound
  let Q : Polynomial ℕ := Polynomial.X + 4
  let R : Polynomial ℕ := Q + (Q + Polynomial.C c) ^ c
  let P : Polynomial ℕ := R + (R + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  let q := p + 4
  let r := q + (q + c) ^ c
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hf : 0 ≤ (q + c) ^ c := by positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hqr : q ≤ r := by dsimp [r]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hg : 0 ≤ (r + c) ^ c := by positivity
  have hb : r + (r + c) ^ c ≤ (p + C) ^ C := by
    simpa [P, R, Q, r, q, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + C) ^ C := by linarith
  have hVq := hV q hq
  have hVr := hV r hr
  have hVqC : verticalDecompositionBudget q ≤ (p + C) ^ C := by
    have hfR : (q + c) ^ c ≤ r := by dsimp [r]; linarith
    exact hVq.trans (hfR.trans hrC)
  have hVrC : verticalDecompositionBudget r ≤ (p + C) ^ C := by linarith
  have hscaled : Real.exp (verticalDecompositionBudget q) * Real.exp (-r) ≤ Real.exp (-q) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [r]
    linarith
  have he4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hsplit : Real.exp (-q) * Real.exp 4 = Real.exp (-p) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [q]
    ring
  have hfour : Real.exp (-q) * 4 ≤ Real.exp (-p) := by
    rw [← hsplit]
    exact mul_le_mul_of_nonneg_left he4 (Real.exp_nonneg _)
  have hsmall : Real.exp (-q) + Real.exp (verticalDecompositionBudget q) * Real.exp (-r) ≤
      Real.exp (-p) / 2 := by linarith
  refine ⟨q, r, Real.exp (-q), Real.exp (-r), hpq, hpq.trans hqr, hqr.trans hrC, hrC,
    hVqC, hVrC, Real.exp_pos _, Real.exp_pos _, ?_, ?_, hsmall, ?_⟩
  · simp only [Real.exp_neg, inv_inv, le_refl]
  · simp only [Real.exp_neg, inv_inv, le_refl]
  · apply (le_div_iff₀ (mul_pos (Real.exp_pos _) (Real.exp_pos _))).mpr
    have hloss : q + verticalDecompositionBudget q + verticalDecompositionBudget r ≤ (p + C) ^ C := by
      have hstep : q + verticalDecompositionBudget q ≤ r := by dsimp [r]; linarith
      linarith
    calc
      _ ≤ Real.exp (-(q + verticalDecompositionBudget q + verticalDecompositionBudget r)) *
          (Real.exp (verticalDecompositionBudget q) * Real.exp (verticalDecompositionBudget r)) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by positivity)
      _ = Real.exp (-q) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-p) / 2 := by linarith [Real.exp_pos (-q)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem norm_expect_three_le {G : Type*} [Fintype G] [Nonempty G]
    (u v w : G → ℂ) {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu : ∀ x, ‖u x‖ ≤ A) (hv : ∀ x, ‖v x‖ ≤ B) (hw : ∀ x, ‖w x‖ ≤ C) :
    ‖𝔼 x, u x * v x * w x‖ ≤ A * B * C := by
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply Finset.expect_le Finset.univ_nonempty
  intro x _
  simp only [norm_mul]
  exact mul_le_mul (mul_le_mul (hu x) (hv x) (norm_nonneg _) hA) (hw x)
    (norm_nonneg _) (mul_nonneg hA hB)

theorem exists_correlating_partner_components {G I J : Type*}
    [AddCommGroup G] [Fintype G] [Fintype I] [Fintype J]
    (U Q R : G → ℂ) (V : I → G → ℂ) (W : J → G → ℂ) (h : G)
    {delta C D rho eta : ℝ} (hdelta : 0 < delta) (hC : 0 < C) (hD : 0 < D)
    (heta : 0 ≤ eta) (hI : (Fintype.card I : ℝ) ≤ C) (hJ : (Fintype.card J : ℝ) ≤ D)
    (hU : ∀ x, ‖U x‖ ≤ 1) (hR : ∀ x, ‖R x‖ ≤ 1)
    (hV : ∀ i x, ‖V i x‖ ≤ 1)
    (hQapprox : ∀ x, ‖Q x - ∑ i, V i x‖ ≤ rho)
    (hRapprox : ∀ x, ‖R x - ∑ j, W j x‖ ≤ eta)
    (hsmall : rho + C * eta ≤ delta / 2)
    (hcorr : delta ≤ ‖𝔼 x, U x * Q x * R (x + h)‖) :
    ∃ i j, (delta / 2) / (C * D) ≤ ‖𝔼 x, U x * V i x * W j (x + h)‖ := by
  have hrho : 0 ≤ rho := (norm_nonneg _).trans (hQapprox 0)
  let ea : G → ℂ := fun x => Q x - ∑ i, V i x
  let eb : I → G → ℂ := fun _ x => R x - ∑ j, W j x
  have hfirst : ‖𝔼 x, U x * ea x * R (x + h)‖ ≤ rho := by
    have h := norm_expect_three_le U ea (fun x => R (x + h)) (by norm_num : (0 : ℝ) ≤ 1)
      hrho hU hQapprox (fun x => hR (x + h))
    simpa only [one_mul, mul_one] using h
  have hsecond (i : I) : ‖𝔼 x, U x * V i x * eb i (x + h)‖ ≤ eta := by
    have h := norm_expect_three_le U (V i) (fun x => eb i (x + h))
      (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
      hU (hV i) (fun x => hRapprox (x + h))
    simpa only [one_mul] using h
  apply exists_model_partner Q R ea U V (fun _ j => W j) eb (fun _ => 1) (fun _ _ => 1)
    (fun x => by dsimp only [ea]; simp only [one_mul]; ring)
    (fun _ x => by dsimp only [eb]; simp only [one_mul]; ring)
    h hdelta hC hD
  · simpa only [norm_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using hI
  · intro _
    simpa only [norm_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using hJ
  · exact hfirst
  · exact hsecond
  · simp only [norm_one, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact (add_le_add le_rfl (mul_le_mul_of_nonneg_right hI heta)).trans hsmall
  · exact hcorr

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_fixed_partner_components {G K : Type*} {I J : K → Type*}
    [AddCommGroup G] [Fintype G] [Fintype K]
    [∀ k, Fintype (I k)] [∀ k, Fintype (J k)]
    (H : Finset G) (hH : H.Nonempty) (U : G → K → G → ℂ) (Q R : K → G → ℂ)
    (V : ∀ k, I k → G → ℂ) (W : ∀ k, J k → G → ℂ)
    {delta C D rho eta budget : ℝ} (hdelta : 0 < delta) (hC : 0 < C) (hD : 0 < D)
    (heta : 0 ≤ eta) (hI : ∀ k, (Fintype.card (I k) : ℝ) ≤ C)
    (hJ : ∀ k, (Fintype.card (J k) : ℝ) ≤ D) (hCD : C * D ≤ Real.exp budget)
    (hU : ∀ h ∈ H, ∀ k x, ‖U h k x‖ ≤ 1) (hR : ∀ k x, ‖R k x‖ ≤ 1)
    (hV : ∀ k i x, ‖V k i x‖ ≤ 1)
    (hQapprox : ∀ k x, ‖Q k x - ∑ i, V k i x‖ ≤ rho)
    (hRapprox : ∀ k x, ‖R k x - ∑ j, W k j x‖ ≤ eta)
    (hsmall : rho + C * eta ≤ delta / 2)
    (hcorr : ∀ h ∈ H, ∀ k, delta ≤ ‖𝔼 x, U h k x * Q k x * R k (x + h)‖) :
    ∃ (q : ∀ k, I k × J k) (S : Finset G), S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-budget * Fintype.card K) * H.card ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ k,
        (delta / 2) / (C * D) ≤ ‖𝔼 x, U h k x * V k (q k).1 x * W k (q k).2 (x + h)‖ := by
  let rel : ∀ (_ : G) (k : K), I k × J k → Prop := fun h k p =>
    (delta / 2) / (C * D) ≤ ‖𝔼 x, U h k x * V k p.1 x * W k p.2 (x + h)‖
  apply exists_large_fixed_dependent_choices H hH rel
  · intro h hh k
    obtain ⟨i, j, hij⟩ := exists_correlating_partner_components (U h k) (Q k) (R k) (V k) (W k) h
      hdelta hC hD heta (hI k) (hJ k) (hU h hh k) (hR k) (hV k)
      (hQapprox k) (hRapprox k) hsmall (hcorr h hh k)
    exact ⟨(i, j), hij⟩
  · intro k
    rw [Fintype.card_prod, Nat.cast_mul]
    exact (mul_le_mul (hI k) (hJ k) (Nat.cast_nonneg _) hC.le).trans hCD

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_native_vertical_pair_on_finset
    {X σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
    (D : RationalFilteredNilmanifold L s d) (D' : RationalFilteredNilmanifold M s e)
    {w : σ → ℕ} (Q : D.Niltest w) (R : D'.Niltest w)
    {p q delta rho eta : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hdelta : 0 < delta)
    (hrho : 0 < rho) (heta : 0 < eta) (hrhop : rho⁻¹ ≤ Real.exp p) (hetaq : eta⁻¹ ≤ Real.exp q)
    (hQc : Q.ComplexityLE p) (hRc : R.ComplexityLE q)
    (hQcap : (Q.normBound : ℝ) ≤ 1) (hRcap : (R.normBound : ℝ) ≤ 1)
    (hsmall : rho + Real.exp (verticalDecompositionBudget p) * eta ≤ delta / 2)
    (B : Finset X) (hB : B.Nonempty) (sample : X → σ → ℤ) (U : X → ℂ)
    (hU : ∀ x ∈ B, ‖U x‖ ≤ 1)
    (hcorr : delta ≤ ‖𝔼 x ∈ B, U x * Q.eval (sample x) * R.eval (sample x)‖) :
    ∃ (freq : L →ₗ[ℚ] ℚ) (freq' : M →ₗ[ℚ] ℚ) (V : D.Niltest w) (W : D'.Niltest w),
      V.ComplexityLE p ∧ V.orbit = Q.orbit ∧ V.normBound = Q.normBound ∧
      W.ComplexityLE q ∧ W.orbit = R.orbit ∧ W.normBound = R.normBound ∧
      (∀ i, rationalLogHeight (freq (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ i, rationalLogHeight (freq' (D'.basis i)) ≤ verticalDecompositionBudget q) ∧
      (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        V.observable (z • x) = character ((realifyFunctional freq z.coord : ℝ) : CircleFourier.Circle) *
          V.observable x) ∧
      (∀ z, z ∈ D'.filtration.realification.subgroup s → ∀ x,
        W.observable (z • x) = character ((realifyFunctional freq' z.coord : ℝ) : CircleFourier.Circle) *
          W.observable x) ∧
      (delta / 2) / (Real.exp (verticalDecompositionBudget p) * Real.exp (verticalDecompositionBudget q)) ≤
        ‖𝔼 x ∈ B, U x * V.eval (sample x) * W.eval (sample x)‖ := by
  obtain ⟨I, instI, freqV, V, hI, hheightV, hcertV, hvertV, _, _, happroxV⟩ :=
    Q.exists_vertical_decomposition_preserving_bounds hp hQc hrho hrhop
  let := instI
  obtain ⟨J, instJ, freqW, W, hJ, hheightW, hcertW, hvertW, _, _, happroxW⟩ :=
    R.exists_vertical_decomposition_preserving_bounds hq hRc heta hetaq
  let := instJ
  obtain ⟨i, j, hbias⟩ := exists_correlating_components_on_finset B hB U
    (fun x => Q.eval (sample x)) (fun x => R.eval (sample x))
    (fun i x => (V i).eval (sample x)) (fun j x => (W j).eval (sample x))
    hdelta (Real.exp_pos _) (Real.exp_pos _) hrho.le heta.le hI hJ hU
    (fun x _ => (R.norm_eval_le (sample x)).trans hRcap)
    (fun i x _ => ((V i).norm_eval_le (sample x)).trans (by rw [(hcertV i).2.2.1]; exact hQcap))
    (fun x _ => by simpa only [norm_sub_rev] using happroxV (sample x))
    (fun x _ => by simpa only [norm_sub_rev] using happroxW (sample x)) hsmall hcorr
  exact ⟨freqV i, freqW j, V i, W j, (hcertV i).1, (hcertV i).2.1, (hcertV i).2.2.1,
    (hcertW j).1, (hcertW j).2.1, (hcertW j).2.2.1, hheightV i, hheightW j, hvertV i, hvertW j, hbias⟩

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_fixed_native_vertical_partners
    {K σ : Type*} [Fintype K] {L L' : K → Type*}
    [∀ k, LieRing (L k)] [∀ k, LieAlgebra ℚ (L k)]
    [∀ k, LieRing (L' k)] [∀ k, LieAlgebra ℚ (L' k)] {s : ℕ} {d d' : K → ℕ}
    [∀ k, TopologicalSpace (ℝ ⊗[ℚ] L k)] [∀ k, IsTopologicalAddGroup (ℝ ⊗[ℚ] L k)]
    [∀ k, ContinuousSMul ℝ (ℝ ⊗[ℚ] L k)] [∀ k, T2Space (ℝ ⊗[ℚ] L k)]
    [∀ k, TopologicalSpace (ℝ ⊗[ℚ] L' k)] [∀ k, IsTopologicalAddGroup (ℝ ⊗[ℚ] L' k)]
    [∀ k, ContinuousSMul ℝ (ℝ ⊗[ℚ] L' k)] [∀ k, T2Space (ℝ ⊗[ℚ] L' k)]
    (D : ∀ k, RationalFilteredNilmanifold (L k) s (d k))
    (D' : ∀ k, RationalFilteredNilmanifold (L' k) s (d' k)) {w : σ → ℕ}
    (Q : ∀ k, (D k).Niltest w) (R : ∀ k, (D' k).Niltest w)
    {p q delta rho eta : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hdelta : 0 < delta)
    (hrho : 0 < rho) (heta : 0 < eta) (hrhop : rho⁻¹ ≤ Real.exp p) (hetaq : eta⁻¹ ≤ Real.exp q)
    (hQc : ∀ k, (Q k).ComplexityLE p) (hRc : ∀ k, (R k).ComplexityLE q)
    (hQcap : ∀ k, ((Q k).normBound : ℝ) ≤ 1) (hRcap : ∀ k, ((R k).normBound : ℝ) ≤ 1)
    (hsmall : rho + Real.exp (verticalDecompositionBudget p) * eta ≤ delta / 2)
    (N : ℕ) [NeZero N] (H : Finset (ZMod N)) (hH : H.Nonempty)
    (U : ZMod N → K → ZMod N → ℂ) (hU : ∀ h ∈ H, ∀ k n, ‖U h k n‖ ≤ 1)
    (hcorr : ∀ h ∈ H, ∀ k, delta ≤ ‖𝔼 n,
      U h k n * (Q k).evalCyclic N (fun _ => n) * (R k).evalCyclic N (fun _ => n + h)‖) :
    ∃ (freq : ∀ k, L k →ₗ[ℚ] ℚ) (freq' : ∀ k, L' k →ₗ[ℚ] ℚ)
      (V : ∀ k, (D k).Niltest w) (W : ∀ k, (D' k).Niltest w) (S : Finset (ZMod N)),
      S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-(verticalDecompositionBudget p + verticalDecompositionBudget q) * Fintype.card K) *
        H.card ≤ (S.card : ℝ) ∧
      (∀ k, (V k).ComplexityLE p ∧ (V k).orbit = (Q k).orbit ∧ ((V k).normBound : ℝ) ≤ 1) ∧
      (∀ k, (W k).ComplexityLE q ∧ (W k).orbit = (R k).orbit ∧ ((W k).normBound : ℝ) ≤ 1) ∧
      (∀ k i, rationalLogHeight (freq k ((D k).basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ k i, rationalLogHeight (freq' k ((D' k).basis i)) ≤ verticalDecompositionBudget q) ∧
      (∀ k (z : (D k).RealGroup), z ∈ (D k).filtration.realification.subgroup s → ∀ x,
        (V k).observable (z • x) =
          character ((realifyFunctional (freq k) z.coord : ℝ) : CircleFourier.Circle) * (V k).observable x) ∧
      (∀ k (z : (D' k).RealGroup), z ∈ (D' k).filtration.realification.subgroup s → ∀ x,
        (W k).observable (z • x) =
          character ((realifyFunctional (freq' k) z.coord : ℝ) : CircleFourier.Circle) * (W k).observable x) ∧
      ∀ h ∈ S, ∀ k, (delta / 2) /
        (Real.exp (verticalDecompositionBudget p) * Real.exp (verticalDecompositionBudget q)) ≤
        ‖𝔼 n, U h k n * (V k).evalCyclic N (fun _ => n) * (W k).evalCyclic N (fun _ => n + h)‖ := by
  classical
  choose I instI freqV V hI hheightV hcertV hvertV hintV hobsV happroxV using
    fun k => (Q k).exists_vertical_decomposition_preserving_bounds hp (hQc k) hrho hrhop
  let : ∀ k, Fintype (I k) := instI
  choose J instJ freqW W hJ hheightW hcertW hvertW hintW hobsW happroxW using
    fun k => (R k).exists_vertical_decomposition_preserving_bounds hq (hRc k) heta hetaq
  let : ∀ k, Fintype (J k) := instJ
  have hVcap (k : K) (i : I k) (n : ZMod N) : ‖(V k i).evalCyclic N (fun _ => n)‖ ≤ 1 := by
    apply ((V k i).norm_evalCyclic_le N _).trans
    rw [(hcertV k i).2.2.1]
    exact hQcap k
  have hRcap' (k : K) (n : ZMod N) : ‖(R k).evalCyclic N (fun _ => n)‖ ≤ 1 :=
    ((R k).norm_evalCyclic_le N _).trans (hRcap k)
  have hQa (k : K) (n : ZMod N) :
      ‖(Q k).evalCyclic N (fun _ => n) - ∑ i, (V k i).evalCyclic N (fun _ => n)‖ ≤ rho := by
    simpa only [RationalFilteredNilmanifold.Niltest.evalCyclic, norm_sub_rev] using
      happroxV k (fun _ => (n.val : ℤ))
  have hRa (k : K) (n : ZMod N) :
      ‖(R k).evalCyclic N (fun _ => n) - ∑ j, (W k j).evalCyclic N (fun _ => n)‖ ≤ eta := by
    simpa only [RationalFilteredNilmanifold.Niltest.evalCyclic, norm_sub_rev] using
      happroxW k (fun _ => (n.val : ℤ))
  have hcount : Real.exp (verticalDecompositionBudget p) * Real.exp (verticalDecompositionBudget q) ≤
      Real.exp (verticalDecompositionBudget p + verticalDecompositionBudget q) :=
    (Real.exp_add _ _).symm.le
  obtain ⟨choices, S, hsub, hSn, hsize, hbias⟩ := exists_fixed_partner_components H hH U
    (fun k n => (Q k).evalCyclic N (fun _ => n)) (fun k n => (R k).evalCyclic N (fun _ => n))
    (fun k i n => (V k i).evalCyclic N (fun _ => n)) (fun k j n => (W k j).evalCyclic N (fun _ => n))
    hdelta (Real.exp_pos _) (Real.exp_pos _) heta.le hI hJ hcount hU hRcap' hVcap hQa hRa hsmall hcorr
  refine ⟨(fun k => freqV k (choices k).1), (fun k => freqW k (choices k).2),
    (fun k => V k (choices k).1), (fun k => W k (choices k).2), S, hsub, hSn, hsize, ?_, ?_,
    (fun k => hheightV k (choices k).1), (fun k => hheightW k (choices k).2),
    (fun k => hvertV k (choices k).1), (fun k => hvertW k (choices k).2), hbias⟩
  · intro k
    refine ⟨(hcertV k (choices k).1).1, (hcertV k (choices k).1).2.1, ?_⟩
    rw [(hcertV k (choices k).1).2.2.1]
    exact hQcap k
  · intro k
    refine ⟨(hcertW k (choices k).2).1, (hcertW k (choices k).2).2.1, ?_⟩
    rw [(hcertW k (choices k).2).2.2.1]
    exact hRcap k

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_native_vertical_pair_power :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X σ L M : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s d e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (D : RationalFilteredNilmanifold L s d) (D' : RationalFilteredNilmanifold M s e)
      {w : σ → ℕ} (Q : D.Niltest w) (R : D'.Niltest w) (p : ℝ), 0 ≤ p →
      Q.ComplexityLE p → R.ComplexityLE p →
      (Q.normBound : ℝ) ≤ 1 → (R.normBound : ℝ) ≤ 1 →
      ∀ (B : Finset X), B.Nonempty → ∀ (sample : X → σ → ℤ) (U : X → ℂ),
      (∀ x ∈ B, ‖U x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ B, U x * Q.eval (sample x) * R.eval (sample x)‖ →
      ∃ (freq : L →ₗ[ℚ] ℚ) (freq' : M →ₗ[ℚ] ℚ) (V : D.Niltest w) (W : D'.Niltest w),
        V.ComplexityLE ((p + C) ^ C) ∧ V.orbit = Q.orbit ∧ V.normBound = Q.normBound ∧
        W.ComplexityLE ((p + C) ^ C) ∧ W.orbit = R.orbit ∧ W.normBound = R.normBound ∧
        (∀ i, rationalLogHeight (freq (D.basis i)) ≤ (p + C) ^ C) ∧
        (∀ i, rationalLogHeight (freq' (D'.basis i)) ≤ (p + C) ^ C) ∧
        (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
          V.observable (z • x) = character ((realifyFunctional freq z.coord : ℝ) : CircleFourier.Circle) *
            V.observable x) ∧
        (∀ z, z ∈ D'.filtration.realification.subgroup s → ∀ x,
          W.observable (z • x) = character ((realifyFunctional freq' z.coord : ℝ) : CircleFourier.Circle) *
            W.observable x) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 x ∈ B, U x * V.eval (sample x) * W.eval (sample x)‖ := by
  obtain ⟨C, hC, hprecision⟩ := exists_vertical_pair_precision
  refine ⟨C, hC, ?_⟩
  intro X σ L M _ _ _ _ s d e _ _ _ _ _ _ _ _ D D' w Q R p hp hQ hR hQcap hRcap
    B hB sample U hU hcorr
  obtain ⟨q, r, rho, eta, hpq, hpr, hqC, hrC, hVq, hVr, hrho, heta, hrhoq, hetar, hsmall, hloss⟩ :=
    hprecision p hp
  obtain ⟨freq, freq', V, W, hVc, hVo, hVn, hWc, hWo, hWn, hVheight, hWheight, hvertV, hvertW, hbias⟩ :=
    exists_native_vertical_pair_on_finset D D' Q R (hp.trans hpq) (hp.trans hpr)
      (Real.exp_pos _) hrho heta hrhoq hetar (hQ.mono hpq) (hR.mono hpr)
      hQcap hRcap hsmall B hB sample U hU hcorr
  exact ⟨freq, freq', V, W, hVc.mono hqC, hVo, hVn, hWc.mono hrC, hWo, hWn,
    fun i => (hVheight i).trans hVq, fun i => (hWheight i).trans hVr, hvertV, hvertW, hloss.trans hbias⟩

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_fixed_native_vertical_power :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {K σ : Type*} [Fintype K] {L L' : K → Type*}
      [∀ k, LieRing (L k)] [∀ k, LieAlgebra ℚ (L k)]
      [∀ k, LieRing (L' k)] [∀ k, LieAlgebra ℚ (L' k)] {s : ℕ} {d d' : K → ℕ}
      [∀ k, TopologicalSpace (ℝ ⊗[ℚ] L k)] [∀ k, IsTopologicalAddGroup (ℝ ⊗[ℚ] L k)]
      [∀ k, ContinuousSMul ℝ (ℝ ⊗[ℚ] L k)] [∀ k, T2Space (ℝ ⊗[ℚ] L k)]
      [∀ k, TopologicalSpace (ℝ ⊗[ℚ] L' k)] [∀ k, IsTopologicalAddGroup (ℝ ⊗[ℚ] L' k)]
      [∀ k, ContinuousSMul ℝ (ℝ ⊗[ℚ] L' k)] [∀ k, T2Space (ℝ ⊗[ℚ] L' k)]
      (D : ∀ k, RationalFilteredNilmanifold (L k) s (d k))
      (D' : ∀ k, RationalFilteredNilmanifold (L' k) s (d' k)) {w : σ → ℕ}
      (Q : ∀ k, (D k).Niltest w) (R : ∀ k, (D' k).Niltest w)
      {p : ℝ}, 0 ≤ p → (Fintype.card K : ℝ) ≤ p →
      (∀ k, (Q k).ComplexityLE p) → (∀ k, (R k).ComplexityLE p) →
      (∀ k, (Q k).normBound ≤ 1) → (∀ k, (R k).normBound ≤ 1) →
      ∀ (N : ℕ) [NeZero N] (H : Finset (ZMod N)), H.Nonempty →
      ∀ U : ZMod N → K → ZMod N → ℂ,
      (∀ h ∈ H, ∀ k n, ‖U h k n‖ ≤ 1) →
      (∀ h ∈ H, ∀ k, Real.exp (-p) ≤ ‖𝔼 n,
        U h k n * (Q k).evalCyclic N (fun _ => n) * (R k).evalCyclic N (fun _ => n + h)‖) →
      ∃ (freq : ∀ k, L k →ₗ[ℚ] ℚ) (freq' : ∀ k, L' k →ₗ[ℚ] ℚ)
        (V : ∀ k, (D k).Niltest w) (W : ∀ k, (D' k).Niltest w) (S : Finset (ZMod N)),
        S ⊆ H ∧ S.Nonempty ∧ Real.exp (-((p + C) ^ C)) * H.card ≤ (S.card : ℝ) ∧
        (∀ k, (V k).ComplexityLE ((p + C) ^ C) ∧ (V k).orbit = (Q k).orbit ∧ (V k).normBound ≤ 1) ∧
        (∀ k, (W k).ComplexityLE ((p + C) ^ C) ∧ (W k).orbit = (R k).orbit ∧ (W k).normBound ≤ 1) ∧
        (∀ k i, rationalLogHeight (freq k ((D k).basis i)) ≤ (p + C) ^ C) ∧
        (∀ k i, rationalLogHeight (freq' k ((D' k).basis i)) ≤ (p + C) ^ C) ∧
        (∀ k z, z ∈ (D k).filtration.realification.subgroup s → ∀ x,
          (V k).observable (z • x) = character
            ((realifyFunctional (freq k) z.coord : ℝ) : CircleFourier.Circle) * (V k).observable x) ∧
        (∀ k z, z ∈ (D' k).filtration.realification.subgroup s → ∀ x,
          (W k).observable (z • x) = character
            ((realifyFunctional (freq' k) z.coord : ℝ) : CircleFourier.Circle) * (W k).observable x) ∧
        ∀ h ∈ S, ∀ k, Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n,
          U h k n * (V k).evalCyclic N (fun _ => n) * (W k).evalCyclic N (fun _ => n + h)‖ := by
  obtain ⟨c, _, hprecision⟩ := exists_vertical_pair_precision
  let X : Polynomial ℕ := Polynomial.X
  let B := (X + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * B * X + B)
  refine ⟨C, hC, ?_⟩
  intro K σ _ L L' _ _ _ _ s d d' _ _ _ _ _ _ _ _ D D' w Q R p hp hK hQc hRc hQcap hRcap
    N _ H hH U hU hcorr
  obtain ⟨q, r, rho, eta, hpq, hpr, hqC, hrC, hVq, hVr, hrho, heta, hrhoq, hetar, hsmall, hloss⟩ :=
    hprecision p hp
  have hB0 : 0 ≤ (p + c) ^ c := by positivity
  have hbud : 2 * (p + c) ^ c * p + (p + c) ^ c ≤ (p + C) ^ C := by
    simpa [X, B, Polynomial.eval₂_pow] using hbudget p hp
  have hBC : (p + c) ^ c ≤ (p + C) ^ C := by nlinarith
  have hsizeBudget : (verticalDecompositionBudget q + verticalDecompositionBudget r) *
      Fintype.card K ≤ (p + C) ^ C := by
    calc
      _ ≤ (2 * (p + c) ^ c) * Fintype.card K :=
        mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
      _ ≤ (2 * (p + c) ^ c) * p := mul_le_mul_of_nonneg_left hK (by positivity)
      _ ≤ (p + C) ^ C := by linarith
  obtain ⟨freq, freq', V, W, S, hsub, hSn, hsize, hV, hW, hheightV, hheightW, hvertV, hvertW, hbias⟩ :=
    exists_fixed_native_vertical_partners D D' Q R (hp.trans hpq) (hp.trans hpr)
      (Real.exp_pos _) hrho heta hrhoq hetar
      (fun k => (hQc k).mono hpq) (fun k => (hRc k).mono hpr)
      hQcap hRcap hsmall N H hH U hU hcorr
  refine ⟨freq, freq', V, W, S, hsub, hSn, ?_, ?_, ?_, ?_, ?_, hvertV, hvertW, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hsizeBudget))
      (Nat.cast_nonneg _)).trans (by simpa only [neg_mul] using hsize)
  · exact fun k => ⟨(hV k).1.mono (hqC.trans hBC), (hV k).2⟩
  · exact fun k => ⟨(hW k).1.mono (hrC.trans hBC), (hW k).2⟩
  · exact fun k i => (hheightV k i).trans (hVq.trans hBC)
  · exact fun k i => (hheightW k i).trans (hVr.trans hBC)
  · exact fun h hh k => (Real.exp_le_exp.mpr (neg_le_neg hBC)).trans (hloss.trans (hbias h hh k))

end Erdos3

end

end OAI
