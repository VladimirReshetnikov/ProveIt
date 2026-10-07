import OAI.Combinatorics.Progressions.Linear.ShiftFailurePositiveBasis

namespace OAI

section

namespace Erdos3.PositiveShiftBasis

open CircleFourier
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

theorem exists_fixed_native_partners :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {s N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
      (B : PositiveShiftBasis s N q a J)
      {I : Type*} {K : I → Type*} [Fintype I] [∀ i, Fintype (K i)]
      {L : I → Type*} {M : ∀ i, K i → Type*}
      [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i k, LieRing (M i k)] [∀ i k, LieAlgebra ℚ (M i k)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [∀ i k, TopologicalSpace (ℝ ⊗[ℚ] M i k)] [∀ i k, IsTopologicalAddGroup (ℝ ⊗[ℚ] M i k)]
      [∀ i k, ContinuousSMul ℝ (ℝ ⊗[ℚ] M i k)] [∀ i k, T2Space (ℝ ⊗[ℚ] M i k)]
      {d : I → ℕ} {e : ∀ i, K i → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i))
      (E : ∀ i k, RationalFilteredNilmanifold (M i k) (s + 1) (e i k))
      (Q : ∀ i, (D i).Niltest (fun _ : Unit => 1))
      (R : ∀ i k, (E i k).Niltest (fun _ : Unit => 1))
      (ea : ZMod N → ℂ) (eb : I → ZMod N → ℂ) (c : I → ℂ) (b : ∀ i, K i → ℂ),
      (∀ n, (a n : ℂ) = (∑ i, c i * (Q i).evalCyclic N (fun _ => n)) + ea n) →
      (∀ i n, (J n : ℂ) = (∑ k, b i k * (R i k).evalCyclic N (fun _ => n)) + eb i n) →
      ∀ {p cap : ℝ}, q ≤ p →
      (∑ i, ‖c i‖) ≤ Real.exp p → (∀ i, (∑ k, ‖b i k‖) ≤ Real.exp p) →
      (∀ n, |J n| ≤ cap) →
      (∀ i, (Q i).ComplexityLE p) → (∀ i k, (R i k).ComplexityLE p) →
      (∀ i, (Q i).normBound ≤ 1) → (∀ i k, (R i k).normBound ≤ 1) →
      (shiftTestingSeminorm (fun n => (J n : ℂ)) B.testingFamily ea +
        ∑ i, ‖c i‖ * shiftTestingSeminorm (fun n => (Q i).evalCyclic N (fun _ => n))
          (translatedTestFamily B.testingFamily) (eb i) ≤ Real.exp (-(2 * q + 2))) →
      (Fintype.card (Sigma K) : ℝ) ≤ Real.exp p →
      ∃ (choice : Fin B.count → Sigma K)
        (freq : ∀ j, L (choice j).1 →ₗ[ℚ] ℚ)
        (freq' : ∀ j, M (choice j).1 (choice j).2 →ₗ[ℚ] ℚ)
        (V : ∀ j, (D (choice j).1).Niltest (fun _ : Unit => 1))
        (W : ∀ j, (E (choice j).1 (choice j).2).Niltest (fun _ : Unit => 1))
        (S : Finset (ZMod N)), S ⊆ B.shifts ∧ S.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (S.card : ℝ) ∧
        (∀ j, (V j).ComplexityLE ((p + C) ^ C) ∧ (V j).orbit = (Q (choice j).1).orbit ∧
          (V j).normBound ≤ 1) ∧
        (∀ j, (W j).ComplexityLE ((p + C) ^ C) ∧
          (W j).orbit = (R (choice j).1 (choice j).2).orbit ∧ (W j).normBound ≤ 1) ∧
        (∀ j i, rationalLogHeight (freq j ((D (choice j).1).basis i)) ≤ (p + C) ^ C) ∧
        (∀ j i, rationalLogHeight (freq' j ((E (choice j).1 (choice j).2).basis i)) ≤ (p + C) ^ C) ∧
        (∀ j z, z ∈ (D (choice j).1).filtration.realification.subgroup (s + 1) → ∀ x,
          (V j).observable (z • x) = character
            ((realifyFunctional (freq j) z.coord : ℝ) : CircleFourier.Circle) * (V j).observable x) ∧
        (∀ j z, z ∈ (E (choice j).1 (choice j).2).filtration.realification.subgroup (s + 1) → ∀ x,
          (W j).observable (z • x) = character
            ((realifyFunctional (freq' j) z.coord : ℝ) : CircleFourier.Circle) * (W j).observable x) ∧
        ∀ h ∈ S, ∀ j, Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n,
          (B.mode h j).evalCyclic N (fun _ => n) * (V j).evalCyclic N (fun _ => n) *
            (W j).evalCyclic N (fun _ => n + h)‖ := by
  classical
  obtain ⟨k, _, hvertical⟩ := exists_fixed_native_vertical_power
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + 2) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C k) ^ k)
  refine ⟨C, hC, ?_⟩
  intro s N _ q a J B I K _ _ L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E Q R ea eb c b
    ha hb p cap hqp hc hbcoeff hJ hQc hRc hQcap hRcap herror hcount
  have hq : 0 ≤ q := (Nat.cast_nonneg B.dim).trans B.geometry.1
  have hp : 0 ≤ p := hq.trans hqp
  let t := (p + 2) ^ 2
  have hpt : p ≤ t := by dsimp [t]; nlinarith [sq_nonneg p]
  have ht : 0 ≤ t := hp.trans hpt
  have hbud : t + (t + k) ^ k ≤ (p + C) ^ C := by
    simpa [T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have hVC : (t + k) ^ k ≤ (p + C) ^ C := by linarith
  obtain ⟨choice, H, hHsub, hHn, hHsize, hHbias⟩ := B.exists_fixed_partners
    (fun i n => (Q i).evalCyclic N (fun _ => n))
    (fun i j n => (R i j).evalCyclic N (fun _ => n)) ea eb c b ha hb hqp hc hbcoeff hJ
    (fun i n => ((Q i).norm_evalCyclic_le N _).trans (hQcap i)) herror hcount
  have hK : (Fintype.card (Fin B.count) : ℝ) ≤ t := by
    rw [Fintype.card_fin]
    exact (Nat.cast_le.mpr B.count_le_dim).trans (B.geometry.1.trans (hqp.trans hpt))
  obtain ⟨freq, freq', V, W, S, hsub, hSn, hsize, hV, hW, hheightV, hheightW, hvertV, hvertW, hbias⟩ :=
    hvertical (fun j => D (choice j).1) (fun j => E (choice j).1 (choice j).2)
      (fun j => Q (choice j).1) (fun j => R (choice j).1 (choice j).2) ht hK
      (fun j => (hQc (choice j).1).mono hpt) (fun j => (hRc (choice j).1 (choice j).2).mono hpt)
      (fun j => hQcap (choice j).1) (fun j => hRcap (choice j).1 (choice j).2)
      N H hHn (fun h j n => (B.mode h j).evalCyclic N (fun _ => n))
      (fun h hh j n => ((B.mode h j).norm_evalCyclic_le N _).trans (B.mode_norm h (hHsub hh) j)) hHbias
  refine ⟨choice, freq, freq', V, W, S, hsub.trans hHsub, hSn, ?_, ?_, ?_, ?_, ?_, hvertV, hvertW, ?_⟩
  · calc
      _ ≤ Real.exp (-(t + (t + k) ^ k)) * N :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hbud)) (Nat.cast_nonneg N)
      _ = Real.exp (-((t + k) ^ k)) * (Real.exp (-t) * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-((t + k) ^ k)) * H.card :=
        mul_le_mul_of_nonneg_left hHsize (Real.exp_pos _).le
      _ ≤ S.card := hsize
  · exact fun j => ⟨(hV j).1.mono hVC, (hV j).2⟩
  · exact fun j => ⟨(hW j).1.mono hVC, (hW j).2⟩
  · exact fun j i => (hheightV j i).trans hVC
  · exact fun j i => (hheightW j i).trans hVC
  · exact fun h hh j => (Real.exp_le_exp.mpr (neg_le_neg hVC)).trans (hbias h hh j)

end Erdos3.PositiveShiftBasis

end

end OAI
