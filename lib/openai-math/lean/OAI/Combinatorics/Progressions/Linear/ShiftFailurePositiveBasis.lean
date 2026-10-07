/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.CommonPositivePartitionRefinement
import OAI.Combinatorics.Progressions.Estimates.ControlledAdaptedRebase
import OAI.Combinatorics.Progressions.Nilpotent.CommonVariableDimensionNiltests

namespace OAI

section

namespace Erdos3

theorem positive_basis_error_bound (p v : ℝ) :
    2 * Real.exp p * Real.exp (-(2 * p + 8)) +
      Real.exp v * Real.exp (-(v + p + 8)) ≤ Real.exp (-p) / 2 := by
  have hfirst : Real.exp p * Real.exp (-(2 * p + 8)) = Real.exp (-p) * Real.exp (-8) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hsecond : Real.exp v * Real.exp (-(v + p + 8)) = Real.exp (-p) * Real.exp (-8) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h6 : 6 * Real.exp (-8) ≤ 1 := by
    calc
      6 * Real.exp (-8) ≤ Real.exp 8 * Real.exp (-8) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (8 : ℝ)]) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; norm_num
  rw [mul_assoc (2 : ℝ), hfirst, hsecond]
  have hmul := mul_le_mul_of_nonneg_left h6 (Real.exp_pos (-p)).le
  nlinarith

theorem exists_positive_basis_precision :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → ∃ q rho tau : ℝ,
      p ≤ q ∧ q ≤ (p + C) ^ C ∧ verticalDecompositionBudget q ≤ (p + C) ^ C ∧
      0 < rho ∧ rho⁻¹ ≤ Real.exp q ∧ 0 < tau ∧ Real.exp (-((p + C) ^ C)) ≤ tau ∧
      2 * Real.exp p * rho + Real.exp (verticalDecompositionBudget q) * tau ≤ Real.exp (-p) / 2 := by
  obtain ⟨c, _, hvertical⟩ := exists_verticalDecompositionBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  let Q := 2 * X + 8
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + Polynomial.C c) ^ c + X + 8)
  refine ⟨C, hC, ?_⟩
  intro p hp
  let q := 2 * p + 8
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hq0 : 0 ≤ q := hp.trans hpq
  have hv0 := verticalDecompositionBudget_nonneg hq0
  have hb : q + (q + c) ^ c + p + 8 ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hv := hvertical q hq0
  have hpow : 0 ≤ (q + c) ^ c := by positivity
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hvC : verticalDecompositionBudget q + p + 8 ≤ (p + C) ^ C := by linarith
  refine ⟨q, Real.exp (-q), Real.exp (-(verticalDecompositionBudget q + p + 8)),
    hpq, hqC, by linarith, Real.exp_pos _, ?_, Real.exp_pos _, ?_, ?_⟩
  · rw [Real.exp_neg, inv_inv]
  · exact Real.exp_le_exp.mpr (neg_le_neg hvC)
  · exact positive_basis_error_bound p (verticalDecompositionBudget q)

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module CircleFourier
open scoped TensorProduct BigOperators

theorem exists_quantitative_positive_basis :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {D : RationalFilteredNilmanifold L s d} (T : D.Niltest (fun _ : Unit => 1))
      {p : ℝ}, 0 ≤ p → T.UnitIntervalValued → T.ComplexityLE p → T.normBound ≤ 1 →
      ∀ {N : ℕ} [NeZero N] (weight : ZMod N → ℂ), (∀ x, ‖weight x‖ ≤ Real.exp p) →
      ∃ (m : ℕ) (eta : Fin m → L →ₗ[ℚ] ℚ) (U : Fin m → D.Niltest (fun _ : Unit => 1))
        (S : D.Niltest (fun _ : Unit => 1)),
        m ≤ d ∧
        (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ (p + C) ^ C) ∧
        (∀ j, (U j).ComplexityLE ((p + C) ^ C) ∧ (U j).orbit = T.orbit ∧ (U j).normBound ≤ 1) ∧
        (∀ j z, z ∈ D.filtration.realification.subgroup s → ∀ x,
          (U j).observable (z • x) =
            character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x) ∧
        (∀ j, Real.exp (-((p + C) ^ C)) < ‖𝔼 n, weight n * (U j).evalCyclic N (fun _ => n)‖) ∧
        LinearIndependent ℚ (fun j => (eta j).comp (D.filtration.layer s).subtype) ∧
        S.UnitIntervalValued ∧ S.ComplexityLE ((p + C) ^ C) ∧ S.orbit = T.orbit ∧
        (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s →
          (∀ j, realifyFunctional (eta j) z.coord = 0) → ∀ x, S.observable (z • x) = S.observable x) ∧
        ‖(𝔼 n, weight n * T.evalCyclic N (fun _ => n)) -
          (𝔼 n, weight n * S.evalCyclic N (fun _ => n))‖ ≤ Real.exp (-p) / 2 := by
  obtain ⟨C, hC, hprecision⟩ := exists_positive_basis_precision
  refine ⟨C, hC, ?_⟩
  intro L _ _ s d _ _ _ _ D T p hp hT hTc hcap N _ weight hweight
  obtain ⟨q, rho, tau, hpq, hqC, hvC, hrho, hrhoq, htau, htauC, hsmall⟩ := hprecision p hp
  obtain ⟨J, inst, hresult⟩ := T.exists_bounded_positive_fourier_basis (hp.trans hpq)
    hT (hTc.mono hpq) hcap hrho hrhoq htau.le (Real.exp_pos p).le weight hweight
  let := inst
  obtain ⟨eta, U, S, m, indices, _, hheight, hU, hvert, hmd, hcorr, hlin, hS, hSc, hSo, hinv, herr⟩ := hresult
  exact ⟨m, (fun j => eta (indices j)), (fun j => U (indices j)), S, hmd,
    (fun j i => (hheight (indices j) i).trans hvC),
    (fun j => ⟨(hU (indices j)).1.mono hqC, (hU (indices j)).2⟩),
    (fun j => hvert (indices j)), (fun j => htauC.trans_lt (hcorr j)), hlin,
    hS, hSc.mono hqC, hSo, hinv, herr.trans hsmall⟩

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

theorem positive_violation_of_norm_sub_le {a b : ℂ} {delta error : ℝ}
    (hviolation : delta < a.re) (herror : ‖a - b‖ ≤ error) (hsmall : error ≤ delta / 2) :
    delta / 2 < b.re := by
  have h := Complex.re_le_norm (a - b)
  rw [Complex.sub_re] at h
  linarith

namespace RationalFilteredNilmanifold

open Module CircleFourier
open scoped TensorProduct BigOperators

theorem exists_common_positive_basis :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (H : Finset G), H.Nonempty →
      ∀ (T : G → D.Niltest (fun _ : Unit => 1)) {p delta : ℝ}, 0 ≤ p →
      Real.exp (-p) ≤ delta →
      (∀ h ∈ H, (T h).UnitIntervalValued) →
      (∀ h ∈ H, (T h).ComplexityLE p) → (∀ h ∈ H, (T h).normBound ≤ 1) →
      ∀ {N : ℕ} [NeZero N] (weight : G → ZMod N → ℂ),
      (∀ h ∈ H, ∀ n, ‖weight h n‖ ≤ Real.exp p) →
      (∀ h ∈ H, delta < (𝔼 n, weight h n * (T h).evalCyclic N (fun _ => n)).re) →
      ∃ (m : ℕ) (H' : Finset G) (eta : G → Fin m → L →ₗ[ℚ] ℚ)
        (U : G → Fin m → D.Niltest (fun _ : Unit => 1)) (S : G → D.Niltest (fun _ : Unit => 1)),
        m ≤ d ∧ H' ⊆ H ∧ H'.Nonempty ∧ Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
        ∀ h ∈ H',
          (∀ j i, rationalLogHeight (eta h j (D.basis i)) ≤ (p + C) ^ C) ∧
          (∀ j, (U h j).ComplexityLE ((p + C) ^ C) ∧ (U h j).orbit = (S h).orbit ∧ (U h j).normBound ≤ 1) ∧
          (∀ j z, z ∈ D.filtration.realification.subgroup s → ∀ x,
            (U h j).observable (z • x) = character
              ((realifyFunctional (eta h j) z.coord : ℝ) : CircleFourier.Circle) * (U h j).observable x) ∧
          (∀ j, Real.exp (-((p + C) ^ C)) < ‖𝔼 n, weight h n * (U h j).evalCyclic N (fun _ => n)‖) ∧
          LinearIndependent ℚ (fun j => (eta h j).comp (D.filtration.layer s).subtype) ∧
          (S h).UnitIntervalValued ∧ (S h).ComplexityLE ((p + C) ^ C) ∧ (S h).orbit = (T h).orbit ∧
          (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s →
            (∀ j, realifyFunctional (eta h j) z.coord = 0) → ∀ x,
              (S h).observable (z • x) = (S h).observable x) ∧
          delta / 2 < (𝔼 n, weight h n * (S h).evalCyclic N (fun _ => n)).re := by
  classical
  obtain ⟨c, _, hbasis⟩ := Niltest.exists_quantitative_positive_basis
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + (X + Polynomial.C c) ^ c + 1)
  refine ⟨C, hC, ?_⟩
  intro G L _ _ s d _ _ _ _ D H hH T p delta hp hdelta hT hTc hcap N _ weight hweight hviolation
  obtain ⟨hbase, hhbase⟩ := hH
  let pick (h : G) := if h ∈ H then h else hbase
  have hpick (h : G) : pick h ∈ H := by
    dsimp only [pick]
    split_ifs with hh
    · exact hh
    · exact hhbase
  have hchoices (h : G) := hbasis (T (pick h)) hp (hT _ (hpick h)) (hTc _ (hpick h))
    (hcap _ (hpick h)) (weight (pick h)) (hweight _ (hpick h))
  choose m eta U S hm hheight hU hvert hcorr hlin hS hSc hSo hinv herr using hchoices
  have hd : (d : ℝ) ≤ p := (hTc hbase hhbase).1.1
  have hpexp : p ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  obtain ⟨a, _, H', hsub, ha, hsame, hlarge⟩ :=
    exists_common_bounded_moduli H ⟨hbase, hhbase⟩ (fun h (_ : Unit) => m h) hp
      (fun h _ _ => ((Nat.cast_le.mpr (hm h)).trans hd).trans hpexp)
  let index (h : G) (hh : h ∈ H') : Fin (m a) ≃ Fin (m h) :=
    (finCongr (congrFun (hsame h hh) ())).symm
  let eta' (h : G) (j : Fin (m a)) : L →ₗ[ℚ] ℚ :=
    if hh : h ∈ H' then eta h (index h hh j) else 0
  let U' (h : G) (j : Fin (m a)) : D.Niltest (fun _ : Unit => 1) :=
    if hh : h ∈ H' then U h (index h hh j) else Niltest.const D (fun _ => 1) 0
  have hbud : p + (p + c) ^ c + 1 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hcC : (p + c) ^ c ≤ (p + C) ^ C := by linarith
  have hpC : p + 1 ≤ (p + C) ^ C := by
    have hn : 0 ≤ (p + c) ^ c := by positivity
    linarith
  have hlarge' : Real.exp (-(p + 1)) * H.card ≤ (H'.card : ℝ) := by
    simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hlarge
  refine ⟨m a, H', eta', U', S, hm a, hsub, ⟨a, ha⟩,
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpC))
      (Nat.cast_nonneg _)).trans hlarge', ?_⟩
  intro h hh
  have hpickh : pick h = h := ite_eq_left (hsub hh)
  simp only [eta', U', dite_eq_left hh]
  refine ⟨(fun j i => (hheight h (index h hh j) i).trans hcC), ?_,
    (fun j => hvert h (index h hh j)), ?_, ?_, hS h, (hSc h).mono hcC, ?_, ?_, ?_⟩
  · intro j
    exact ⟨(hU h (index h hh j)).1.mono hcC,
      (hU h (index h hh j)).2.1.trans (hSo h).symm, (hU h (index h hh j)).2.2⟩
  · intro j
    have ht := (Real.exp_le_exp.mpr (neg_le_neg hcC)).trans_lt (hcorr h (index h hh j))
    simpa only [hpickh] using ht
  · exact (hlin h).comp (index h hh) (index h hh).injective
  · simpa only [hpickh] using hSo h
  · intro z hz hzero x
    apply hinv h z hz _ x
    intro i
    obtain ⟨j, rfl⟩ := (index h hh).surjective i
    exact hzero j
  · have he : ‖(𝔼 n, weight h n * (T h).evalCyclic N (fun _ => n)) -
        (𝔼 n, weight h n * (S h).evalCyclic N (fun _ => n))‖ ≤ Real.exp (-p) / 2 := by
      simpa only [hpickh] using herr h
    exact positive_violation_of_norm_sub_le (hviolation h (hsub hh)) he (by linarith)

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module CircleFourier
open scoped TensorProduct BigOperators

theorem exists_common_model_positive_basis (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G : Type*} {L : G → Type*}
      [∀ h, LieRing (L h)] [∀ h, LieAlgebra ℚ (L h)]
      [∀ h, TopologicalSpace (ℝ ⊗[ℚ] L h)] [∀ h, IsTopologicalAddGroup (ℝ ⊗[ℚ] L h)]
      [∀ h, ContinuousSMul ℝ (ℝ ⊗[ℚ] L h)] [∀ h, T2Space (ℝ ⊗[ℚ] L h)] {d : G → ℕ}
      (D : ∀ h, RationalFilteredNilmanifold (L h) s (d h))
      (T : ∀ h, (D h).Niltest (fun _ : Unit => 1)) (H : Finset G), H.Nonempty →
      ∀ {p delta : ℝ}, 0 ≤ p → Real.exp (-p) ≤ delta → (∀ h, (T h).ComplexityLE p) →
      (∀ h ∈ H, (T h).UnitIntervalValued) →
      ∀ {N : ℕ} [NeZero N] (weight : G → ZMod N → ℂ),
      (∀ h ∈ H, ∀ n, ‖weight h n‖ ≤ Real.exp p) →
      (∀ h ∈ H, delta < (𝔼 n, weight h n * (T h).evalCyclic N (fun _ => n)).re) →
      ∃ h₀ ∈ H, ∃ E : RationalFilteredNilmanifold (L h₀) s (d h₀),
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ (m : ℕ) (H' : Finset G) (eta : G → Fin m → L h₀ →ₗ[ℚ] ℚ)
          (U : G → Fin m → E.Niltest (fun _ : Unit => 1)) (S : G → E.Niltest (fun _ : Unit => 1)),
          m ≤ d h₀ ∧ H' ⊆ H ∧ H'.Nonempty ∧ Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
          ∀ h ∈ H',
            (∀ j i, rationalLogHeight (eta h j (E.basis i)) ≤ (p + C) ^ C) ∧
            (∀ j, (U h j).ComplexityLE ((p + C) ^ C) ∧ (U h j).orbit = (S h).orbit ∧ (U h j).normBound ≤ 1) ∧
            (∀ j z, z ∈ E.filtration.realification.subgroup s → ∀ x,
              (U h j).observable (z • x) = character
                ((realifyFunctional (eta h j) z.coord : ℝ) : CircleFourier.Circle) * (U h j).observable x) ∧
            (∀ j, Real.exp (-((p + C) ^ C)) < ‖𝔼 n, weight h n * (U h j).evalCyclic N (fun _ => n)‖) ∧
            LinearIndependent ℚ (fun j => (eta h j).comp (E.filtration.layer s).subtype) ∧
            (S h).UnitIntervalValued ∧ (S h).ComplexityLE ((p + C) ^ C) ∧
            (∀ z : E.RealGroup, z ∈ E.filtration.realification.subgroup s →
              (∀ j, realifyFunctional (eta h j) z.coord = 0) → ∀ x,
                (S h).observable (z • x) = (S h).observable x) ∧
            delta / 2 < (𝔼 n, weight h n * (S h).evalCyclic N (fun _ => n)).re := by
  classical
  obtain ⟨c, _, hmodels⟩ := exists_common_variable_dimension_niltest_model s
  obtain ⟨k, _, hbases⟩ := exists_common_positive_basis
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + 1 + (X + 1 + Polynomial.C c) ^ c + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + Polynomial.C k) ^ k)
  refine ⟨C, hC, ?_⟩
  intro G L _ _ _ _ _ _ d D T H hH p delta hp hdelta hTc hT N _ weight hweight hviolation
  let T₀ : ∀ h, (D h).Niltest (fun _ : Unit => 1) := fun h =>
    if hh : h ∈ H then (T h).withUnitBound (hT h hh).norm_le_one else T h
  have hTc₀ (h) : (T₀ h).ComplexityLE (p + 1) := by
    by_cases hh : h ∈ H
    · simpa only [T₀, dite_eq_left hh] using
        (T h).withUnitBound_complexity (hT h hh).norm_le_one (hTc h)
    · simpa only [T₀, dite_eq_right hh] using (hTc h).mono (by linarith : p ≤ p + 1)
  have hT₀ (h) (hh : h ∈ H) : (T₀ h).UnitIntervalValued := by
    simp only [T₀, dite_eq_left hh]
    exact hT h hh
  have hcap₀ (h) (hh : h ∈ H) : (T₀ h).normBound ≤ 1 := by
    simp only [T₀, dite_eq_left hh]
    exact le_rfl
  have hvalue₀ (h) (hh : h ∈ H) (x : Unit → ℤ) : (T₀ h).eval x = (T h).eval x := by
    simp only [T₀, dite_eq_left hh, Niltest.withUnitBound_eval]
  let q := p + 1 + (p + 1 + c) ^ c + 2
  have hpow : 0 ≤ (p + 1 + c) ^ c := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hmodelq : (p + 1 + c) ^ c ≤ q := by dsimp [q]; linarith
  have hq0 : 0 ≤ q := hp.trans hpq
  have hbud : q + (q + k) ^ k ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by
    have hh : 0 ≤ (q + k) ^ k := by positivity
    linarith
  have hbaseC : (q + k) ^ k ≤ (p + C) ^ C := by linarith
  have hloss : (p + 1 + c) ^ c + (q + k) ^ k ≤ (p + C) ^ C := by linarith
  obtain ⟨h₀, hh₀, E, hE, H₁, P, hsub₁, hh₀', hlarge₁, hP⟩ :=
    hmodels D T₀ H hH (by linarith : 0 ≤ p + 1) hTc₀
  have hPc (h) (hh : h ∈ H₁) : (P h).ComplexityLE q := (hP h hh).1.mono hmodelq
  have hPunit (h) (hh : h ∈ H₁) : (P h).UnitIntervalValued := (hP h hh).2.2.2 (hT₀ h (hsub₁ hh))
  have hPcap (h) (hh : h ∈ H₁) : (P h).normBound ≤ 1 := by
    rw [(hP h hh).2.1]
    exact hcap₀ h (hsub₁ hh)
  have hPvalue (h) (hh : h ∈ H₁) (n : ZMod N) :
      (P h).evalCyclic N (fun _ => n) = (T h).evalCyclic N (fun _ => n) :=
    ((hP h hh).2.2.1 _).trans (hvalue₀ h (hsub₁ hh) _)
  have hPviolation (h) (hh : h ∈ H₁) :
      delta < (𝔼 n, weight h n * (P h).evalCyclic N (fun _ => n)).re := by
    simpa only [hPvalue h hh] using hviolation h (hsub₁ hh)
  obtain ⟨m, H₂, eta, U, S, hm, hsub₂, hnonempty, hlarge₂, hbasis⟩ :=
    hbases E H₁ ⟨h₀, hh₀'⟩ P hq0
      ((Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hdelta) hPunit hPc hPcap weight
      (fun h hh n => (hweight h (hsub₁ hh) n).trans (Real.exp_le_exp.mpr hpq)) hPviolation
  refine ⟨h₀, hh₀, E, hE.mono E (hmodelq.trans hqC), m, H₂, eta, U, S, hm,
    hsub₂.trans hsub₁, hnonempty, ?_, ?_⟩
  · calc
      Real.exp (-((p + C) ^ C)) * H.card ≤
          Real.exp (-((p + 1 + c) ^ c + (q + k) ^ k)) * H.card :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hloss)) (Nat.cast_nonneg _)
      _ = Real.exp (-((q + k) ^ k)) * (Real.exp (-((p + 1 + c) ^ c)) * H.card) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-((q + k) ^ k)) * H₁.card :=
        mul_le_mul_of_nonneg_left hlarge₁ (Real.exp_pos _).le
      _ ≤ H₂.card := hlarge₂
  · intro h hh
    obtain ⟨hheight, hU, hvert, hcorr, hlin, hS, hSc, _, hinv, hv⟩ := hbasis h hh
    exact ⟨(fun j i => (hheight j i).trans hbaseC),
      (fun j => ⟨(hU j).1.mono hbaseC, (hU j).2⟩), hvert,
      (fun j => (Real.exp_le_exp.mpr (neg_le_neg hbaseC)).trans_lt (hcorr j)),
      hlin, hS, hSc.mono hbaseC, hinv, hv⟩

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct BigOperators

structure PositiveShiftBasis (degree N : ℕ) [NeZero N] (p : ℝ)
    (a J : ZMod N → ℝ) where
  L : Type u
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  geometry : model.GeometryComplexityLE p
  count : ℕ
  count_le_dim : count ≤ dim
  shifts : Finset (ZMod N)
  shifts_nonempty : shifts.Nonempty
  shifts_large : Real.exp (-p) * N ≤ (shifts.card : ℝ)
  frequency : ZMod N → Fin count → L →ₗ[ℚ] ℚ
  mode : ZMod N → Fin count → model.Niltest (fun _ : Unit => 1)
  test : ZMod N → model.Niltest (fun _ : Unit => 1)
  frequency_height : ∀ h ∈ shifts, ∀ j i, rationalLogHeight (frequency h j (model.basis i)) ≤ p
  mode_complexity : ∀ h ∈ shifts, ∀ j, (mode h j).ComplexityLE p
  mode_orbit : ∀ h ∈ shifts, ∀ j, (mode h j).orbit = (test h).orbit
  mode_norm : ∀ h ∈ shifts, ∀ j, (mode h j).normBound ≤ 1
  mode_vertical : ∀ h ∈ shifts, ∀ j z, z ∈ model.filtration.realification.subgroup degree → ∀ x,
    (mode h j).observable (z • x) = character
      ((realifyFunctional (frequency h j) z.coord : ℝ) : CircleFourier.Circle) * (mode h j).observable x
  mode_bias : ∀ h ∈ shifts, ∀ j, Real.exp (-p) <
    ‖𝔼 n, (mode h j).evalCyclic N (fun _ => n) * (a n : ℂ) * (J (n + h) : ℂ)‖
  independent : ∀ h ∈ shifts,
    LinearIndependent ℚ (fun j => (frequency h j).comp (model.filtration.layer degree).subtype)
  test_positive : ∀ h ∈ shifts, (test h).UnitIntervalValued
  test_complexity : ∀ h ∈ shifts, (test h).ComplexityLE p
  test_invariant : ∀ h ∈ shifts, ∀ z : model.RealGroup,
    z ∈ model.filtration.realification.subgroup degree →
    (∀ j, realifyFunctional (frequency h j) z.coord = 0) → ∀ x,
      (test h).observable (z • x) = (test h).observable x
  test_violation : ∀ h ∈ shifts, Real.exp (-p) <
    𝔼 n, a n * J (n + h) * ((test h).evalCyclic N (fun _ => n)).re

end Erdos3

end

section

universe u

namespace Erdos3.PositiveShiftBasis

open Module
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

theorem exists_adapted :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {s N : ℕ} [NeZero N] {p : ℝ} {a J : ZMod N → ℝ}
      (B : PositiveShiftBasis.{u} s N p a J),
      ∃ (B' : PositiveShiftBasis.{u} s N ((p + C) ^ C) a J) (hcount : B'.count = B.count),
        (∃ weight : Fin B'.dim → ℕ, ∀ i, B'.model.filtration.layer i =
          Submodule.span ℚ (B'.model.basis '' {j | i ≤ weight j})) ∧
        B'.shifts = B.shifts ∧
        (∀ h j x, (B'.mode h j).eval x = (B.mode h (Fin.cast hcount j)).eval x) ∧
        ∀ h x, (B'.test h).eval x = (B.test h).eval x := by
  obtain ⟨C, hC, hrebase⟩ := RationalFilteredNilmanifold.exists_controlled_adapted_rebase
  refine ⟨C, hC, ?_⟩
  intro s N _ p a J B
  have hp : 0 ≤ p := (Nat.cast_nonneg B.dim).trans B.geometry.1
  obtain ⟨F, H, hH, hbase, hF, hcomp, hfreq⟩ := hrebase B.model hp B.geometry
  have hdim : finrank ℚ B.L = B.dim := by
    simpa only [Fintype.card_fin] using finrank_eq_card_basis B.model.basis
  let B' : PositiveShiftBasis s N ((p + C) ^ C) a J := {
    L := B.L
    lie := B.lie
    algebra := B.algebra
    dim := finrank ℚ B.L
    topology := B.topology
    topologicalAdd := B.topologicalAdd
    continuousSMul := B.continuousSMul
    hausdorff := B.hausdorff
    model := F.model
    geometry := hF
    count := B.count
    count_le_dim := by rw [hdim]; exact B.count_le_dim
    shifts := B.shifts
    shifts_nonempty := B.shifts_nonempty
    shifts_large := (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (neg_le_neg hbase)) (Nat.cast_nonneg N)).trans B.shifts_large
    frequency := B.frequency
    mode := fun h j => F.rebaseNiltest H hH (B.mode h j)
    test := fun h => F.rebaseNiltest H hH (B.test h)
    frequency_height := fun h hh j => hfreq (B.frequency h j) (B.frequency_height h hh j)
    mode_complexity := fun h hh j => hcomp (B.mode h j) (B.mode_complexity h hh j)
    mode_orbit := fun h hh j => B.mode_orbit h hh j
    mode_norm := fun h hh j => B.mode_norm h hh j
    mode_vertical := fun h hh j => B.mode_vertical h hh j
    mode_bias := fun h hh j => (Real.exp_le_exp.mpr (neg_le_neg hbase)).trans_lt (B.mode_bias h hh j)
    independent := fun h hh => B.independent h hh
    test_positive := fun h hh => B.test_positive h hh
    test_complexity := fun h hh => hcomp (B.test h) (B.test_complexity h hh)
    test_invariant := fun h hh => B.test_invariant h hh
    test_violation := fun h hh => (Real.exp_le_exp.mpr (neg_le_neg hbase)).trans_lt (B.test_violation h hh) }
  exact ⟨B', rfl, ⟨F.weight, F.model_layers⟩, rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

def mono {s N : ℕ} [NeZero N] {p q : ℝ} {a J : ZMod N → ℝ}
    (B : PositiveShiftBasis s N p a J) (hpq : p ≤ q) : PositiveShiftBasis s N q a J where
  L := B.L
  lie := B.lie
  algebra := B.algebra
  dim := B.dim
  topology := B.topology
  topologicalAdd := B.topologicalAdd
  continuousSMul := B.continuousSMul
  hausdorff := B.hausdorff
  model := B.model
  geometry := B.geometry.mono B.model hpq
  count := B.count
  count_le_dim := B.count_le_dim
  shifts := B.shifts
  shifts_nonempty := B.shifts_nonempty
  shifts_large := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq))
    (Nat.cast_nonneg N)).trans B.shifts_large
  frequency := B.frequency
  mode := B.mode
  test := B.test
  frequency_height := fun h hh j i => (B.frequency_height h hh j i).trans hpq
  mode_complexity := fun h hh j => (B.mode_complexity h hh j).mono hpq
  mode_orbit := B.mode_orbit
  mode_norm := B.mode_norm
  mode_vertical := B.mode_vertical
  mode_bias := fun h hh j => (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans_lt (B.mode_bias h hh j)
  independent := B.independent
  test_positive := B.test_positive
  test_complexity := fun h hh => (B.test_complexity h hh).mono hpq
  test_invariant := B.test_invariant
  test_violation := fun h hh => (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans_lt (B.test_violation h hh)

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open scoped BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

variable {s N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}

noncomputable def testingFamily (B : PositiveShiftBasis s N q a J) :
    ZMod N × Fin B.count → ZMod N → ℂ := by
  classical
  exact fun hk n => if hk.1 ∈ B.shifts then (B.mode hk.1 hk.2).evalCyclic N (fun _ => n) else 0

theorem testingFamily_of_mem (B : PositiveShiftBasis s N q a J) {h : ZMod N}
    (hh : h ∈ B.shifts) (j : Fin B.count) (n : ZMod N) :
    B.testingFamily (h, j) n = (B.mode h j).evalCyclic N (fun _ => n) := by
  simp only [testingFamily, ite_eq_left hh]

theorem testingFamily_norm_le (B : PositiveShiftBasis s N q a J)
    (hk : ZMod N × Fin B.count) (n : ZMod N) : ‖B.testingFamily hk n‖ ≤ 1 := by
  classical
  by_cases hh : hk.1 ∈ B.shifts
  · rw [testingFamily, ite_eq_left hh]
    exact ((B.mode hk.1 hk.2).norm_evalCyclic_le N _).trans (B.mode_norm hk.1 hh hk.2)
  · simp only [testingFamily, ite_eq_right hh, norm_zero, zero_le_one]

theorem exists_fixed_partners (B : PositiveShiftBasis s N q a J)
    {I : Type*} {K : I → Type*} [Fintype I] [∀ i, Fintype (K i)]
    (Q : I → ZMod N → ℂ) (R : ∀ i, K i → ZMod N → ℂ)
    (ea : ZMod N → ℂ) (eb : I → ZMod N → ℂ) (c : I → ℂ) (d : ∀ i, K i → ℂ)
    (ha : ∀ n, (a n : ℂ) = (∑ i, c i * Q i n) + ea n)
    (hb : ∀ i n, (J n : ℂ) = (∑ j, d i j * R i j n) + eb i n)
    {p M : ℝ} (hqp : q ≤ p)
    (hc : (∑ i, ‖c i‖) ≤ Real.exp p) (hd : ∀ i, (∑ j, ‖d i j‖) ≤ Real.exp p)
    (hJ : ∀ n, |J n| ≤ M) (hQ : ∀ i n, ‖Q i n‖ ≤ 1)
    (herror : shiftTestingSeminorm (fun n => (J n : ℂ)) B.testingFamily ea +
      ∑ i, ‖c i‖ * shiftTestingSeminorm (Q i) (translatedTestFamily B.testingFamily) (eb i) ≤
        Real.exp (-(2 * q + 2)))
    (hcount : (Fintype.card (Sigma K) : ℝ) ≤ Real.exp p) :
    ∃ (choice : Fin B.count → Sigma K) (S : Finset (ZMod N)), S ⊆ B.shifts ∧ S.Nonempty ∧
      Real.exp (-((p + 2) ^ 2)) * N ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ j, Real.exp (-((p + 2) ^ 2)) ≤
        ‖𝔼 n, (B.mode h j).evalCyclic N (fun _ => n) * Q (choice j).1 n *
          R (choice j).1 (choice j).2 (n + h)‖ := by
  have hq : 0 ≤ q := (Nat.cast_nonneg B.dim).trans B.geometry.1
  have hK : (Fintype.card (Fin B.count) : ℝ) ≤ p := by
    rw [Fintype.card_fin]
    exact (Nat.cast_le.mpr B.count_le_dim).trans (B.geometry.1.trans hqp)
  have hH : Real.exp (-q) * Fintype.card (ZMod N) ≤ (B.shifts.card : ℝ) := by
    simpa only [ZMod.card] using B.shifts_large
  have hbcap (n) : ‖(J n : ℂ)‖ ≤ M := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hJ n
  have hcorr (h) (hh : h ∈ B.shifts) (j : Fin B.count) :
      Real.exp (-q) ≤ ‖𝔼 n, B.testingFamily (h, j) n * (a n : ℂ) * (J (n + h) : ℂ)‖ := by
    simp only [testingFamily_of_mem B hh]
    exact (B.mode_bias h hh j).le
  obtain ⟨choice, S, hsub, hSn, hlarge, hbias⟩ := exists_fixed_partners_power B.shifts
    (fun n => (a n : ℂ)) (fun n => (J n : ℂ)) ea B.testingFamily (fun h j => (h, j))
    Q R eb c d ha hb (hq.trans hqp) hqp hK hc hd B.testingFamily_norm_le hbcap hQ herror hH hcorr hcount
  refine ⟨choice, S, hsub, hSn, ?_, ?_⟩
  · simpa only [ZMod.card] using hlarge
  · intro h hh j
    simpa only [testingFamily_of_mem B (hsub hh)] using hbias h hh j

end Erdos3.PositiveShiftBasis

end

section

universe u

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct BigOperators

theorem exists_positive_basis_of_shift_failure (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p epsilon : ℝ}, 0 ≤ p →
      0 ≤ epsilon → epsilon ≤ 1 → ∀ f g J : ZMod N → ℝ,
      (∀ n, 0 ≤ f n ∧ f n ≤ Real.exp p) →
      (∀ n, 0 ≤ g n ∧ g n ≤ Real.exp p) →
      (∀ n, 0 ≤ J n ∧ J n ≤ Real.exp p) →
      (¬ ∃ E : Finset (ZMod N), (E.card : ℝ) ≤ Real.exp (-p) * N ∧
        CyclicNiltestShiftBound.{u} s N p (Real.exp (-p))
          (fun n => f n - (1 + epsilon) * g n) J E) →
      Nonempty (PositiveShiftBasis.{u} s N ((p + C) ^ C)
        (fun n => f n - (1 + epsilon) * g n) J) := by
  classical
  obtain ⟨c, _, hmodels⟩ := RationalFilteredNilmanifold.exists_common_model_positive_basis s
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + 2) ^ 2 + 3 + 2 * X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C c) ^ c + X + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p epsilon hp hepsilon hepsilon1 f g J hf hg hJ hfailure
  let a := fun n => f n - (1 + epsilon) * g n
  obtain ⟨H, F, hH, hlarge, hF, hviolation⟩ :=
    exists_many_positive_cyclic_violations a J (Real.exp_pos (-p)).le hfailure
  let R := fun h => Classical.choice ((hF h).model_nonempty hp)
  let L := fun h => (R h).L
  let : ∀ h, LieRing (L h) := fun h => (R h).lie
  let : ∀ h, LieAlgebra ℚ (L h) := fun h => (R h).algebra
  let : ∀ h, TopologicalSpace (ℝ ⊗[ℚ] L h) := fun h => (R h).topology
  let : ∀ h, IsTopologicalAddGroup (ℝ ⊗[ℚ] L h) := fun h => (R h).topologicalAdd
  let : ∀ h, ContinuousSMul ℝ (ℝ ⊗[ℚ] L h) := fun h => (R h).continuousSMul
  let : ∀ h, T2Space (ℝ ⊗[ℚ] L h) := fun h => (R h).hausdorff
  let t := raisedNiltestBudget p + 2 * p + 2
  have hraised : 0 ≤ raisedNiltestBudget p := hp.trans (le_raisedNiltestBudget p)
  have hrt : raisedNiltestBudget p ≤ t := by dsimp [t]; linarith
  have hwt : 2 * p + 2 ≤ t := by dsimp [t]; linarith
  have hpt : p ≤ t := (le_raisedNiltestBudget p).trans hrt
  have ht : 0 ≤ t := hp.trans hpt
  have hbud : t + (t + c) ^ c + p + 2 ≤ (p + C) ^ C := by
    simpa [T, X, t, raisedNiltestBudget, Polynomial.eval₂_pow] using hbudget p hp
  have hcomp : (t + c) ^ c ≤ (p + C) ^ C := by linarith
  have hloss : p + (t + c) ^ c ≤ (p + C) ^ C := by linarith
  have hhalf : Real.exp (-((p + C) ^ C)) ≤ Real.exp (-p) / 2 := by
    have hpow : 0 ≤ (t + c) ^ c := by positivity
    exact (Real.exp_le_exp.mpr (by linarith : -((p + C) ^ C) ≤ -p - 1)).trans
      (exp_sub_one_le_half_exp (-p))
  let weight : ZMod N → ZMod N → ℂ := fun h n => ((a n * J (n + h) : ℝ) : ℂ)
  have hw (h n : ZMod N) : ‖weight h n‖ ≤ Real.exp t :=
    (shift_violation_weight_cap hepsilon hepsilon1 f g J hf hg hJ h n).trans
      (Real.exp_le_exp.mpr hwt)
  have hv (h) (hh : h ∈ H) : Real.exp (-p) <
      (𝔼 n, weight h n * (R h).test.evalCyclic N (fun _ => n)).re := by
    change Real.exp (-p) < (𝔼 n, ((a n * J (n + h) : ℝ) : ℂ) *
      (R h).test.evalCyclic N (fun _ => n)).re
    rw [real_shift_weighted_mean]
    simpa only [(R h).eval] using hviolation h hh
  obtain ⟨h₀, _, E, hE, m, H', eta, U, S, hm, _, hH', hlarge', hresult⟩ :=
    hmodels (fun h => (R h).model) (fun h => (R h).test) H hH ht
      (Real.exp_le_exp.mpr (neg_le_neg hpt))
      (fun h => (R h).complexity.mono hrt) (fun h _ => (R h).positive) weight
      (fun h _ n => hw h n) hv
  have hdensity : Real.exp (-((p + C) ^ C)) * N ≤ (H'.card : ℝ) := by
    calc
      _ ≤ Real.exp (-(p + (t + c) ^ c)) * N :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hloss)) (Nat.cast_nonneg N)
      _ = Real.exp (-((t + c) ^ c)) * (Real.exp (-p) * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-((t + c) ^ c)) * H.card :=
        mul_le_mul_of_nonneg_left hlarge.le (Real.exp_pos _).le
      _ ≤ H'.card := hlarge'
  refine ⟨{
    L := L h₀
    lie := inferInstance
    algebra := inferInstance
    dim := (R h₀).dim
    topology := inferInstance
    topologicalAdd := inferInstance
    continuousSMul := inferInstance
    hausdorff := inferInstance
    model := E
    geometry := hE.mono E hcomp
    count := m
    count_le_dim := hm
    shifts := H'
    shifts_nonempty := hH'
    shifts_large := hdensity
    frequency := eta
    mode := U
    test := S
    frequency_height := ?_
    mode_complexity := ?_
    mode_orbit := ?_
    mode_norm := ?_
    mode_vertical := ?_
    mode_bias := ?_
    independent := ?_
    test_positive := ?_
    test_complexity := ?_
    test_invariant := ?_
    test_violation := ?_ }⟩
  · exact fun h hh j i => ((hresult h hh).1 j i).trans hcomp
  · exact fun h hh j => ((hresult h hh).2.1 j).1.mono hcomp
  · exact fun h hh j => ((hresult h hh).2.1 j).2.1
  · exact fun h hh j => ((hresult h hh).2.1 j).2.2
  · exact fun h hh => (hresult h hh).2.2.1
  · intro h hh j
    have hc := (Real.exp_le_exp.mpr (neg_le_neg hcomp)).trans_lt ((hresult h hh).2.2.2.1 j)
    have he : (𝔼 n, weight h n * (U h j).evalCyclic N (fun _ => n)) =
        𝔼 n, (U h j).evalCyclic N (fun _ => n) * (a n : ℂ) * (J (n + h) : ℂ) := by
      apply Finset.expect_congr rfl
      intro n _
      dsimp only [weight]
      rw [Complex.ofReal_mul]
      ring
    simpa only [he] using hc
  · exact fun h hh => (hresult h hh).2.2.2.2.1
  · exact fun h hh => (hresult h hh).2.2.2.2.2.1
  · exact fun h hh => (hresult h hh).2.2.2.2.2.2.1.mono hcomp
  · exact fun h hh => (hresult h hh).2.2.2.2.2.2.2.1
  · intro h hh
    have hv' := hhalf.trans_lt (hresult h hh).2.2.2.2.2.2.2.2
    simpa only [weight, real_shift_weighted_mean] using hv'

end Erdos3

end

end OAI
