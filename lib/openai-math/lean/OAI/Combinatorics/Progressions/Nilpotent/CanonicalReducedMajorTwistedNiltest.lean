import OAI.Combinatorics.Progressions.Dynamics.ReducedTwistedTranslationBudget

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module
open scoped NNReal TensorProduct

variable {U : Type*} {m : ℕ}

theorem majorZeroParameterSlice_eq (D : MvPolynomial (U ⊕ Fin m) ℝ) :
    specializeMajorParameters (RingHom.id ℝ) D 0 =
      aeval (Sum.elim (fun _ : U => (0 : MvPolynomial (Fin m) ℝ)) X) D := by
  simp only [specializeMajorParameters, RingHom.comp_id, Pi.zero_apply, map_zero]
  rfl

theorem majorZeroParameterSlice_mass (D : MvPolynomial (U ⊕ Fin m) ℝ) :
    realPolynomialMass (specializeMajorParameters (RingHom.id ℝ) D 0) ≤
      realPolynomialMass D := by
  rw [majorZeroParameterSlice_eq]
  exact realPolynomialMass_zeroParameterEval_le D

theorem majorZeroParameterSlice_degree (w : Fin m → ℕ) (hw : ∀ i, 0 < w i)
    {d : ℕ} {D : MvPolynomial (U ⊕ Fin m) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d) :
    (specializeMajorParameters (RingHom.id ℝ) D 0).totalDegree ≤ d := by
  rw [majorZeroParameterSlice_eq]
  apply totalDegree_le_of_positive_weightedSupport w hw
  apply weightedSupportLE_aeval _ _ _ _ hD
  intro i
  cases i with
  | inl i => exact Submodule.zero_mem _
  | inr i => exact weightedSupportLE_X w i

variable (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]
    [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

theorem exists_majorTranslation_buffered_niltest (hd : 0 < d)
    (Ψ : PatchKernel m) (D : MvPolynomial (U ⊕ Fin m) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (M : ℝ≥0) (hM : realPolynomialMass D ≤ M) :
    ∃ F : (weightedTranslationNilmanifold w d hw hwd).Niltest (fun _ : U => 1),
      F.normBound = 1 ∧ F.lipBound = 2 * bufferedTranslationTermLip w d Ψ M ∧
      F.orbit = majorTranslationPolynomialOrbit w d hw hwd D hD A hA ∧
      (∀ u : U → ℝ, ∀ β : Fin m → ℤ,
        (∀ i, |eval u (A i) - (β i : ℝ)| ≤ 1 / 2) →
        F.evalReal u = (Ψ.value (fun i => eval u (A i) - (β i : ℝ)) : ℂ) *
          (Real.fourierChar (eval (Sum.elim u (fun i => (β i : ℝ))) D) : ℂ)) ∧
      (∀ u : U → ℝ, ‖F.evalReal u‖ ≤ 1) := by
  let q := majorTranslationPolynomialOrbit w d hw hwd D hD A hA
  have hq := majorTranslationPolynomialOrbit_realEval w d hw hwd D hD A hA
  let D₀ := specializeMajorParameters (RingHom.id ℝ) D 0
  have hdegree : D₀.totalDegree ≤ d := majorZeroParameterSlice_degree w hw hD
  have hmass : realPolynomialMass D₀ ≤ M := (majorZeroParameterSlice_mass D).trans hM
  let F := weightedTranslationBufferedNiltest w d hw hwd (fun _ : U => 1)
    hd Ψ D₀ M hdegree hmass q
  refine ⟨F, rfl, rfl, rfl, ?_, ?_⟩
  · intro u β hβ
    change bufferedTranslationPhase Ψ D₀
      (bchRealTranslationHom w d hwd
        ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
          (fun _ : U => 1) u q)) = _
    rw [hq u]
    exact bufferedTranslationPhase_majorSymbol Ψ D D₀ A u β hβ
  · intro u
    exact weightedTranslationBufferedObservable_norm_le_one w d hw hwd Ψ D₀ _

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3

open MvPolynomial

theorem fractionalCoefficientPolynomial_mem_weightedSupportLE {σ : Type*}
    (D : MvPolynomial σ ℝ) (w : σ → ℕ) (d : ℕ)
    (hD : D ∈ weightedSupportLE w d) :
    fractionalCoefficientPolynomial D ∈ weightedSupportLE w d := by
  intro a ha
  apply hD
  apply mem_support_iff.mpr
  intro hz
  change D.coeff a = 0 at hz
  have hcoeff := mem_support_iff.mp ha
  apply hcoeff
  change (fractionalCoefficientPolynomial D).coeff a = 0
  simp only [fractionalCoefficientPolynomial_coeff, hz, Int.fract_zero]

theorem fractionalCoefficientPolynomial_mass_le_of_weightedSupportLE
    {σ : Type*} [Fintype σ] (D : MvPolynomial σ ℝ)
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (d : ℕ)
    (hD : D ∈ weightedSupportLE w d) :
    realPolynomialMass (fractionalCoefficientPolynomial D) ≤
      ((Fintype.card σ : ℝ) + 1) ^ d := by
  refine (fractionalCoefficientPolynomial_mass_le_card D).trans ?_
  have hcard := boundedExponentSet_card_le (fractionalCoefficientPolynomial D).support d
    (fun a ha => (exponentSum_le_positive_weight w hw a).trans
      (fractionalCoefficientPolynomial_mem_weightedSupportLE D w d hD ha))
  exact_mod_cast hcard

end Erdos3

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module
open scoped NNReal TensorProduct

theorem exists_majorTranslation_degree_reduced_niltest (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U : Type*} [Fintype U] {m : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      (_hd : 0 < d) (Ψ : PatchKernel m) (D : MvPolynomial (U ⊕ Fin m) ℝ)
      (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
      {p : ℝ} (_hp : 0 ≤ p) (_hdim : (Fintype.card U + m : ℕ) ≤ p)
      (_hΨ : (Ψ.lip : ℝ) ≤ Real.exp p),
      ∃ F : (weightedTranslationNilmanifold w d hw hwd).Niltest (fun _ : U => 1),
        F.normBound = 1 ∧ F.ComplexityLE ((p + C) ^ C) ∧
        F.orbit = majorTranslationPolynomialOrbit w d hw hwd
          (fractionalCoefficientPolynomial D)
          (fractionalCoefficientPolynomial_mem_weightedSupportLE D
            (Sum.elim (fun _ : U => 1) w) d hD) A hA ∧
        ∀ u : U → ℤ, ∀ β : Fin m → ℤ,
          (∀ i, |eval (fun j => (u j : ℝ)) (A i) - (β i : ℝ)| ≤ 1 / 2) →
          F.eval u =
            (Ψ.value (fun i => eval (fun j => (u j : ℝ)) (A i) - (β i : ℝ)) : ℂ) *
              (Real.fourierChar (eval (fun j => ((Sum.elim u β j : ℤ) : ℝ)) D) : ℂ) := by
  obtain ⟨a, ha, hbudget⟩ := exists_weightedTranslationBuffered_budget d
  let X : Polynomial ℕ := Polynomial.X
  let Q := (Polynomial.C (d + 1) * (X + 1) + Polynomial.C a) ^ a + 4
  obtain ⟨C, hC, hCbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro U _ m w hw hwd _ _ _ _ _ hd Ψ D hD A hA p hp hdim hΨ
  let v : U ⊕ Fin m → ℕ := Sum.elim (fun _ : U => 1) w
  have hv : ∀ i, 0 < v i := by intro i; cases i with
    | inl i => exact Nat.zero_lt_one
    | inr i => exact hw i
  let Dred := fractionalCoefficientPolynomial D
  have hDred : Dred ∈ weightedSupportLE v d :=
    fractionalCoefficientPolynomial_mem_weightedSupportLE D v d hD
  let M : ℝ≥0 := ((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d
  have hmass : realPolynomialMass Dred ≤ M := by
    change realPolynomialMass Dred ≤ (((Fintype.card U + m + 1 : ℕ) : ℝ) ^ d)
    have hh := fractionalCoefficientPolynomial_mass_le_of_weightedSupportLE D v hv d hD
    simpa only [Dred,
      Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hh
  obtain ⟨F, hnorm, hlip, horbit, heval, _⟩ := exists_majorTranslation_buffered_niltest
    w d hw hwd hd Ψ Dred hDred A hA M hmass
  let q : ℝ := (d + 1 : ℕ) * (p + 1)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    dsimp [q]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hm : (m : ℝ) ≤ q := by
    have hh : (m : ℝ) ≤ (Fintype.card U + m : ℕ) := by exact_mod_cast Nat.le_add_left m (Fintype.card U)
    exact hh.trans (hdim.trans hpq)
  have hM : (M : ℝ) ≤ Real.exp q := by
    have hb : ((Fintype.card U + m + 1 : ℕ) : ℝ) ≤ Real.exp (p + 1) := by
      push_cast at hdim ⊢
      linarith [Real.add_one_le_exp (p + 1)]
    calc
      (M : ℝ) ≤ (Real.exp (p + 1)) ^ d := by
        change (((Fintype.card U + m + 1 : ℕ) : ℝ) ^ d) ≤ _
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) hb d
      _ = Real.exp ((d : ℝ) * (p + 1)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp q := by apply Real.exp_le_exp.mpr; dsimp [q]; push_cast; nlinarith
  obtain ⟨hgeometry, hlipBudget⟩ := hbudget w hw hwd Ψ M q hq hm
    (hΨ.trans (Real.exp_le_exp.mpr hpq)) hM
  have hcost : (q + a) ^ a + 4 ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hCbudget p hp
  have hlog : Real.log (3 + (F.lipBound : ℝ)) ≤ (q + a) ^ a + 4 := by
    have hnonneg : 0 ≤ (q + a) ^ a := by positivity
    have hh := add_le_exp_add_one (by norm_num : (0 : ℝ) ≤ 3) hnonneg
      (show (3 : ℝ) ≤ Real.exp 3 by linarith [Real.add_one_le_exp (3 : ℝ)])
      (show (F.lipBound : ℝ) ≤ Real.exp ((q + a) ^ a) by rw [hlip]; exact hlipBudget)
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    convert hh using 1
    congr 1
    ring
  refine ⟨F, hnorm, ⟨RationalFilteredNilmanifold.GeometryComplexityLE.mono _
    hgeometry (by linarith), ?_⟩, horbit, ?_⟩
  · simpa only [hnorm, NNReal.coe_one, show (2 : ℝ) + 1 = 3 by norm_num]
      using hlog.trans hcost
  · intro u β hβ
    rw [← F.evalReal_integer u, heval _ β hβ]
    have hcast : Sum.elim (fun j => (u j : ℝ)) (fun i => (β i : ℝ)) =
        (fun j => ((Sum.elim u β j : ℤ) : ℝ)) := by
      funext j
      cases j <;> rfl
    rw [hcast]
    congr 1
    exact congrArg (fun z : Circle => (z : ℂ))
      (fractionalCoefficientPolynomial_fourierChar D (Sum.elim u β))

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module
open scoped NNReal TensorProduct

theorem exists_majorTranslation_reduced_niltest (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U : Type*} [Fintype U] {m : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      (_hd : 0 < d) (Ψ : PatchKernel m) (D : MvPolynomial (U ⊕ Fin m) ℝ)
      (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
      {p : ℝ} (_hp : 0 ≤ p) (_hdim : (Fintype.card U + m : ℕ) ≤ p)
      (_hΨ : (Ψ.lip : ℝ) ≤ Real.exp p),
      ∃ F : (weightedTranslationNilmanifold w d hw hwd).Niltest (fun _ : U => 1),
        F.normBound = 1 ∧ F.ComplexityLE ((p + C) ^ C) ∧
        F.orbit = majorTranslationPolynomialOrbit w d hw hwd
          (fractionalCoefficientPolynomial D)
          (fun _α hα => (fractionalCoefficientPolynomial_isWeightedHomogeneous D
            (Sum.elim (fun _ : U => 1) w) d hD (mem_support_iff.mp hα)).le) A hA ∧
        ∀ u : U → ℤ, ∀ β : Fin m → ℤ,
          (∀ i, |eval (fun j => (u j : ℝ)) (A i) - (β i : ℝ)| ≤ 1 / 2) →
          F.eval u =
            (Ψ.value (fun i => eval (fun j => (u j : ℝ)) (A i) - (β i : ℝ)) : ℂ) *
              (Real.fourierChar (eval (fun j => ((Sum.elim u β j : ℤ) : ℝ)) D) : ℂ) := by
  obtain ⟨a, ha, hbudget⟩ := exists_weightedTranslationBuffered_budget d
  let X : Polynomial ℕ := Polynomial.X
  let Q := (Polynomial.C (d + 1) * (X + 1) + Polynomial.C a) ^ a + 4
  obtain ⟨C, hC, hCbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro U _ m w hw hwd _ _ _ _ _ hd Ψ D hD A hA p hp hdim hΨ
  let v : U ⊕ Fin m → ℕ := Sum.elim (fun _ : U => 1) w
  have hv : ∀ i, 0 < v i := by intro i; cases i with
    | inl i => exact Nat.zero_lt_one
    | inr i => exact hw i
  let Dred := fractionalCoefficientPolynomial D
  have hDred : Dred.IsWeightedHomogeneous v d :=
    fractionalCoefficientPolynomial_isWeightedHomogeneous D v d hD
  let M : ℝ≥0 := ((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d
  have hmass : realPolynomialMass Dred ≤ M := by
    change realPolynomialMass Dred ≤ (((Fintype.card U + m + 1 : ℕ) : ℝ) ^ d)
    have hh := fractionalCoefficientPolynomial_mass_le D v hv d hD
    simpa only [Dred,
      Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hh
  obtain ⟨F, hnorm, hlip, horbit, heval, _⟩ := exists_majorTranslation_buffered_niltest
    w d hw hwd hd Ψ Dred (fun α hα => (hDred (mem_support_iff.mp hα)).le) A hA M hmass
  let q : ℝ := (d + 1 : ℕ) * (p + 1)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    dsimp [q]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hm : (m : ℝ) ≤ q := by
    have hh : (m : ℝ) ≤ (Fintype.card U + m : ℕ) := by exact_mod_cast Nat.le_add_left m (Fintype.card U)
    exact hh.trans (hdim.trans hpq)
  have hM : (M : ℝ) ≤ Real.exp q := by
    have hb : ((Fintype.card U + m + 1 : ℕ) : ℝ) ≤ Real.exp (p + 1) := by
      push_cast at hdim ⊢
      linarith [Real.add_one_le_exp (p + 1)]
    calc
      (M : ℝ) ≤ (Real.exp (p + 1)) ^ d := by
        change (((Fintype.card U + m + 1 : ℕ) : ℝ) ^ d) ≤ _
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) hb d
      _ = Real.exp ((d : ℝ) * (p + 1)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp q := by apply Real.exp_le_exp.mpr; dsimp [q]; push_cast; nlinarith
  obtain ⟨hgeometry, hlipBudget⟩ := hbudget w hw hwd Ψ M q hq hm
    (hΨ.trans (Real.exp_le_exp.mpr hpq)) hM
  have hcost : (q + a) ^ a + 4 ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hCbudget p hp
  have hlog : Real.log (3 + (F.lipBound : ℝ)) ≤ (q + a) ^ a + 4 := by
    have hnonneg : 0 ≤ (q + a) ^ a := by positivity
    have hh := add_le_exp_add_one (by norm_num : (0 : ℝ) ≤ 3) hnonneg
      (show (3 : ℝ) ≤ Real.exp 3 by linarith [Real.add_one_le_exp (3 : ℝ)])
      (show (F.lipBound : ℝ) ≤ Real.exp ((q + a) ^ a) by rw [hlip]; exact hlipBudget)
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    convert hh using 1
    congr 1
    ring
  refine ⟨F, hnorm, ⟨RationalFilteredNilmanifold.GeometryComplexityLE.mono _
    hgeometry (by linarith), ?_⟩, horbit, ?_⟩
  · simpa only [hnorm, NNReal.coe_one, show (2 : ℝ) + 1 = 3 by norm_num]
      using hlog.trans hcost
  · intro u β hβ
    rw [← F.evalReal_integer u, heval _ β hβ]
    have hcast : Sum.elim (fun j => (u j : ℝ)) (fun i => (β i : ℝ)) =
        (fun j => ((Sum.elim u β j : ℤ) : ℝ)) := by
      funext j
      cases j <;> rfl
    rw [hcast]
    congr 1
    exact congrArg (fun z : Circle => (z : ℂ))
      (fractionalCoefficientPolynomial_fourierChar D (Sum.elim u β))

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module
open scoped NNReal TensorProduct

section Construction

variable {U : Type*} {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]
    [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

theorem exists_majorTranslation_twisted_niltest (hd : 0 < d)
    (M : ℕ) (hM : 0 < M) (Ψ : PatchKernel m) (D : MvPolynomial (U ⊕ Fin m) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (B K : ℝ≥0) (hB : realPolynomialMass D ≤ B)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r)) :
    ∃ F : (weightedTranslationResidueNilmanifold w d hw hwd M hM).Niltest (fun _ : U => 1),
      F.normBound = 1 ∧ F.lipBound = 2 * twistedBufferedTranslationTermLip w d Ψ B K ∧
      F.orbit = majorTranslationPolynomialOrbit w d hw hwd D hD A hA ∧
      ∀ u : U → ℝ, ∀ β : Fin m → ℤ,
        (∀ i, |eval u (A i) - (β i : ℝ)| ≤ 1 / 2) →
        F.evalReal u =
          T (fun i => eval u (A i) - (β i : ℝ)) (fun i => (β i : ZMod M)) *
            (Ψ.value (fun i => eval u (A i) - (β i : ℝ)) : ℂ) *
              (Real.fourierChar (eval (Sum.elim u (fun i => (β i : ℝ))) D) : ℂ) := by
  let q := majorTranslationPolynomialOrbit w d hw hwd D hD A hA
  have hq := majorTranslationPolynomialOrbit_realEval w d hw hwd D hD A hA
  let D₀ := specializeMajorParameters (RingHom.id ℝ) D 0
  have hdegree : D₀.totalDegree ≤ d := majorZeroParameterSlice_degree w hw hD
  have hmass : realPolynomialMass D₀ ≤ B := (majorZeroParameterSlice_mass D).trans hB
  let F := weightedTranslationTwistedNiltest w d hw hwd M hM (fun _ : U => 1)
    hd Ψ D₀ B K hdegree hmass T hT hLip q
  refine ⟨F, rfl, rfl, rfl, ?_⟩
  intro u β hβ
  change twistedBufferedTranslationPhase M Ψ D₀ T
    (bchRealTranslationHom w d hwd
      ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
        (fun _ : U => 1) u q)) = _
  rw [hq u]
  exact twistedBufferedTranslationPhase_majorSymbol M Ψ D D₀ T A u β hβ

end Construction

theorem exists_majorTranslation_reduced_twisted_niltest (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U : Type*} [Fintype U] {m : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      (_hd : 0 < d) (M : ℕ) (hM : 0 < M) (Ψ : PatchKernel m)
      (D : MvPolynomial (U ⊕ Fin m) ℝ)
      (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
      (K : ℝ≥0) (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
      (_hT : ∀ x r, ‖T x r‖ ≤ 1) (_hLip : ∀ r, LipschitzWith K (fun x => T x r))
      {p : ℝ} (_hp : 0 ≤ p) (_hdim : (Fintype.card U + m : ℕ) ≤ p)
      (_hMp : (M : ℝ) ≤ Real.exp p) (_hΨ : (Ψ.lip : ℝ) ≤ Real.exp p)
      (_hK : (K : ℝ) ≤ Real.exp p),
      ∃ F : (weightedTranslationResidueNilmanifold w d hw hwd M hM).Niltest (fun _ : U => 1),
        F.normBound = 1 ∧ F.ComplexityLE ((p + C) ^ C) ∧
        F.orbit = majorTranslationPolynomialOrbit w d hw hwd
          (fractionalCoefficientPolynomial D)
          (fun _ hα => (fractionalCoefficientPolynomial_isWeightedHomogeneous D
            (Sum.elim (fun _ : U => 1) w) d hD (mem_support_iff.mp hα)).le) A hA ∧
        ∀ u : U → ℤ, ∀ β : Fin m → ℤ,
          (∀ i, |eval (fun j => (u j : ℝ)) (A i) - (β i : ℝ)| ≤ 1 / 2) →
          F.eval u =
            T (fun i => eval (fun j => (u j : ℝ)) (A i) - (β i : ℝ))
              (fun i => (β i : ZMod M)) *
            (Ψ.value (fun i => eval (fun j => (u j : ℝ)) (A i) - (β i : ℝ)) : ℂ) *
              (Real.fourierChar (eval (fun j => ((Sum.elim u β j : ℤ) : ℝ)) D) : ℂ) := by
  obtain ⟨a, _, hbudget⟩ := exists_weightedTwistedTranslation_budget d
  let X : Polynomial ℕ := Polynomial.X
  let Q := (Polynomial.C (d + 1) * (X + 1) + Polynomial.C a) ^ a
  obtain ⟨C, hC, hCbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro U _ m w hw hwd _ _ _ _ _ hd M hM Ψ D hD A hA K T hT hLip p hp hdim hMp hΨ hK
  let v : U ⊕ Fin m → ℕ := Sum.elim (fun _ : U => 1) w
  have hv : ∀ i, 0 < v i := by
    intro i
    cases i with
    | inl i => exact Nat.zero_lt_one
    | inr i => exact hw i
  let Dred := fractionalCoefficientPolynomial D
  have hDred : Dred.IsWeightedHomogeneous v d :=
    fractionalCoefficientPolynomial_isWeightedHomogeneous D v d hD
  let B : ℝ≥0 := ((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d
  have hmass : realPolynomialMass Dred ≤ B := by
    change realPolynomialMass Dred ≤ (((Fintype.card U + m + 1 : ℕ) : ℝ) ^ d)
    have hh := fractionalCoefficientPolynomial_mass_le D v hv d hD
    simpa only [Dred, Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hh
  obtain ⟨F, hnorm, hlip, horbit, heval⟩ := exists_majorTranslation_twisted_niltest
    w d hw hwd hd M hM Ψ Dred (fun _ hα => (hDred (mem_support_iff.mp hα)).le)
      A hA B K hmass T hT hLip
  let q : ℝ := (d + 1 : ℕ) * (p + 1)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    dsimp [q]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hm : (m : ℝ) ≤ q := by
    have hh : (m : ℝ) ≤ (Fintype.card U + m : ℕ) := by
      exact_mod_cast Nat.le_add_left m (Fintype.card U)
    exact hh.trans (hdim.trans hpq)
  have hB : (B : ℝ) ≤ Real.exp q := by
    have hb : ((Fintype.card U + m + 1 : ℕ) : ℝ) ≤ Real.exp (p + 1) := by
      push_cast at hdim ⊢
      linarith [Real.add_one_le_exp (p + 1)]
    calc
      (B : ℝ) ≤ (Real.exp (p + 1)) ^ d := by
        change (((Fintype.card U + m + 1 : ℕ) : ℝ) ^ d) ≤ _
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) hb d
      _ = Real.exp ((d : ℝ) * (p + 1)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp q := by apply Real.exp_le_exp.mpr; dsimp [q]; push_cast; nlinarith
  obtain ⟨hgeometry, hlog⟩ := hbudget w hw hwd M hM Ψ B K q hq hm
    (hMp.trans (Real.exp_le_exp.mpr hpq)) (hΨ.trans (Real.exp_le_exp.mpr hpq))
    hB (hK.trans (Real.exp_le_exp.mpr hpq))
  have hcost : (q + a) ^ a ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hCbudget p hp
  refine ⟨F, hnorm,
    ⟨RationalFilteredNilmanifold.GeometryComplexityLE.mono _ hgeometry hcost, ?_⟩,
    horbit, ?_⟩
  · simpa only [hnorm, hlip, NNReal.coe_one, show (2 : ℝ) + 1 = 3 by norm_num]
      using hlog.trans hcost
  · intro u β hβ
    rw [← F.evalReal_integer u, heval _ β hβ]
    have hcast : Sum.elim (fun j => (u j : ℝ)) (fun i => (β i : ℝ)) =
        (fun j => ((Sum.elim u β j : ℤ) : ℝ)) := by
      funext j
      cases j <;> rfl
    rw [hcast]
    congr 1
    exact congrArg (fun z : Circle => (z : ℂ))
      (fractionalCoefficientPolynomial_fourierChar D (Sum.elim u β))

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module
open scoped NNReal TensorProduct

section Construction

variable {U : Type*} [Fintype U] {m : ℕ}

omit [Fintype U] in
theorem fractionalMajorPolynomial_support (w : Fin m → ℕ) (d : ℕ)
    (D : MvPolynomial (U ⊕ Fin m) ℝ)
    (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d) :
    fractionalCoefficientPolynomial D ∈
      weightedSupportLE (Sum.elim (fun _ : U => 1) w) d :=
  fun _ hα => (fractionalCoefficientPolynomial_isWeightedHomogeneous D
    (Sum.elim (fun _ : U => 1) w) d hD (mem_support_iff.mp hα)).le

theorem fractionalMajorPolynomial_mass (w : Fin m → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (D : MvPolynomial (U ⊕ Fin m) ℝ)
    (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d) :
    realPolynomialMass (fractionalCoefficientPolynomial D) ≤
      ((((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d : ℝ≥0) : ℝ) := by
  change realPolynomialMass (fractionalCoefficientPolynomial D) ≤
    (((Fintype.card U + m + 1 : ℕ) : ℝ) ^ d)
  have hv : ∀ i, 0 < Sum.elim (fun _ : U => 1) w i := by
    intro i
    cases i with
    | inl i => exact Nat.zero_lt_one
    | inr i => exact hw i
  simpa only [Fintype.card_sum, Fintype.card_fin, NNReal.coe_pow,
    NNReal.coe_natCast, Nat.cast_add, Nat.cast_one] using
    fractionalCoefficientPolynomial_mass_le D (Sum.elim (fun _ : U => 1) w) hv d hD

variable (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]
    [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

noncomputable def reducedMajorTranslationTwistedNiltest (hd : 0 < d)
    (M : ℕ) (hM : 0 < M) (Ψ : PatchKernel m)
    (D : MvPolynomial (U ⊕ Fin m) ℝ)
    (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
    (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (K : ℝ≥0) (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r)) :
    (weightedTranslationResidueNilmanifold w d hw hwd M hM).Niltest (fun _ : U => 1) :=
  weightedTranslationTwistedNiltest w d hw hwd M hM (fun _ : U => 1) hd Ψ
    (specializeMajorParameters (RingHom.id ℝ) (fractionalCoefficientPolynomial D) 0)
    (((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d) K
    (majorZeroParameterSlice_degree w hw (fractionalMajorPolynomial_support w d D hD))
    ((majorZeroParameterSlice_mass (fractionalCoefficientPolynomial D)).trans
      (fractionalMajorPolynomial_mass w d hw D hD)) T hT hLip
    (majorTranslationPolynomialOrbit w d hw hwd (fractionalCoefficientPolynomial D)
      (fractionalMajorPolynomial_support w d D hD) A hA)

variable (hd : 0 < d) (M : ℕ) (hM : 0 < M) (Ψ : PatchKernel m)
    (D : MvPolynomial (U ⊕ Fin m) ℝ)
    (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
    (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (K : ℝ≥0) (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r))

@[simp] theorem reducedMajorTranslationTwistedNiltest_normBound :
    (reducedMajorTranslationTwistedNiltest w d hw hwd hd M hM Ψ D hD A hA K T hT hLip).normBound = 1 := rfl

@[simp] theorem reducedMajorTranslationTwistedNiltest_lipBound :
    (reducedMajorTranslationTwistedNiltest w d hw hwd hd M hM Ψ D hD A hA K T hT hLip).lipBound = 2 * twistedBufferedTranslationTermLip w d Ψ
        (((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d) K := rfl

@[simp] theorem reducedMajorTranslationTwistedNiltest_orbit :
    (reducedMajorTranslationTwistedNiltest w d hw hwd hd M hM Ψ D hD A hA K T hT hLip).orbit = majorTranslationPolynomialOrbit w d hw hwd (fractionalCoefficientPolynomial D)
        (fractionalMajorPolynomial_support w d D hD) A hA := rfl

@[simp] theorem reducedMajorTranslationTwistedNiltest_observable :
    (reducedMajorTranslationTwistedNiltest w d hw hwd hd M hM Ψ D hD A hA K T hT hLip).observable = weightedTranslationTwistedObservable w d hw hwd M hM Ψ
        (specializeMajorParameters (RingHom.id ℝ) (fractionalCoefficientPolynomial D) 0) T := rfl

theorem reducedMajorTranslationTwistedNiltest_evalReal
    (u : U → ℝ) (β : Fin m → ℤ)
    (hβ : ∀ i, |eval u (A i) - (β i : ℝ)| ≤ 1 / 2) :
    (reducedMajorTranslationTwistedNiltest w d hw hwd hd M hM Ψ D hD A hA K T hT hLip).evalReal u =
      T (fun i => eval u (A i) - (β i : ℝ)) (fun i => (β i : ZMod M)) *
        (Ψ.value (fun i => eval u (A i) - (β i : ℝ)) : ℂ) *
          (Real.fourierChar (eval (Sum.elim u (fun i => (β i : ℝ)))
            (fractionalCoefficientPolynomial D)) : ℂ) := by
  change twistedBufferedTranslationPhase M Ψ
    (specializeMajorParameters (RingHom.id ℝ) (fractionalCoefficientPolynomial D) 0) T
    (bchRealTranslationHom w d hwd
      ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
        (fun _ : U => 1) u
        (majorTranslationPolynomialOrbit w d hw hwd (fractionalCoefficientPolynomial D)
          (fractionalMajorPolynomial_support w d D hD) A hA))) = _
  rw [majorTranslationPolynomialOrbit_realEval]
  exact twistedBufferedTranslationPhase_majorSymbol M Ψ (fractionalCoefficientPolynomial D)
    (specializeMajorParameters (RingHom.id ℝ) (fractionalCoefficientPolynomial D) 0) T A u β hβ

theorem reducedMajorTranslationTwistedNiltest_eval
    (u : U → ℤ) (β : Fin m → ℤ)
    (hβ : ∀ i, |eval (fun j => (u j : ℝ)) (A i) - (β i : ℝ)| ≤ 1 / 2) :
    (reducedMajorTranslationTwistedNiltest w d hw hwd hd M hM Ψ D hD A hA K T hT hLip).eval u =
      T (fun i => eval (fun j => (u j : ℝ)) (A i) - (β i : ℝ))
        (fun i => (β i : ZMod M)) *
        (Ψ.value (fun i => eval (fun j => (u j : ℝ)) (A i) - (β i : ℝ)) : ℂ) *
          (Real.fourierChar (eval (fun j => ((Sum.elim u β j : ℤ) : ℝ)) D) : ℂ) := by
  rw [← RationalFilteredNilmanifold.Niltest.evalReal_integer,
    reducedMajorTranslationTwistedNiltest_evalReal w d hw hwd hd M hM Ψ D hD A hA K T hT hLip
      _ β hβ]
  have hcast : Sum.elim (fun j => (u j : ℝ)) (fun i => (β i : ℝ)) =
      (fun j => ((Sum.elim u β j : ℤ) : ℝ)) := by
    funext j
    cases j <;> rfl
  rw [hcast]
  congr 1
  exact congrArg (fun z : Circle => (z : ℂ))
    (fractionalCoefficientPolynomial_fourierChar D (Sum.elim u β))

end Construction

theorem exists_reducedMajorTranslationTwistedNiltest_complexity (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U : Type*} [Fintype U] {m : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      (hd : 0 < d) (M : ℕ) (hM : 0 < M) (Ψ : PatchKernel m)
      (D : MvPolynomial (U ⊕ Fin m) ℝ)
      (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
      (K : ℝ≥0) (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
      (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r))
      {p : ℝ} (_hp : 0 ≤ p) (_hdim : (Fintype.card U + m : ℕ) ≤ p)
      (_hMp : (M : ℝ) ≤ Real.exp p) (_hΨ : (Ψ.lip : ℝ) ≤ Real.exp p)
      (_hK : (K : ℝ) ≤ Real.exp p),
      (reducedMajorTranslationTwistedNiltest w d hw hwd hd M hM Ψ D hD A hA K T hT hLip).ComplexityLE ((p + C) ^ C) := by
  obtain ⟨C, hC, hbudget⟩ := exists_reducedTwistedTranslation_budget d
  refine ⟨C, hC, ?_⟩
  intro U _ m w hw hwd _ _ _ _ _ hd M hM Ψ D hD A hA K T hT hLip p hp hdim hMp hΨ hK
  obtain ⟨hgeometry, hlog⟩ := hbudget U w hw hwd M hM Ψ K p hp hdim hMp hΨ hK
  refine ⟨hgeometry, ?_⟩
  simpa only [reducedMajorTranslationTwistedNiltest_normBound,
    reducedMajorTranslationTwistedNiltest_lipBound, NNReal.coe_one,
    show (2 : ℝ) + 1 = 3 by norm_num] using hlog

end Erdos3.PolynomialTranslationLie

end

end OAI
