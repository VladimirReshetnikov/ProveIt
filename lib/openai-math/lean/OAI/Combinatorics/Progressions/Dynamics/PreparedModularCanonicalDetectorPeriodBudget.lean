import OAI.Combinatorics.Progressions.Estimates.AllocatedCanonicalPeriodPrimitiveBounds
import OAI.Combinatorics.Progressions.Lattices.AllocatedAffineAnalyticBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem exists_canonicalSlicedModelPrefactor_budget (m dim : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Fin m → Type*} [∀ j, Fintype (I j)]
      {n : Fin m → ℕ} {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
      {P Pnum Pk : ℝ}, 0 ≤ P → Pnum ∈ Set.Icc 0 P → Pk ∈ Set.Icc 0 P →
      (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ P →
      (∀ j, (Fintype.card (Q j) : ℝ) ≤ P) →
      let Fmodel := (m * (2 : ℝ) ^ Fintype.card (Fin dim)) * (Pnum + 8) * (1 + 4 * Pnum) +
        Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
        ∑ j : Fin m, (Fintype.card (Q j) : ℝ) *
          (Fintype.card (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type) * ((m + 1 : ℕ) * Pk))
      Fmodel ∈ Set.Icc 0 ((P + C) ^ C) := by
  let rows : ℕ := ∑ j : Fin m,
    Fintype.card (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type)
  let X : Polynomial ℕ := Polynomial.X
  let poly := Polynomial.C (m * 2 ^ dim) * (X + 8) * (1 + 4 * X) +
    X * (Polynomial.C (m * 2 ^ (m + 1)) * X) +
    X * (Polynomial.C rows * (Polynomial.C (m + 1) * X))
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro I _ n Q _ P Pnum Pk hP hPnum hPk haxes hQ Fmodel
  have hnum : 0 ≤ Pnum := hPnum.1
  have hk : 0 ≤ Pk := hPk.1
  have hsum : (∑ j : Fin m, (Fintype.card (Q j) : ℝ) *
      (Fintype.card (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type) * ((m + 1 : ℕ) * Pk))) ≤
      P * (rows * ((m + 1 : ℕ) * P)) := by
    calc
      _ ≤ ∑ j : Fin m, P *
          (Fintype.card (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type) * ((m + 1 : ℕ) * P)) := by
        apply Finset.sum_le_sum
        intro j _
        gcongr
        exact hQ j
        exact hPk.2
      _ = _ := by
        simp only [rows, Nat.cast_sum]
        rw [← Finset.mul_sum, ← Finset.sum_mul]
  have hF : Fmodel ≤ (m * (2 : ℝ) ^ dim) * (P + 8) * (1 + 4 * P) +
      P * ((m * 2 ^ (m + 1) : ℕ) * P) + P * (rows * ((m + 1 : ℕ) * P)) := by
    dsimp only [Fmodel]
    simp only [Fintype.card_fin]
    apply add_le_add _ hsum
    gcongr
    exact hPnum.2
    exact hPnum.2
    exact hPk.2
  refine ⟨by dsimp only [Fmodel]; positivity, hF.trans ?_⟩
  simpa [poly, X, Polynomial.eval₂_pow] using hbound P hP

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

theorem exists_canonicalSlicedPeriod_common_budget (m dim nX Cgrid : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {A : Type*} [Fintype A]
      (n : Fin m → ℕ) (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
      {P Pk Qstride p : ℝ}, 0 ≤ P → Pk ∈ Set.Icc 0 P →
      Qstride ∈ Set.Icc 0 P → p ∈ Set.Icc 0 P →
      (Fintype.card A : ℝ) ≤ P → (∀ j, (n j : ℝ) ≤ P) →
      (∀ j, (Fintype.card (Q j) : ℝ) ≤ P) →
      let O := fun j : Fin m => (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type)
      let budget := (P + C) ^ C
      let L := ((m + 1 : ℕ) : ℝ) * Pk
      let qlog := L + nX * Qstride
      let maskLog := (Fintype.card A : ℝ) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
        ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (O j) * L)
      let labelLog := (∑ j, (n j : ℝ) * L) + ∑ j, (Fintype.card (Q j) : ℝ) * L
      P ≤ budget ∧ L ∈ Set.Icc 0 budget ∧ qlog ∈ Set.Icc 0 budget ∧
      (p + 1) ∈ Set.Icc 0 budget ∧ maskLog ∈ Set.Icc 0 budget ∧
      labelLog ∈ Set.Icc 0 budget ∧
      ((dim : ℝ) + qlog + (p + 1) + 1) ∈ Set.Icc 0 budget ∧
      ((Cgrid : ℝ) + ((dim + 1 : ℕ) : ℝ) * qlog + (p + 1) + 4) ∈ Set.Icc 0 budget ∧
      ∀ {M period : ℕ} [NeZero period],
        (M : ℝ) ≤ Real.exp Pk → period ≤ M ^ (m + 1) →
        (period : ℝ) ≤ Real.exp budget ∧
        (layerKernelIndexBound m M : ℝ) ^ Fintype.card A * coefficientDeckPeriodCap O Q period ≤
          Real.exp budget ∧
        (Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, Q j → ZMod period)) : ℝ) ≤
          Real.exp budget := by
  let rows : ℕ := ∑ j : Fin m, Fintype.card
    (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type)
  let X : Polynomial ℕ := Polynomial.X
  let Lp := Polynomial.C (m + 1) * X
  let Qp := Lp + Polynomial.C nX * X
  let Mp := X * (Polynomial.C (m * 2 ^ (m + 1)) * X) + X * (Polynomial.C rows * Lp)
  let labelp := Polynomial.C (2 * m) * X * Lp
  let tp := Polynomial.C dim + Qp + (X + 1) + 1
  let gp := Polynomial.C Cgrid + Polynomial.C (dim + 1) * Qp + (X + 1) + 4
  let poly := X + Lp + Mp + labelp + tp + gp
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro A _ n Q _ P Pk Qstride p hP hPk hQstride hp hA hn hQ O budget L qlog maskLog labelLog
  have hPk0 : 0 ≤ Pk := hPk.1
  have hp0 : 0 ≤ p := hp.1
  let Lb := ((m + 1 : ℕ) : ℝ) * P
  let Qb := Lb + nX * P
  let Mb := P * ((m * 2 ^ (m + 1) : ℕ) * P) + P * (rows * Lb)
  let labelb := (2 * m : ℕ) * P * Lb
  let tb := (dim : ℝ) + Qb + (P + 1) + 1
  let gb := (Cgrid : ℝ) + ((dim + 1 : ℕ) : ℝ) * Qb + (P + 1) + 4
  have hLb : 0 ≤ Lb := by dsimp only [Lb]; positivity
  have hQb : 0 ≤ Qb := by dsimp only [Qb]; positivity
  have hMb : 0 ≤ Mb := by dsimp only [Mb]; positivity
  have hlb : 0 ≤ labelb := by dsimp only [labelb]; positivity
  have htb : 0 ≤ tb := by dsimp only [tb]; positivity
  have hgb : 0 ≤ gb := by dsimp only [gb]; positivity
  have htotal : P + Lb + Mb + labelb + tb + gb ≤ budget := by
    simpa [poly, X, Lp, Qp, Mp, labelp, tp, gp, Lb, Qb, Mb, labelb, tb, gb,
      Polynomial.eval₂_pow] using hbound P hP
  have hL : L ≤ Lb := mul_le_mul_of_nonneg_left hPk.2 (Nat.cast_nonneg _)
  have hL0 : 0 ≤ L := mul_nonneg (Nat.cast_nonneg _) hPk.1
  have hqlog : qlog ≤ Qb := add_le_add hL
    (mul_le_mul_of_nonneg_left hQstride.2 (Nat.cast_nonneg _))
  have hqlog0 : 0 ≤ qlog := add_nonneg hL0 (mul_nonneg (Nat.cast_nonneg _) hQstride.1)
  have hsum : (∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (O j) * L)) ≤ P * (rows * Lb) := by
    calc
      _ ≤ ∑ j : Fin m, P * (Fintype.card (O j) * Lb) := by
        apply Finset.sum_le_sum
        intro j _
        gcongr
        exact hQ j
      _ = _ := by
        simp only [O, rows, Nat.cast_sum]
        rw [← Finset.mul_sum, ← Finset.sum_mul]
  have hmask : maskLog ≤ Mb := by
    apply add_le_add _ hsum
    gcongr
    exact hPk.2
  have hlabel : labelLog ≤ labelb := by
    calc
      _ ≤ (∑ _j : Fin m, P * Lb) + ∑ _j : Fin m, P * Lb := by
        apply add_le_add
        · apply Finset.sum_le_sum
          intro j _
          gcongr
          exact hn j
        · apply Finset.sum_le_sum
          intro j _
          gcongr
          exact hQ j
      _ = _ := by simp only [labelb, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]; ring
  have ht : (dim : ℝ) + qlog + (p + 1) + 1 ≤ tb := by
    dsimp only [tb]
    gcongr
    exact hp.2
  have hg : (Cgrid : ℝ) + ((dim + 1 : ℕ) : ℝ) * qlog + (p + 1) + 4 ≤ gb := by
    dsimp only [gb]
    gcongr
    exact hp.2
  have hLbudget : L ≤ budget := by linarith
  have hmaskbudget : maskLog ≤ budget := by linarith
  have hlabelbudget : labelLog ≤ budget := by linarith
  refine ⟨by linarith, ⟨hL0, hLbudget⟩,
    ⟨hqlog0, ?_⟩, ⟨by positivity, ?_⟩,
    ⟨by dsimp only [maskLog]; positivity, hmaskbudget⟩,
    ⟨by dsimp only [labelLog]; positivity, hlabelbudget⟩,
    ⟨by positivity, by linarith⟩, ⟨by positivity, by linarith⟩, ?_⟩
  · dsimp only [tb] at htotal htb
    linarith [Nat.cast_nonneg (α := ℝ) dim]
  · dsimp only [tb] at htotal htb
    linarith [Nat.cast_nonneg (α := ℝ) dim, hp.2]
  · intro M period _ hM hperiod
    obtain ⟨hperiodBound, hmaskBound, hlabelBound⟩ :=
      canonicalPeriod_primitive_bounds A n O Q hM hperiod
    exact ⟨hperiodBound.trans (Real.exp_le_exp.mpr hLbudget),
      hmaskBound.trans (Real.exp_le_exp.mpr hmaskbudget),
      hlabelBound.trans (Real.exp_le_exp.mpr hlabelbudget)⟩

theorem exists_detectedCanonical_common_grid_budget (m dim nX : ℕ) (Ag : ℝ≥0) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {A : Type*} [Fintype A]
      (n : Fin m → ℕ) (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
      {P Pk Qstride p : ℝ}, 0 ≤ P → Pk ∈ Set.Icc 0 P →
      Qstride ∈ Set.Icc 0 P → p ∈ Set.Icc 0 P →
      (Fintype.card A : ℝ) ≤ P → (∀ j, (n j : ℝ) ≤ P) →
      (∀ j, (Fintype.card (Q j) : ℝ) ≤ P) →
      let O := fun j : Fin m => (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type)
      let budget := (P + C) ^ C
      let δ := Real.exp (-(p + 1))
      P ≤ budget ∧ 0 < δ ∧ δ ≤ 1 ∧ δ⁻¹ ≤ Real.exp budget ∧
      ∃ T : ℕ, (T : ℝ) ≤ Real.exp budget ∧
      ∀ {M period : ℕ} [NeZero period] (stride : Fin nX → ℕ),
        (M : ℝ) ≤ Real.exp Pk → period ≤ M ^ (m + 1) →
        (∀ i, 0 < stride i) → (∀ i, (stride i : ℝ) ≤ Real.exp Qstride) →
        let modulus := residueRefinedPeriod period stride
        (period : ℝ) ≤ Real.exp budget ∧
        (layerKernelIndexBound m M : ℝ) ^ Fintype.card A * coefficientDeckPeriodCap O Q period ≤
          Real.exp budget ∧
        (Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, Q j → ZMod period)) : ℝ) ≤
          Real.exp budget ∧
        (((dim + 1) * modulus : ℕ) : ℝ) / δ ≤ T ∧
        1 ≤ Real.exp budget ∧
        scalarCubePrimitiveEnvelope Empty Ag 16 (128 * probabilityProfileLipschitz) 1 ≤ Real.exp budget ∧
        scalarCubePrimitiveEnvelope (Fin dim) Ag 1 0 modulus ≤ Real.exp budget ∧
        ∀ {Y : Type*} (step : Y → ℕ),
          (∀ y, (step y : ℝ) ≤ 4 * Real.exp (p + 1)) →
          ∀ y, ((step y * modulus : ℕ) : ℝ) ≤ Real.exp budget := by
  obtain ⟨Cgrid, _, hgrid⟩ := exists_detectedCanonicalGridParameters m dim nX Ag
  obtain ⟨C, hC, hbudget⟩ := exists_canonicalSlicedPeriod_common_budget m dim nX Cgrid
  refine ⟨C, hC, ?_⟩
  intro A _ n Q _ P Pk Qstride p hP hPk hQstride hp hA hn hQ O budget δ
  obtain ⟨hPB, _, _, hF, _, _, htg, hpg, hperiodBounds⟩ :=
    hbudget n Q hP hPk hQstride hp hA hn hQ
  obtain ⟨hδ, hδone, hδinv, _, _, T, hT, hgridAll⟩ := hgrid hPk.1 hQstride.1 hp.1
  refine ⟨hPB, hδ, hδone, hδinv.trans (Real.exp_le_exp.mpr hF.2), T,
    hT.trans (Real.exp_le_exp.mpr htg.2), ?_⟩
  intro M period _ stride hM hperiod hstride hstrideBound modulus
  obtain ⟨hpBound, hmBound, hlBound⟩ := hperiodBounds hM hperiod
  obtain ⟨hQT, hPg, hcP, hsP, hstep⟩ :=
    hgridAll stride hM (NeZero.pos period) hperiod hstride hstrideBound
  have hgexp := Real.exp_le_exp.mpr hpg.2
  refine ⟨hpBound, hmBound, hlBound, hQT, hPg.trans hgexp,
    hcP.trans hgexp, hsP.trans hgexp, ?_⟩
  intro Y step hstepBound y
  exact (hstep step hstepBound y).trans hgexp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

theorem exists_preparedModularCanonicalDetector_period_budget (m dim Cgrid : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {nX : ℕ} {A : Type*} [Fintype A]
      (n : Fin m → ℕ) (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
      {P Pk Qstride p : ℝ}, 0 ≤ P → (nX : ℝ) ≤ P → Pk ∈ Set.Icc 0 P →
      Qstride ∈ Set.Icc 0 P → p ∈ Set.Icc 0 P →
      (Fintype.card A : ℝ) ≤ P → (∀ j, (n j : ℝ) ≤ P) →
      (∀ j, (Fintype.card (Q j) : ℝ) ≤ P) →
      let O := fun j : Fin m => (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type)
      let budget := (P + C) ^ C
      let L := ((m + 1 : ℕ) : ℝ) * Pk
      let qlog := L + nX * Qstride
      let maskLog := (Fintype.card A : ℝ) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
        ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (O j) * L)
      let labelLog := (∑ j, (n j : ℝ) * L) + ∑ j, (Fintype.card (Q j) : ℝ) * L
      P ≤ budget ∧ L ∈ Set.Icc 0 budget ∧ qlog ∈ Set.Icc 0 budget ∧
      (p + 1) ∈ Set.Icc 0 budget ∧ maskLog ∈ Set.Icc 0 budget ∧
      labelLog ∈ Set.Icc 0 budget ∧
      ((dim : ℝ) + qlog + (p + 1) + 1) ∈ Set.Icc 0 budget ∧
      ((Cgrid : ℝ) + ((dim + 1 : ℕ) : ℝ) * qlog + (p + 1) + 4) ∈ Set.Icc 0 budget ∧
      ∀ {M period : ℕ} [NeZero period],
        (M : ℝ) ≤ Real.exp Pk → period ≤ M ^ (m + 1) →
        (period : ℝ) ≤ Real.exp budget ∧
        (layerKernelIndexBound m M : ℝ) ^ Fintype.card A * coefficientDeckPeriodCap O Q period ≤
          Real.exp budget ∧
        (Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, Q j → ZMod period)) : ℝ) ≤
          Real.exp budget := by
  let rows : ℕ := ∑ j : Fin m, Fintype.card
    (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type)
  let X : Polynomial ℕ := Polynomial.X
  let Lp := Polynomial.C (m + 1) * X
  let Qp := Lp + X * X
  let Mp := X * (Polynomial.C (m * 2 ^ (m + 1)) * X) + X * (Polynomial.C rows * Lp)
  let labelp := Polynomial.C (2 * m) * X * Lp
  let tp := Polynomial.C dim + Qp + (X + 1) + 1
  let gp := Polynomial.C Cgrid + Polynomial.C (dim + 1) * Qp + (X + 1) + 4
  let poly := X + Lp + Mp + labelp + tp + gp
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro nX A _ n Q _ P Pk Qstride p hP hnX hPk hQstride hp hA hn hQ O budget L qlog maskLog labelLog
  have hPk0 : 0 ≤ Pk := hPk.1
  have hp0 : 0 ≤ p := hp.1
  let Lb := ((m + 1 : ℕ) : ℝ) * P
  let Qb := Lb + P * P
  let Mb := P * ((m * 2 ^ (m + 1) : ℕ) * P) + P * (rows * Lb)
  let labelb := (2 * m : ℕ) * P * Lb
  let tb := (dim : ℝ) + Qb + (P + 1) + 1
  let gb := (Cgrid : ℝ) + ((dim + 1 : ℕ) : ℝ) * Qb + (P + 1) + 4
  have hLb : 0 ≤ Lb := by dsimp only [Lb]; positivity
  have hQb : 0 ≤ Qb := by dsimp only [Qb]; positivity
  have hMb : 0 ≤ Mb := by dsimp only [Mb]; positivity
  have hlb : 0 ≤ labelb := by dsimp only [labelb]; positivity
  have htb : 0 ≤ tb := by dsimp only [tb]; positivity
  have hgb : 0 ≤ gb := by dsimp only [gb]; positivity
  have htotal : P + Lb + Mb + labelb + tb + gb ≤ budget := by
    simpa [poly, X, Lp, Qp, Mp, labelp, tp, gp, Lb, Qb, Mb, labelb, tb, gb,
      Polynomial.eval₂_pow] using hbound P hP
  have hL : L ≤ Lb := mul_le_mul_of_nonneg_left hPk.2 (Nat.cast_nonneg _)
  have hL0 : 0 ≤ L := mul_nonneg (Nat.cast_nonneg _) hPk.1
  have hqlog : qlog ≤ Qb := add_le_add hL
    (mul_le_mul hnX hQstride.2 hQstride.1 hP)
  have hqlog0 : 0 ≤ qlog := add_nonneg hL0 (mul_nonneg (Nat.cast_nonneg _) hQstride.1)
  have hsum : (∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (O j) * L)) ≤ P * (rows * Lb) := by
    calc
      _ ≤ ∑ j : Fin m, P * (Fintype.card (O j) * Lb) := by
        apply Finset.sum_le_sum
        intro j _
        gcongr
        exact hQ j
      _ = _ := by
        simp only [O, rows, Nat.cast_sum]
        rw [← Finset.mul_sum, ← Finset.sum_mul]
  have hmask : maskLog ≤ Mb := by
    apply add_le_add _ hsum
    gcongr
    exact hPk.2
  have hlabel : labelLog ≤ labelb := by
    calc
      _ ≤ (∑ _j : Fin m, P * Lb) + ∑ _j : Fin m, P * Lb := by
        apply add_le_add
        · apply Finset.sum_le_sum
          intro j _
          gcongr
          exact hn j
        · apply Finset.sum_le_sum
          intro j _
          gcongr
          exact hQ j
      _ = _ := by simp only [labelb, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]; ring
  have ht : (dim : ℝ) + qlog + (p + 1) + 1 ≤ tb := by
    dsimp only [tb]
    gcongr
    exact hp.2
  have hg : (Cgrid : ℝ) + ((dim + 1 : ℕ) : ℝ) * qlog + (p + 1) + 4 ≤ gb := by
    dsimp only [gb]
    gcongr
    exact hp.2
  have hLbudget : L ≤ budget := by linarith
  have hmaskbudget : maskLog ≤ budget := by linarith
  have hlabelbudget : labelLog ≤ budget := by linarith
  refine ⟨by linarith, ⟨hL0, hLbudget⟩,
    ⟨hqlog0, ?_⟩, ⟨by positivity, ?_⟩,
    ⟨by dsimp only [maskLog]; positivity, hmaskbudget⟩,
    ⟨by dsimp only [labelLog]; positivity, hlabelbudget⟩,
    ⟨by positivity, by linarith⟩, ⟨by positivity, by linarith⟩, ?_⟩
  · dsimp only [tb] at htotal htb
    linarith [Nat.cast_nonneg (α := ℝ) dim]
  · dsimp only [tb] at htotal htb
    linarith [Nat.cast_nonneg (α := ℝ) dim, hp.2]
  · intro M period _ hM hperiod
    obtain ⟨hperiodBound, hmaskBound, hlabelBound⟩ :=
      canonicalPeriod_primitive_bounds A n O Q hM hperiod
    exact ⟨hperiodBound.trans (Real.exp_le_exp.mpr hLbudget),
      hmaskBound.trans (Real.exp_le_exp.mpr hmaskbudget),
      hlabelBound.trans (Real.exp_le_exp.mpr hlabelbudget)⟩

theorem exists_preparedModularCanonicalDetector_grid_parameters (m dim : ℕ) (A : ℝ≥0) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {nX : ℕ} {Pk Qstride p : ℝ},
      0 ≤ Pk → 0 ≤ Qstride → 0 ≤ p →
      let Q := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let tg := (dim : ℝ) + Q + (p + 1) + 1
      let pg := (C : ℝ) + ((dim + 1 : ℕ) : ℝ) * Q + (p + 1) + 4
      let δ := Real.exp (-(p + 1))
      0 < δ ∧ δ ≤ 1 ∧ δ⁻¹ ≤ Real.exp (p + 1) ∧ 0 ≤ tg ∧ 0 ≤ pg ∧
      ∃ T : ℕ, (T : ℝ) ≤ Real.exp tg ∧
      ∀ {M period : ℕ} (stride : Fin nX → ℕ),
        (M : ℝ) ≤ Real.exp Pk → 0 < period → period ≤ M ^ (m + 1) →
        (∀ i, 0 < stride i) → (∀ i, (stride i : ℝ) ≤ Real.exp Qstride) →
        let q := residueRefinedPeriod period stride
        (((dim + 1) * q : ℕ) : ℝ) / δ ≤ T ∧
        1 ≤ Real.exp pg ∧
        scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ Real.exp pg ∧
        scalarCubePrimitiveEnvelope (Fin dim) A 1 0 q ≤ Real.exp pg ∧
        ∀ {Y : Type*} (step : Y → ℕ),
          (∀ y, (step y : ℝ) ≤ 4 * Real.exp (p + 1)) →
          ∀ y, ((step y * q : ℕ) : ℝ) ≤ Real.exp pg := by
  obtain ⟨C, hC, hparameters⟩ := exists_uniform_slicedGridParameters dim A
  refine ⟨C, hC, ?_⟩
  intro nX Pk Qstride p hPk hQstride hp Q tg pg δ
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hF : 0 ≤ p + 1 := by positivity
  have hδ : 0 < δ := Real.exp_pos _
  have hδF : δ⁻¹ ≤ Real.exp (p + 1) := by
    simp only [δ, Real.exp_neg, inv_inv, le_refl]
  obtain ⟨T, hT, hgrid⟩ := hparameters hF hQ
  refine ⟨hδ, Real.exp_le_one_iff.mpr (by linarith), hδF,
    by dsimp only [tg]; positivity, by dsimp only [pg]; positivity, T, hT, ?_⟩
  intro M period stride hM hperiod hperiodBound hstride hstrideBound q
  have hperiodLog : (period : ℝ) ≤ Real.exp (((m + 1 : ℕ) : ℝ) * Pk) := by
    calc
      _ ≤ ((M ^ (m + 1) : ℕ) : ℝ) := Nat.cast_le.mpr hperiodBound
      _ = (M : ℝ) ^ (m + 1) := Nat.cast_pow _ _
      _ ≤ (Real.exp Pk) ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM _
      _ = _ := (Real.exp_nat_mul _ _).symm
  have hq : 0 < q := residueRefinedPeriod_pos hperiod stride hstride
  have hqQ : (q : ℝ) ≤ Real.exp Q := by
    simpa only [Fintype.card_fin] using residueRefinedPeriod_exp_bound period stride hperiodLog hstrideBound
  have hstepZero : ((0 : ℕ) : ℝ) ≤ 4 * Real.exp (p + 1) := by
    simpa only [Nat.cast_zero] using
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Real.exp_nonneg (p + 1))
  obtain ⟨hQT, hPg, hcP, hsP, _⟩ := hgrid (step := 0) hδ hδF hq hqQ hstepZero
  refine ⟨hQT, hPg, hcP, hsP, ?_⟩
  intro Y step hstep y
  exact (hgrid hδ hδF hq hqQ (hstep y)).2.2.2.2

theorem exists_preparedModularCanonicalDetector_common_grid_budget (m dim : ℕ) (Ag : ℝ≥0) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {nX : ℕ} {A : Type*} [Fintype A]
      (n : Fin m → ℕ) (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
      {P Pk Qstride p : ℝ}, 0 ≤ P → (nX : ℝ) ≤ P → Pk ∈ Set.Icc 0 P →
      Qstride ∈ Set.Icc 0 P → p ∈ Set.Icc 0 P →
      (Fintype.card A : ℝ) ≤ P → (∀ j, (n j : ℝ) ≤ P) →
      (∀ j, (Fintype.card (Q j) : ℝ) ≤ P) →
      let O := fun j : Fin m => (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type)
      let budget := (P + C) ^ C
      let δ := Real.exp (-(p + 1))
      P ≤ budget ∧ 0 < δ ∧ δ ≤ 1 ∧ δ⁻¹ ≤ Real.exp budget ∧
      ∃ T : ℕ, (T : ℝ) ≤ Real.exp budget ∧
      ∀ {M period : ℕ} [NeZero period] (stride : Fin nX → ℕ),
        (M : ℝ) ≤ Real.exp Pk → period ≤ M ^ (m + 1) →
        (∀ i, 0 < stride i) → (∀ i, (stride i : ℝ) ≤ Real.exp Qstride) →
        let modulus := residueRefinedPeriod period stride
        (period : ℝ) ≤ Real.exp budget ∧
        (layerKernelIndexBound m M : ℝ) ^ Fintype.card A * coefficientDeckPeriodCap O Q period ≤
          Real.exp budget ∧
        (Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, Q j → ZMod period)) : ℝ) ≤
          Real.exp budget ∧
        (((dim + 1) * modulus : ℕ) : ℝ) / δ ≤ T ∧
        1 ≤ Real.exp budget ∧
        scalarCubePrimitiveEnvelope Empty Ag 16 (128 * probabilityProfileLipschitz) 1 ≤ Real.exp budget ∧
        scalarCubePrimitiveEnvelope (Fin dim) Ag 1 0 modulus ≤ Real.exp budget ∧
        ∀ {Y : Type*} (step : Y → ℕ),
          (∀ y, (step y : ℝ) ≤ 4 * Real.exp (p + 1)) →
          ∀ y, ((step y * modulus : ℕ) : ℝ) ≤ Real.exp budget := by
  obtain ⟨Cgrid, _, hgrid⟩ := exists_preparedModularCanonicalDetector_grid_parameters m dim Ag
  obtain ⟨C, hC, hbudget⟩ := exists_preparedModularCanonicalDetector_period_budget m dim Cgrid
  refine ⟨C, hC, ?_⟩
  intro nX A _ n Q _ P Pk Qstride p hP hnX hPk hQstride hp hA hn hQ O budget δ
  obtain ⟨hPB, _, _, hF, _, _, htg, hpg, hperiodBounds⟩ :=
    hbudget n Q hP hnX hPk hQstride hp hA hn hQ
  obtain ⟨hδ, hδone, hδinv, _, _, T, hT, hgridAll⟩ := hgrid (nX := nX) hPk.1 hQstride.1 hp.1
  refine ⟨hPB, hδ, hδone, hδinv.trans (Real.exp_le_exp.mpr hF.2), T,
    hT.trans (Real.exp_le_exp.mpr htg.2), ?_⟩
  intro M period _ stride hM hperiod hstride hstrideBound modulus
  obtain ⟨hpBound, hmBound, hlBound⟩ := hperiodBounds hM hperiod
  obtain ⟨hQT, hPg, hcP, hsP, hstep⟩ :=
    hgridAll stride hM (NeZero.pos period) hperiod hstride hstrideBound
  have hgexp := Real.exp_le_exp.mpr hpg.2
  refine ⟨hpBound, hmBound, hlBound, hQT, hPg.trans hgexp,
    hcP.trans hgexp, hsP.trans hgexp, ?_⟩
  intro Y step hstepBound y
  exact (hstep step hstepBound y).trans hgexp

end Erdos3.VectorPolynomial

end

end OAI
