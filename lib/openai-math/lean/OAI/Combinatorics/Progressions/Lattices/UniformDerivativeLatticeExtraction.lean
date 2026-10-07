import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import OAI.Combinatorics.Progressions.Estimates.DerivativeHorizontalLifts

namespace OAI

section

namespace Erdos3

theorem derivative_covolume_budget_le_exp (d n : ℕ) (R δ p : ℝ)
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hn : (n : ℝ) ≤ p)
    (hR0 : 0 ≤ R) (hR : R ≤ Real.exp p) (hδ : 0 < δ)
    (hδinv : δ⁻¹ ≤ Real.exp p) :
    (((d : ℝ) + 2) * ((n : ℝ) * R)) ^ d / δ ≤ Real.exp (3 * p ^ 2 + 2 * p) := by
  have hd2 : (d : ℝ) + 2 ≤ Real.exp (p + 1) := by
    exact (by linarith : (d : ℝ) + 2 ≤ (p + 1) + 1).trans (Real.add_one_le_exp (p + 1))
  have hnexp : (n : ℝ) ≤ Real.exp p :=
    hn.trans ((show p ≤ p + 1 by linarith).trans (Real.add_one_le_exp p))
  have hbase : ((d : ℝ) + 2) * ((n : ℝ) * R) ≤ Real.exp (3 * p + 1) := by
    calc
      _ ≤ Real.exp (p + 1) * (Real.exp p * Real.exp p) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc
    _ ≤ Real.exp (3 * p + 1) ^ d * Real.exp p := by
      rw [div_eq_mul_inv]
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) hbase d) hδinv
        (inv_nonneg.mpr hδ.le) (by positivity)
    _ = Real.exp ((d : ℝ) * (3 * p + 1) + p) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp (3 * p ^ 2 + 2 * p) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hd (by positivity : 0 ≤ 3 * p + 1)]

theorem derivative_extended_budget_le_exp (k l : ℕ) (C p : ℝ)
    (hp : 0 ≤ p) (hk : (k : ℝ) ≤ p) (hl : (l : ℝ) ≤ Real.exp p)
    (hC : C ≤ Real.exp (3 * p ^ 2 + 2 * p)) :
    C * (l : ℝ) ^ k ≤ Real.exp (4 * p ^ 2 + 2 * p) := by
  calc
    _ ≤ Real.exp (3 * p ^ 2 + 2 * p) * Real.exp p ^ k := by
      exact mul_le_mul hC (pow_le_pow_left₀ (Nat.cast_nonneg l) hl k)
        (pow_nonneg (Nat.cast_nonneg l) k) (Real.exp_nonneg _)
    _ = Real.exp (3 * p ^ 2 + 2 * p + (k : ℝ) * p) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp (4 * p ^ 2 + 2 * p) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hk hp]

theorem derivative_output_exponent_le {p : ℝ} (hp : 0 ≤ p) :
    4 * p ^ 2 + 4 * p + 1 ≤ (p + 2) ^ 3 := by
  nlinarith [pow_nonneg hp 3]

theorem derivative_output_budgets_le_exp (n k l : ℕ) (B p : ℝ)
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) (hk : (k : ℝ) ≤ p)
    (hl : (l : ℝ) ≤ Real.exp p) (hB : B ≤ Real.exp (4 * p ^ 2 + 2 * p)) :
    B ≤ Real.exp ((p + 2) ^ 3) ∧
      (n : ℝ) * k * B ≤ Real.exp ((p + 2) ^ 3) ∧
      (l : ℝ) * B ≤ Real.exp ((p + 2) ^ 3) ∧
      (Nat.ceil B : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
  have hne : (n : ℝ) ≤ Real.exp p :=
    hn.trans ((show p ≤ p + 1 by linarith).trans (Real.add_one_le_exp p))
  have hke : (k : ℝ) ≤ Real.exp p :=
    hk.trans ((show p ≤ p + 1 by linarith).trans (Real.add_one_le_exp p))
  have hpoly := derivative_output_exponent_le hp
  have h0 : 4 * p ^ 2 + 2 * p ≤ (p + 2) ^ 3 := by linarith
  have h1 : 4 * p ^ 2 + 3 * p ≤ (p + 2) ^ 3 := by linarith
  have h2 : 4 * p ^ 2 + 4 * p ≤ (p + 2) ^ 3 := by linarith
  have h3 : 4 * p ^ 2 + 2 * p + 1 ≤ (p + 2) ^ 3 := by linarith
  refine ⟨hB.trans (Real.exp_le_exp.mpr h0), ?_, ?_, ?_⟩
  · calc
      _ ≤ (n : ℝ) * k * Real.exp (4 * p ^ 2 + 2 * p) := by gcongr
      _ ≤ Real.exp p * Real.exp p * Real.exp (4 * p ^ 2 + 2 * p) := by gcongr
      _ = Real.exp (4 * p ^ 2 + 4 * p) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr h2
  · calc
      _ ≤ (l : ℝ) * Real.exp (4 * p ^ 2 + 2 * p) := by gcongr
      _ ≤ Real.exp p * Real.exp (4 * p ^ 2 + 2 * p) := by gcongr
      _ = Real.exp (4 * p ^ 2 + 3 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr h1
  · calc
      (Nat.ceil B : ℝ) ≤ Nat.ceil (Real.exp (4 * p ^ 2 + 2 * p)) := by
        exact_mod_cast Nat.ceil_mono hB
      _ ≤ Real.exp (4 * p ^ 2 + 2 * p + 1) := ceil_exp_le_exp_add_one (by positivity)
      _ ≤ _ := Real.exp_le_exp.mpr h3

theorem derivative_projection_budget_le_exp (n : ℕ) (R δ p : ℝ)
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) (hR0 : 0 ≤ R) (hR : R ≤ Real.exp p)
    (hδ : 0 < δ) (hδinv : δ⁻¹ ≤ Real.exp p) :
    (3 * R) ^ (n - 1) / δ ≤ Real.exp ((p + 2) ^ 3) := by
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hbase : 3 * R ≤ Real.exp (p + 2) := by
    calc
      _ ≤ Real.exp 2 * Real.exp p := mul_le_mul hthree hR hR0 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hn' : ((n - 1 : ℕ) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (Nat.sub_le n 1)).trans hn
  calc
    _ ≤ Real.exp (p + 2) ^ (n - 1) * Real.exp p := by
      rw [div_eq_mul_inv]
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) hbase _) hδinv
        (inv_nonneg.mpr hδ.le) (by positivity)
    _ = Real.exp (((n - 1 : ℕ) : ℝ) * (p + 2) + p) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp (p ^ 2 + 3 * p) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hn' (by positivity : 0 ≤ p + 2)]
    _ ≤ Real.exp ((p + 2) ^ 3) := by
      apply Real.exp_le_exp.mpr
      nlinarith [derivative_output_exponent_le hp, sq_nonneg p]

end Erdos3

end

section

namespace Erdos3

theorem lattice_subspace_budgets_le_exp
    {σ : Type*} [Fintype σ] {m : ℕ}
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ Fin m))) (V : Submodule ℝ Z)
    (l : ℕ) (R δ p : ℝ) (hp : 0 ≤ p)
    (hdim : ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) ≤ p)
    (hl : (l : ℝ) ≤ Real.exp p) (hR0 : 0 ≤ R) (hR : R ≤ Real.exp p)
    (hδ : 0 < δ) (hδinv : δ⁻¹ ≤ Real.exp p) :
    let n := Fintype.card σ + Fintype.card (Fin m)
    let d := Module.finrank ℝ Z
    let k := Module.finrank ℝ V
    let C := (((d : ℝ) + 2) * ((n : ℝ) * R)) ^ d / δ
    let B := C * (l : ℝ) ^ k
    C * (l : ℝ) ^ m ≤ Real.exp ((p + 2) ^ 3) ∧
      B ≤ Real.exp ((p + 2) ^ 3) ∧
      (n : ℝ) * k * B ≤ Real.exp ((p + 2) ^ 3) ∧
      (l : ℝ) * B ≤ Real.exp ((p + 2) ^ 3) ∧
      (Nat.ceil B : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
  let n := Fintype.card σ + Fintype.card (Fin m)
  let d := Module.finrank ℝ Z
  let k := Module.finrank ℝ V
  let C := (((d : ℝ) + 2) * ((n : ℝ) * R)) ^ d / δ
  let B := C * (l : ℝ) ^ k
  have hdn : d ≤ n := by
    simpa only [finrank_euclideanSpace, Fintype.card_sum] using Z.finrank_le
  have hdp : (d : ℝ) ≤ p := (Nat.cast_le.mpr hdn).trans hdim
  have hkp : (k : ℝ) ≤ p := (Nat.cast_le.mpr V.finrank_le).trans hdp
  have hmp : (m : ℝ) ≤ p := by
    have hmn : m ≤ n := by simp [n]
    exact (Nat.cast_le.mpr hmn).trans hdim
  have hC : C ≤ Real.exp (3 * p ^ 2 + 2 * p) :=
    derivative_covolume_budget_le_exp d n R δ p hp hdp hdim hR0 hR hδ hδinv
  have hB : B ≤ Real.exp (4 * p ^ 2 + 2 * p) :=
    derivative_extended_budget_le_exp k l C p hp hkp hl hC
  have hthreshold : C * (l : ℝ) ^ m ≤ Real.exp ((p + 2) ^ 3) := by
    apply (derivative_extended_budget_le_exp m l C p hp hmp hl hC).trans
    apply Real.exp_le_exp.mpr
    have he := derivative_output_exponent_le hp
    linarith
  exact ⟨hthreshold, derivative_output_budgets_le_exp n k l B p hp hdim hkp hl hB⟩

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_lattice_extraction
    {σ : Type*} [Fintype σ] [DecidableEq σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R δ : ℝ) (hR : 1 ≤ R) (hδ : 0 < δ)
    (H : Finset (σ → ℤ)) (r : (σ → ℤ) → Fin m → ℝ)
    (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (hlarge : ∀ i, (3 * R) ^ (Fintype.card σ - 1) < δ * T i)
    (a : ℕ) (ha : a ≤ m) (Tmin : ℝ)
    (hscalehor : ∀ j, j.val < a → scale j = 1)
    (hblock : ∀ i j, i.val < a → j.val < a →
      (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (hfar : ∀ i, a ≤ i.val → Tmin ≤ scale i) :
    let hT0 : ∀ i, T i ≠ 0 := fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne'
    let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
    let ρ := ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) * R
    let Λ := euclideanDerivativeLattice T hT0 scale hs0 Y A l hl
    let Z := shortVectorSpan Λ ρ
    let π := (euclideanDerivativeShiftMap T hT0).comp Z.subtype
    let V := LinearMap.ker π
    let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
    let k := Module.finrank ℝ V
    let C := (((Module.finrank ℝ Z : ℝ) + 2) * ρ) ^ Module.finrank ℝ Z / δ
    let B := C * (l : ℝ) ^ k
    let N := (Fintype.card (σ ⊕ Fin m) : ℝ) * k * B
    C * (l : ℝ) ^ m < Tmin →
      ∃ lifts : RationalHorizontalLift k P ha A scale N (Nat.ceil B),
        ∃ I : ℕ, 0 < I ∧ (I : ℝ) ≤ B ∧
          ∀ i, ∃ (s r' : Fin m → ℝ) (q : LinearMap.range P),
            Y (Pi.basisFun ℝ σ i) = s + A r' + lifts.geometricLift q ∧
            r' ∈ realDenominatorGrid (l * I) ∧
            ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * s j)‖ ≤ B / T i := by
  let hT0 : ∀ i, T i ≠ 0 := fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne'
  let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
  let ρ := ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) * R
  let Λ := euclideanDerivativeLattice T hT0 scale hs0 Y A l hl
  let Z := shortVectorSpan Λ ρ
  let π := (euclideanDerivativeShiftMap T hT0).comp Z.subtype
  let V := LinearMap.ker π
  let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
  let k := Module.finrank ℝ V
  let C := (((Module.finrank ℝ Z : ℝ) + 2) * ρ) ^ Module.finrank ℝ Z / δ
  let B := C * (l : ℝ) ^ k
  let N := (Fintype.card (σ ⊕ Fin m) : ℝ) * k * B
  let I := (latticeImage (shortVectorLattice Λ ρ) π).toAddSubgroup.relIndex
    integerCoordinateLattice.toAddSubgroup
  change C * (l : ℝ) ^ m < Tmin →
    ∃ lifts : RationalHorizontalLift k P ha A scale N (Nat.ceil B),
      ∃ I : ℕ, 0 < I ∧ (I : ℝ) ≤ B ∧
        ∀ i, ∃ (s r' : Fin m → ℝ) (q : LinearMap.range P),
          Y (Pi.basisFun ℝ σ i) = s + A r' + lifts.geometricLift q ∧
          r' ∈ realDenominatorGrid (l * I) ∧
          ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * s j)‖ ≤ B / T i
  intro hvertical
  obtain ⟨hI, G, hG, _, hcov, hIB, hGB⟩ := euclideanDerivative_index_graph_bounds
    T hT scale hscale Y A hA hdiag l hl R δ hR hδ H r hr hnorm hdense hlarge
  obtain ⟨lifts, hrecovers⟩ := euclideanDerivative_horizontal_lifts T hT0 scale hscale
    Y A hA hdiag l hl ρ a ha Tmin C hscalehor hblock hfar hvertical hcov
  refine ⟨lifts, I, hI, hIB, ?_⟩
  have hGbasis (i) : ‖G (Pi.basisFun ℝ σ i)‖ ≤ B :=
    (euclidean_section_basis_norm_le_gram_sqrt Z G hG i).trans hGB
  have hI_lifts (i) : ∃ v : Z, v.val ∈ Λ ∧
      euclideanDerivativeShiftMap T hT0 v.val = (I : ℝ) • Pi.basisFun ℝ σ i := by
    obtain ⟨v, hv, hπv⟩ := latticeImage_basis_lifts (shortVectorLattice Λ ρ) π i
    exact ⟨v, hv, hπv⟩
  exact indexed_derivative_decomposition (σ := σ) (m := m) (a := a) (k := k)
    T hT0 (fun i => lt_of_lt_of_le zero_lt_one (hT i)) scale hs0 Y A l hl Z ha N B
    (Nat.ceil B) lifts hrecovers G hG hGbasis I hI hI_lifts

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_uniform_lattice_extraction
    {σ : Type*} [Fintype σ] [DecidableEq σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R δ : ℝ) (hR : 1 ≤ R) (hδ : 0 < δ)
    (H : Finset (σ → ℤ)) (r : (σ → ℤ) → Fin m → ℝ)
    (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (a : ℕ) (ha : a ≤ m) (Tmin : ℝ)
    (hscalehor : ∀ j, j.val < a → scale j = 1)
    (hblock : ∀ i j, i.val < a → j.val < a →
      (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (hfar : ∀ i, a ≤ i.val → Tmin ≤ scale i)
    (p : ℝ) (hp : 0 ≤ p)
    (hdim : ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) ≤ p)
    (hlcap : (l : ℝ) ≤ Real.exp p) (hRcap : R ≤ Real.exp p)
    (hδcap : δ⁻¹ ≤ Real.exp p)
    (hmin : Real.exp ((p + 2) ^ 3) < Tmin) (hside : ∀ i, Tmin ≤ T i) :
    let hT0 : ∀ i, T i ≠ 0 := fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne'
    let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
    let ρ := ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) * R
    let Λ := euclideanDerivativeLattice T hT0 scale hs0 Y A l hl
    let Z := shortVectorSpan Λ ρ
    let π := (euclideanDerivativeShiftMap T hT0).comp Z.subtype
    let V := LinearMap.ker π
    let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
    let k := Module.finrank ℝ V
    let C := (((Module.finrank ℝ Z : ℝ) + 2) * ρ) ^ Module.finrank ℝ Z / δ
    let B := C * (l : ℝ) ^ k
    let N := (Fintype.card (σ ⊕ Fin m) : ℝ) * k * B
    let E := Real.exp ((p + 2) ^ 3)
    ∃ lifts : RationalHorizontalLift k P ha A scale N (Nat.ceil B),
      N ≤ E ∧ (Nat.ceil B : ℝ) ≤ E ∧
        ∃ I : ℕ, 0 < I ∧ ((l * I : ℕ) : ℝ) ≤ E ∧
          ∀ i, ∃ (s r' : Fin m → ℝ) (q : LinearMap.range P),
            Y (Pi.basisFun ℝ σ i) = s + A r' + lifts.geometricLift q ∧
            r' ∈ realDenominatorGrid (l * I) ∧
            ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * s j)‖ ≤ E / T i := by
  let hT0 : ∀ i, T i ≠ 0 := fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne'
  let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
  let ρ := ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) * R
  let Λ := euclideanDerivativeLattice T hT0 scale hs0 Y A l hl
  let Z := shortVectorSpan Λ ρ
  let π := (euclideanDerivativeShiftMap T hT0).comp Z.subtype
  let V := LinearMap.ker π
  let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
  let k := Module.finrank ℝ V
  let C := (((Module.finrank ℝ Z : ℝ) + 2) * ρ) ^ Module.finrank ℝ Z / δ
  let B := C * (l : ℝ) ^ k
  let N := (Fintype.card (σ ⊕ Fin m) : ℝ) * k * B
  let E := Real.exp ((p + 2) ^ 3)
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  obtain ⟨hthreshold, hBE, hNE, hlBE, hheight⟩ :=
    lattice_subspace_budgets_le_exp Z V l R δ p hp hdim hlcap hR0 hRcap hδ hδcap
  have hN : N ≤ E := by
    simpa only [N, Fintype.card_sum] using hNE
  have hσ : (Fintype.card σ : ℝ) ≤ p := by
    have hd : (Fintype.card σ : ℝ) + Fintype.card (Fin m) ≤ p := by exact_mod_cast hdim
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (Fin m))]
  have hprojection := derivative_projection_budget_le_exp (Fintype.card σ) R δ p
    hp hσ hR0 hRcap hδ hδcap
  have hlarge : ∀ i, (3 * R) ^ (Fintype.card σ - 1) < δ * T i := by
    intro i
    have hi := (div_lt_iff₀ hδ).mp (hprojection.trans_lt (hmin.trans_le (hside i)))
    simpa only [mul_comm] using hi
  have hvertical : C * (l : ℝ) ^ m < Tmin := hthreshold.trans_lt hmin
  obtain ⟨lifts, I, hI, hIB, hdecomp⟩ := euclideanDerivative_lattice_extraction
    T hT scale hscale Y A hA hdiag l hl R δ hR hδ H r hr hnorm hdense hlarge
    a ha Tmin hscalehor hblock hfar hvertical
  refine ⟨lifts, hN, hheight, I, hI, ?_, ?_⟩
  · rw [Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_left hIB (Nat.cast_nonneg l)).trans hlBE
  · intro i
    obtain ⟨s, r', q, heq, hr', hs⟩ := hdecomp i
    refine ⟨s, r', q, heq, hr', ?_⟩
    exact hs.trans (div_le_div_of_nonneg_right hBE (zero_le_one.trans (hT i)))

end Erdos3

end

end OAI
