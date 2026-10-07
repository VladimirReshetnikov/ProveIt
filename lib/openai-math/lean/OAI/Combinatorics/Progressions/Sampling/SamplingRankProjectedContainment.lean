/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import OAI.Combinatorics.Progressions.Estimates.RationalApproximationScaling
import OAI.Combinatorics.Progressions.Estimates.VectorCoefficientScaling
import OAI.Combinatorics.Progressions.Lattices.RealSpanIntegerDefiningRows
import OAI.Combinatorics.Progressions.Polynomial.TranslationTopDegree

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def HasLayerSamplingRank {I J : Type*} [Fintype J]
    (h : ℕ) (T : I → ℝ) (R : ℝ) (W : Submodule ℝ (J → ℝ))
    (p : VectorPolynomial I ℝ (J → ℝ)) : Prop :=
  ∀ a : J → ℤ, (∀ j, |(a j : ℝ)| ≤ R) →
    (∃ w : W, (∑ j, (a j : ℝ) * w.val j) ≠ 0) →
    ¬ PolynomialRationalApproximation T R
      (MvPolynomial.homogeneousComponent h (VectorPolynomial.integerRowPolynomial a p))

theorem HasLayerSamplingRank.not_approximation {I J : Type*} [Fintype J]
    {h : ℕ} {T : I → ℝ} {R : ℝ} {W : Submodule ℝ (J → ℝ)}
    {p : VectorPolynomial I ℝ (J → ℝ)} (hrank : HasLayerSamplingRank h T R W p)
    (hp : VectorPolynomial.Homogeneous h p) (a : J → ℤ)
    (ha : ∀ j, |(a j : ℝ)| ≤ R) (hw : ∃ w : W, (∑ j, (a j : ℝ) * w.val j) ≠ 0) :
    ¬ PolynomialRationalApproximation T R (VectorPolynomial.integerRowPolynomial a p) := by
  have hn := hrank a ha hw
  rwa [MvPolynomial.homogeneousComponent_eq_self
    (VectorPolynomial.integerRowPolynomial_homogeneous a p hp)] at hn

end Erdos3

end

section

namespace Erdos3

theorem VectorPolynomial.integerRowPolynomial_homogeneousPart {I J : Type*} [Fintype J]
    (a : J → ℤ) (h : ℕ) (p : VectorPolynomial I ℝ (J → ℝ)) :
    VectorPolynomial.integerRowPolynomial a (VectorPolynomial.homogeneousPart h p) =
      MvPolynomial.homogeneousComponent h (VectorPolynomial.integerRowPolynomial a p) :=
  VectorPolynomial.coordinate_homogeneousPart _ h p

theorem hasLayerSamplingRank_homogeneousPart_iff {I J : Type*} [Fintype J]
    (h : ℕ) (T : I → ℝ) (R : ℝ) (W : Submodule ℝ (J → ℝ))
    (p : VectorPolynomial I ℝ (J → ℝ)) :
    HasLayerSamplingRank h T R W (VectorPolynomial.homogeneousPart h p) ↔
      HasLayerSamplingRank h T R W p := by
  unfold HasLayerSamplingRank
  simp only [VectorPolynomial.integerRowPolynomial_homogeneousPart,
    MvPolynomial.homogeneousComponent_eq_self (MvPolynomial.homogeneousComponent_isHomogeneous h _)]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct

variable {I J : Type*} [Fintype J]

noncomputable def samplingRankProjection (a : J → ℤ) (e : J → ℝ) :
    (J → ℝ) →ₗ[ℝ] (J → ℝ) :=
  LinearMap.id - (integerRowLinear a).smulRight e

@[simp] theorem samplingRankProjection_apply (a : J → ℤ) (e v : J → ℝ) :
    samplingRankProjection a e v = v - integerRowLinear a v • e := rfl

theorem samplingRankProjection_mem (a : J → ℤ) (e : J → ℝ)
    (W : Submodule ℝ (J → ℝ)) (he : e ∈ W) (hae : integerRowLinear a e = 1)
    {v : J → ℝ} (hv : v ∈ W) :
    samplingRankProjection a e v ∈ W ⊓ LinearMap.ker (integerRowLinear a) := by
  constructor
  · exact W.sub_mem hv (W.smul_mem _ he)
  · change integerRowLinear a (samplingRankProjection a e v) = 0
    rw [samplingRankProjection_apply, map_sub, map_smul, hae]
    simp

theorem samplingRankCut_decomposition (a : J → ℤ) (e : J → ℝ)
    (p : VectorPolynomial I ℝ (J → ℝ)) :
    p = map (samplingRankProjection a e) p + integerRowPolynomial a p ⊗ₜ[ℝ] e := by
  apply coefficients.injective
  ext α j
  simp only [map_add, coefficients_map, coefficients_tmul, Finsupp.add_apply,
    samplingRankProjection_apply, integerRowPolynomial_coeff, integerRowLinear_apply,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem samplingRankCut_finrank_lt (a : J → ℤ) (e : J → ℝ)
    (W : Submodule ℝ (J → ℝ)) (he : e ∈ W) (hae : integerRowLinear a e = 1) :
    Module.finrank ℝ ↥(W ⊓ LinearMap.ker (integerRowLinear a)) < Module.finrank ℝ W := by
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne inf_le_left ?_
  intro h
  have hem : e ∈ W ⊓ LinearMap.ker (integerRowLinear a) := by rw [h]; exact he
  have hz : integerRowLinear a e = 0 := hem.2
  linarith

theorem exists_samplingRankCut {h : ℕ} {T : I → ℝ} {R : ℝ}
    (W : Submodule ℝ (J → ℝ)) (p : VectorPolynomial I ℝ (J → ℝ))
    (hmem : ∀ α, coefficients p α ∈ W) (hdegree : DegreeLE (fun _ => 1) h p)
    (hfail : ¬ HasLayerSamplingRank h T R W p) :
    ∃ (a : J → ℤ) (e : J → ℝ) (q : VectorPolynomial I ℝ (J → ℝ)),
      (∀ j, |(a j : ℝ)| ≤ R) ∧ e ∈ W ∧ integerRowLinear a e = 1 ∧
      (∀ α, coefficients q α ∈ W ⊓ LinearMap.ker (integerRowLinear a)) ∧
      DegreeLE (fun _ => 1) h q ∧
      p = q + integerRowPolynomial a p ⊗ₜ[ℝ] e ∧
      Module.finrank ℝ ↥(W ⊓ LinearMap.ker (integerRowLinear a)) < Module.finrank ℝ W ∧
      PolynomialRationalApproximation T R
        (MvPolynomial.homogeneousComponent h (integerRowPolynomial a p)) := by
  classical
  simp only [HasLayerSamplingRank, not_forall, not_not] at hfail
  obtain ⟨a, ha, ⟨w, hw⟩, happrox⟩ := hfail
  have hw' : integerRowLinear a w.val ≠ 0 := by simpa only [integerRowLinear_apply] using hw
  let e : J → ℝ := (integerRowLinear a w.val)⁻¹ • w.val
  have he : e ∈ W := W.smul_mem _ w.property
  have hae : integerRowLinear a e = 1 := by
    dsimp only [e]
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hw']
  let q := map (samplingRankProjection a e) p
  refine ⟨a, e, q, ha, he, hae, ?_, hdegree.map _, samplingRankCut_decomposition a e p,
    samplingRankCut_finrank_lt a e W he hae, happrox⟩
  intro α
  rw [coefficients_map]
  exact samplingRankProjection_mem a e W he hae (hmem α)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem HasLayerSamplingRank.mono {I J : Type*} [Fintype J]
    {h : ℕ} {T : I → ℝ} {R S : ℝ} {W : Submodule ℝ (J → ℝ)}
    {P : VectorPolynomial I ℝ (J → ℝ)}
    (hrank : HasLayerSamplingRank h T S W P) (hRS : R ≤ S)
    (hT : ∀ i, 0 < T i) : HasLayerSamplingRank h T R W P := by
  intro a ha hw happ
  exact hrank a (fun j => (ha j).trans hRS) hw (happ.mono hRS hT)

end Erdos3

end

section

namespace Erdos3

theorem HasLayerSamplingRank.inv_nat_smul {I J : Type*} [Fintype J]
    {h : ℕ} {T : I → ℝ} {R : ℝ} (hR : 0 ≤ R)
    {W : Submodule ℝ (J → ℝ)} {p : VectorPolynomial I ℝ (J → ℝ)}
    (q : ℕ) (hq : 0 < q) (hrank : HasLayerSamplingRank h T ((q : ℝ) * R) W p) :
    HasLayerSamplingRank h T R W ((q : ℝ)⁻¹ • p) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  intro a ha hw happ
  have ha' : ∀ j, |(a j : ℝ)| ≤ (q : ℝ) * R := fun j => (ha j).trans (by nlinarith)
  apply hrank a ha' hw
  have hh := happ.nat_smul q hq
  simpa only [VectorPolynomial.integerRowPolynomial_smul, map_smul, smul_smul,
    mul_inv_cancel₀ hq0, one_smul] using hh

theorem HasLayerSamplingRank.div_nat {I J : Type*} [Fintype J]
    {h : ℕ} {T : I → ℝ} {R : ℝ} (hR : 0 ≤ R)
    {W : Submodule ℝ (J → ℝ)} {p : VectorPolynomial I ℝ (J → ℝ)}
    (hrank : HasLayerSamplingRank h T R W p) (q : ℕ) (hq : 0 < q) :
    HasLayerSamplingRank h T (R / q) W ((q : ℝ)⁻¹ • p) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hr : HasLayerSamplingRank h T ((q : ℝ) * (R / q)) W p := by
    simpa only [mul_div_cancel₀ R hq0] using hrank
  exact HasLayerSamplingRank.inv_nat_smul (div_nonneg hR (Nat.cast_nonneg q)) q hq hr

end Erdos3

end

section

namespace Erdos3

theorem hasLayerSamplingRank_translate_iff {X J : Type*} [Fintype J]
    (a : X → ℝ) (n : ℕ) (H : X → ℝ) (R : ℝ) (U : Submodule ℝ (J → ℝ))
    (p : VectorPolynomial X ℝ (J → ℝ)) (hp : VectorPolynomial.DegreeLE (1 : X → ℕ) n p) :
    HasLayerSamplingRank n H R U (VectorPolynomial.translate a p) ↔
      HasLayerSamplingRank n H R U p := by
  rw [← hasLayerSamplingRank_homogeneousPart_iff n H R U (VectorPolynomial.translate a p),
    VectorPolynomial.homogeneousPart_translate a p hp,
    hasLayerSamplingRank_homogeneousPart_iff]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix BigOperators

theorem exists_bounded_rational_unit_preimage {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι κ ℚ) (i : ι) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H)
    (hconsistent : ∃ x : κ → ℝ,
      Matrix.of (fun i j => (A i j : ℝ)) *ᵥ x = Pi.single i 1) :
    ∃ x : κ → ℚ, A *ᵥ x = Pi.single i 1 ∧
      ∀ j, RationalHeightLE (x j) (rationalKernelHeight (Fintype.card ι) H) := by
  classical
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section A hH hA
  have hSr := real_matrix_image_section A S hS
  obtain ⟨y, hy⟩ := hconsistent
  have hinv : Matrix.of (fun i j => (A i j : ℝ)) *ᵥ
      (Matrix.of (fun i j => (S i j : ℝ)) *ᵥ Pi.single i 1) = Pi.single i 1 := by
    rw [← hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hSr]
  refine ⟨fun j => S j i, ?_, fun j => hSH j i⟩
  ext k
  rw [Matrix.mulVec_single_one] at hinv
  have hk := congrFun hinv k
  simp only [Matrix.mulVec, dotProduct, Matrix.col_apply, Matrix.of_apply,
    Pi.single_apply] at hk ⊢
  split_ifs at hk ⊢ <;> exact_mod_cast hk

theorem exists_bounded_joint_rational_section {ι κ ρ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ρ]
    (B : Matrix ι κ ℚ) (A : Matrix ρ ι ℚ) (a : ι → ℚ)
    {H R : ℕ} (hH : 1 ≤ H) (hR : 1 ≤ R)
    (hB : ∀ i j, RationalHeightLE (B i j) H)
    (hA : ∀ i j, RationalHeightLE (A i j) R)
    (ha : ∀ i, RationalHeightLE (a i) R)
    (hconsistent : ∃ y : κ → ℝ,
      Matrix.of (fun i j => (A i j : ℝ)) *ᵥ
        (Matrix.of (fun i j => (B i j : ℝ)) *ᵥ y) = 0 ∧
      ∑ i, (a i : ℝ) * (Matrix.of (fun i j => (B i j : ℝ)) *ᵥ y) i ≠ 0) :
    let hSystem := (Fintype.card ι + 1) * (R * H) ^ Fintype.card ι
    let hSection := rationalKernelHeight (Fintype.card ρ + 1) hSystem
    ∃ z : κ → ℚ, A *ᵥ (B *ᵥ z) = 0 ∧
      (∑ i, a i * (B *ᵥ z) i) = 1 ∧
      (∀ j, RationalHeightLE (z j) hSection) ∧
      ∀ i, RationalHeightLE ((B *ᵥ z) i)
        ((Fintype.card κ + 1) * (H * hSection) ^ Fintype.card κ) := by
  classical
  intro hSystem hSection
  let C : Matrix (Option ρ) ι ℚ := Matrix.of (fun r i => r.elim (a i) (fun r => A r i))
  let M : Matrix (Option ρ) κ ℚ := C * B
  have hC : ∀ i j, RationalHeightLE (C i j) R := by
    intro i j
    cases i with
    | none => exact ha j
    | some i => exact hA i j
  have hM : ∀ i j, RationalHeightLE (M i j) hSystem :=
    rationalHeightLE_matrix_mul C B hC hB
  have hSystem1 : 1 ≤ hSystem := by
    dsimp [hSystem]
    exact Nat.mul_pos (Nat.succ_pos _) (pow_pos (Nat.mul_pos hR hH) _)
  have hMr : Matrix.of (fun i j => (M i j : ℝ)) =
      Matrix.of (fun i j => (C i j : ℝ)) * Matrix.of (fun i j => (B i j : ℝ)) := by
    ext i j
    simp [M, Matrix.mul_apply]
  have hunit : ∃ x : κ → ℝ, Matrix.of (fun i j => (M i j : ℝ)) *ᵥ x =
      Pi.single none 1 := by
    obtain ⟨y, hy, hay⟩ := hconsistent
    let t : ℝ := ∑ i, (a i : ℝ) * (Matrix.of (fun i j => (B i j : ℝ)) *ᵥ y) i
    refine ⟨t⁻¹ • y, ?_⟩
    rw [Matrix.mulVec_smul, hMr, ← Matrix.mulVec_mulVec]
    ext i
    cases i with
    | none =>
      change t⁻¹ * t = 1
      exact inv_mul_cancel₀ hay
    | some i =>
      have hi := congrFun hy i
      change t⁻¹ * (Matrix.of (fun i j => (A i j : ℝ)) *ᵥ
        (Matrix.of (fun i j => (B i j : ℝ)) *ᵥ y)) i = 0
      simp only [hi, Pi.zero_apply, mul_zero]
  obtain ⟨z, hz, hzH⟩ := exists_bounded_rational_unit_preimage M none hSystem1 hM hunit
  have hcz : C *ᵥ (B *ᵥ z) = Pi.single none 1 := by
    rw [Matrix.mulVec_mulVec]
    exact hz
  refine ⟨z, ?_, congrFun hcz none, ?_, ?_⟩
  · ext i
    exact congrFun hcz (some i)
  · simpa only [hSection, Fintype.card_option] using hzH
  · intro i
    exact rationalHeightLE_sum (fun j => B i j * z j)
      (fun j => (hB i j).mul (by simpa only [hSection, Fintype.card_option] using hzH j))

namespace VectorPolynomial

def jointRationalSpace {ι κ ρ : Type*} [Fintype ι] [Fintype κ]
    (B : Matrix ι κ ℚ) (A : Matrix ρ ι ℚ) : Submodule ℝ (ι → ℝ) :=
  LinearMap.range (Matrix.of (fun i j => (B i j : ℝ))).mulVecLin ⊓
    LinearMap.ker (Matrix.of (fun i j => (A i j : ℝ))).mulVecLin

def appendRankCutRow {ι ρ : Type*} (A : Matrix ρ ι ℚ) (a : ι → ℤ) :
    Matrix (Option ρ) ι ℚ :=
  Matrix.of (fun r i => r.elim (a i : ℚ) (fun r => A r i))

theorem jointRationalSpace_appendRankCutRow {ι κ ρ : Type*}
    [Fintype ι] [Fintype κ] (B : Matrix ι κ ℚ) (A : Matrix ρ ι ℚ) (a : ι → ℤ) :
    jointRationalSpace B (appendRankCutRow A a) =
      jointRationalSpace B A ⊓ LinearMap.ker (integerRowLinear a) := by
  ext v
  constructor
  · rintro ⟨hB, hA⟩
    change Matrix.of (fun r i => ((appendRankCutRow A a) r i : ℝ)) *ᵥ v = 0 at hA
    refine ⟨⟨hB, ?_⟩, ?_⟩
    · change Matrix.of (fun r i => (A r i : ℝ)) *ᵥ v = 0
      ext r
      exact congrFun hA (some r)
    · change integerRowLinear a v = 0
      have hn := congrFun hA none
      simpa only [appendRankCutRow, Matrix.mulVec, dotProduct, Matrix.of_apply,
        Option.elim_none, Rat.cast_intCast, Pi.zero_apply, integerRowLinear_apply] using hn
  · rintro ⟨⟨hB, hA⟩, ha⟩
    refine ⟨hB, ?_⟩
    change Matrix.of (fun r i => ((appendRankCutRow A a) r i : ℝ)) *ᵥ v = 0
    change Matrix.of (fun r i => (A r i : ℝ)) *ᵥ v = 0 at hA
    change integerRowLinear a v = 0 at ha
    ext r
    cases r with
    | none =>
      simpa only [appendRankCutRow, Matrix.mulVec, dotProduct, Matrix.of_apply,
        Option.elim_none, Rat.cast_intCast, Pi.zero_apply, integerRowLinear_apply] using ha
    | some r => exact congrFun hA r

theorem appendRankCutRow_height {ι ρ : Type*} (A : Matrix ρ ι ℚ) (a : ι → ℤ)
    {R : ℕ} (hR : 1 ≤ R) (hA : ∀ r i, RationalHeightLE (A r i) R)
    (ha : ∀ i, |(a i : ℝ)| ≤ R) :
    ∀ r i, RationalHeightLE (appendRankCutRow A a r i) R := by
  intro r i
  cases r with
  | none =>
    change RationalHeightLE (a i : ℚ) R
    have habs : (a i).natAbs ≤ R := by
      exact_mod_cast (show ((a i).natAbs : ℝ) ≤ R by
        simpa only [Nat.cast_natAbs, Int.cast_abs] using ha i)
    exact ⟨by simpa only [Rat.num_intCast] using habs, by simpa only [Rat.den_intCast] using hR⟩
  | some r => exact hA r i

theorem exists_bounded_joint_rational_direction {ι κ ρ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ρ]
    (B : Matrix ι κ ℚ) (A : Matrix ρ ι ℚ) (a : ι → ℤ)
    {H R : ℕ} (hH : 1 ≤ H) (hR : 1 ≤ R)
    (hB : ∀ i j, RationalHeightLE (B i j) H)
    (hA : ∀ i j, RationalHeightLE (A i j) R)
    (ha : ∀ i, |(a i : ℝ)| ≤ R)
    (hrow : ∃ w : jointRationalSpace B A, integerRowLinear a w.val ≠ 0) :
    let hSystem := (Fintype.card ι + 1) * (R * H) ^ Fintype.card ι
    let hSection := rationalKernelHeight (Fintype.card ρ + 1) hSystem
    ∃ e : ι → ℚ, (fun i => (e i : ℝ)) ∈ jointRationalSpace B A ∧
      integerRowLinear a (fun i => (e i : ℝ)) = 1 ∧
      ∀ i, RationalHeightLE (e i)
        ((Fintype.card κ + 1) * (H * hSection) ^ Fintype.card κ) := by
  classical
  intro hSystem hSection
  have haQ : ∀ i, RationalHeightLE (a i : ℚ) R := by
    intro i
    have habs : (a i).natAbs ≤ R := by
      exact_mod_cast (show ((a i).natAbs : ℝ) ≤ R by
        simpa only [Nat.cast_natAbs, Int.cast_abs] using ha i)
    exact ⟨by simpa only [Rat.num_intCast] using habs, by simpa only [Rat.den_intCast] using hR⟩
  have hconsistent : ∃ y : κ → ℝ,
      Matrix.of (fun i j => (A i j : ℝ)) *ᵥ
        (Matrix.of (fun i j => (B i j : ℝ)) *ᵥ y) = 0 ∧
      ∑ i, ((a i : ℚ) : ℝ) * (Matrix.of (fun i j => (B i j : ℝ)) *ᵥ y) i ≠ 0 := by
    obtain ⟨w, hw⟩ := hrow
    obtain ⟨⟨y, hy⟩, hAw⟩ := w.property
    change Matrix.of (fun i j => (B i j : ℝ)) *ᵥ y = w.val at hy
    refine ⟨y, ?_, ?_⟩
    · rw [hy]
      exact hAw
    · simpa only [Rat.cast_intCast, ← integerRowLinear_apply, hy] using hw
  obtain ⟨z, hAz, haz, hzH, heH⟩ :=
    exists_bounded_joint_rational_section B A (fun i => (a i : ℚ)) hH hR hB hA haQ hconsistent
  let e := B *ᵥ z
  have heq : (fun i => (e i : ℝ)) =
      Matrix.of (fun i j => (B i j : ℝ)) *ᵥ (fun j => (z j : ℝ)) := by
    ext i
    simp [e, Matrix.mulVec, dotProduct]
  refine ⟨e, ⟨?_, ?_⟩, ?_, heH⟩
  · exact ⟨fun j => (z j : ℝ), heq.symm⟩
  · change Matrix.of (fun i j => (A i j : ℝ)) *ᵥ (fun i => (e i : ℝ)) = 0
    ext i
    have hi := congrArg (fun v : ρ → ℚ => (v i : ℝ)) hAz
    simpa [e, Matrix.mulVec, dotProduct] using hi
  · have hi := congrArg (fun q : ℚ => (q : ℝ)) haz
    simpa [e, integerRowLinear_apply, Matrix.mulVec, dotProduct] using hi

open scoped TensorProduct

theorem exists_bounded_samplingRankCut {X ι κ ρ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ρ]
    (B : Matrix ι κ ℚ) (A : Matrix ρ ι ℚ)
    {H R h : ℕ} (hH : 1 ≤ H) (hR : 1 ≤ R)
    (hB : ∀ i j, RationalHeightLE (B i j) H)
    (hA : ∀ i j, RationalHeightLE (A i j) R)
    (T : X → ℝ) (p : VectorPolynomial X ℝ (ι → ℝ))
    (hmem : ∀ α, coefficients p α ∈ jointRationalSpace B A)
    (hdegree : DegreeLE (fun _ => 1) h p)
    (hfail : ¬ HasLayerSamplingRank h T R (jointRationalSpace B A) p) :
    let W := jointRationalSpace B A
    let hSystem := (Fintype.card ι + 1) * (R * H) ^ Fintype.card ι
    let hSection := rationalKernelHeight (Fintype.card ρ + 1) hSystem
    ∃ (a : ι → ℤ) (e : ι → ℚ) (q : VectorPolynomial X ℝ (ι → ℝ)),
      (∀ i, |(a i : ℝ)| ≤ R) ∧
      (fun i => (e i : ℝ)) ∈ W ∧ integerRowLinear a (fun i => (e i : ℝ)) = 1 ∧
      (∀ α, coefficients q α ∈ W ⊓ LinearMap.ker (integerRowLinear a)) ∧
      DegreeLE (fun _ => 1) h q ∧
      p = q + integerRowPolynomial a p ⊗ₜ[ℝ] (fun i => (e i : ℝ)) ∧
      Module.finrank ℝ ↥(W ⊓ LinearMap.ker (integerRowLinear a)) < Module.finrank ℝ W ∧
      PolynomialRationalApproximation T R
        (MvPolynomial.homogeneousComponent h (integerRowPolynomial a p)) ∧
      ∀ i, RationalHeightLE (e i)
        ((Fintype.card κ + 1) * (H * hSection) ^ Fintype.card κ) := by
  classical
  intro W hSystem hSection
  simp only [HasLayerSamplingRank, not_forall, not_not] at hfail
  obtain ⟨a, ha, hrow, happrox⟩ := hfail
  obtain ⟨e, he, hae, heH⟩ := exists_bounded_joint_rational_direction B A a hH hR hB hA ha
    (by simpa only [integerRowLinear_apply] using hrow)
  let q := map (samplingRankProjection a (fun i => (e i : ℝ))) p
  refine ⟨a, e, q, ha, he, hae, ?_, hdegree.map _,
    samplingRankCut_decomposition a _ p, samplingRankCut_finrank_lt a _ W he hae, happrox, heH⟩
  intro α
  rw [coefficients_map]
  exact samplingRankProjection_mem a _ W he hae (hmem α)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open scoped Matrix BigOperators

theorem exists_bounded_rational_unit_preimage_of_real_solution {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι κ ℚ) (i : ι) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H)
    (hconsistent : ∃ x : κ → ℝ,
      Matrix.of (fun i j => (A i j : ℝ)) *ᵥ x = Pi.single i 1) :
    ∃ x : κ → ℚ, A *ᵥ x = Pi.single i 1 ∧
      ∀ j, RationalHeightLE (x j) (rationalKernelHeight (Fintype.card ι) H) := by
  classical
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section A hH hA
  have hSr := real_matrix_image_section A S hS
  obtain ⟨y, hy⟩ := hconsistent
  have hinv : Matrix.of (fun i j => (A i j : ℝ)) *ᵥ
      (Matrix.of (fun i j => (S i j : ℝ)) *ᵥ Pi.single i 1) = Pi.single i 1 := by
    rw [← hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hSr]
  refine ⟨fun j => S j i, ?_, fun j => hSH j i⟩
  ext k
  rw [Matrix.mulVec_single_one] at hinv
  have hk := congrFun hinv k
  simp only [Matrix.mulVec, dotProduct, Matrix.col_apply, Matrix.of_apply,
    Pi.single_apply] at hk ⊢
  split_ifs at hk ⊢ <;> exact_mod_cast hk

end Erdos3

end

section

namespace Erdos3

theorem PolynomialRationalApproximation.homogeneous_decomposition
    {I : Type*} {T : I → ℝ} {R : ℝ} {h : ℕ} {P : MvPolynomial I ℝ}
    (happrox : PolynomialRationalApproximation T R P) (hP : P.IsHomogeneous h)
    (hT : ∀ i, 0 < T i) (hR : 0 ≤ R) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ R ∧
      ∃ (Q : MvPolynomial I ℤ) (E : MvPolynomial I ℝ),
        Q.IsHomogeneous h ∧ E.IsHomogeneous h ∧
        P = E + MvPolynomial.C (1 / (D : ℝ)) * MvPolynomial.map (Int.castRingHom ℝ) Q ∧
        ∀ α, |E.coeff α| ≤ R / monomialScale T α := by
  classical
  obtain ⟨D, hD, hDR, Q, hQ⟩ := happrox
  let Qtop := MvPolynomial.homogeneousComponent h Q
  let E := P - MvPolynomial.C (1 / (D : ℝ)) * MvPolynomial.map (Int.castRingHom ℝ) Qtop
  have hQtop : Qtop.IsHomogeneous h := MvPolynomial.homogeneousComponent_isHomogeneous _ _
  refine ⟨D, hD, hDR, Qtop, E, hQtop, hP.sub ((hQtop.map _).C_mul _),
    (sub_add_cancel P _).symm, ?_⟩
  intro α
  dsimp only [E]
  rw [MvPolynomial.coeff_sub, integerPolynomialQuotient_coeff]
  by_cases hα : α.degree = h
  · simpa only [Qtop, MvPolynomial.coeff_homogeneousComponent, ite_eq_left hα] using hQ α
  · rw [hP.coeff_eq_zero hα]
    simp only [Qtop, MvPolynomial.coeff_homogeneousComponent, ite_eq_right hα,
      Int.cast_zero, zero_div, sub_zero, abs_zero]
    exact div_nonneg hR (monomialScale_pos T hT α).le

namespace VectorPolynomial

open scoped TensorProduct

theorem integerRowPolynomial_totalDegree_le {I J : Type*} [Fintype J]
    (a : J → ℤ) {p : VectorPolynomial I ℝ (J → ℝ)} {h : ℕ}
    (hp : DegreeLE (fun _ => 1) h p) : (integerRowPolynomial a p).totalDegree ≤ h := by
  have hw : (integerRowPolynomial a p).weightedTotalDegree (1 : I → ℕ) ≤ h := by
    apply (scalar_weightedDegree_le_iff _ _ _).mpr
    intro α hα
    simp only [integerRowPolynomial, coeff_coordinate, hp α hα, map_zero]
  simpa only [MvPolynomial.weightedTotalDegree_one] using hw

theorem samplingRankCut_homogeneous_split {I J : Type*} [Fintype J]
    (a : J → ℤ) (e : J → ℝ) (p : VectorPolynomial I ℝ (J → ℝ))
    {h : ℕ} {T : I → ℝ} {R : ℝ}
    (hp : DegreeLE (fun _ => 1) (h + 1) p) (hT : ∀ i, 0 < T i) (hR : 0 ≤ R)
    (happrox : PolynomialRationalApproximation T R
      (MvPolynomial.homogeneousComponent (h + 1) (integerRowPolynomial a p))) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ R ∧
      ∃ (Q : MvPolynomial I ℤ) (E l : MvPolynomial I ℝ),
        Q.IsHomogeneous (h + 1) ∧ E.IsHomogeneous (h + 1) ∧ l.totalDegree ≤ h ∧
        (∀ α, |E.coeff α| ≤ R / monomialScale T α) ∧
        p = map (samplingRankProjection a e) p + E ⊗ₜ[ℝ] e +
          (MvPolynomial.C (1 / (D : ℝ)) * MvPolynomial.map (Int.castRingHom ℝ) Q) ⊗ₜ[ℝ] e +
          l ⊗ₜ[ℝ] e := by
  classical
  obtain ⟨D, hD, hDR, Q, E, hQ, hE, htop, hcoeff⟩ :=
    happrox.homogeneous_decomposition (MvPolynomial.homogeneousComponent_isHomogeneous _ _) hT hR
  let l := integerRowPolynomial a (p - homogeneousPart (h + 1) p)
  have hl : l.totalDegree ≤ h :=
    integerRowPolynomial_totalDegree_le a (sub_homogeneousPart_degreeLE hp)
  have hrow : integerRowPolynomial a p =
      MvPolynomial.homogeneousComponent (h + 1) (integerRowPolynomial a p) + l := by
    ext α
    simp only [l, integerRowPolynomial, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      MvPolynomial.coeff_homogeneousComponent, coeff_coordinate, map_sub,
      Finsupp.sub_apply, coefficients_homogeneousPart]
    split_ifs <;> simp
  refine ⟨D, hD, hDR, Q, E, l, hQ, hE, hl, hcoeff, ?_⟩
  calc
    p = map (samplingRankProjection a e) p + integerRowPolynomial a p ⊗ₜ[ℝ] e :=
      samplingRankCut_decomposition a e p
    _ = _ := by
      rw [hrow, htop]
      simp only [TensorProduct.add_tmul]
      abel

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

open VectorPolynomial

theorem integerRowPolynomial_coefficientGrid {σ J : Type*} [Fintype J]
    (a : J → ℤ) (Q : VectorPolynomial σ ℝ (J → ℝ)) (q : ℕ)
    (hQ : ∀ α, coefficients Q α ∈ realDenominatorGrid q) :
    realPolynomialCoefficientGrid q (integerRowPolynomial a Q) := by
  classical
  have hz : ∀ α, ∃ z : J → ℤ, ∀ j, (z j : ℝ) = (q : ℝ) * coefficients Q α j := by
    intro α
    obtain ⟨z, hz⟩ := hQ α
    exact ⟨z, fun j => congrFun hz j⟩
  choose z hz using hz
  refine ⟨fun α => ∑ j, a j * z α j, funext fun α => ?_⟩
  change ((∑ j, a j * z α j : ℤ) : ℝ) = (q : ℝ) * (integerRowPolynomial a Q).coeff α
  simp only [Int.cast_sum, Int.cast_mul, integerRowPolynomial_coeff, Finset.mul_sum, hz]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem integerRowPolynomial_homogeneous_approximation_of_decomposition
    {σ J : Type*} [Fintype J] (h : ℕ) (T : σ → ℝ) (R S b : ℝ)
    (a : J → ℤ) (A E P Q : VectorPolynomial σ ℝ (J → ℝ))
    (q : ℕ) (hq : 0 < q) (hqR : (q : ℝ) ≤ R)
    (hT : ∀ i, 0 < T i) (hb : 0 ≤ b)
    (ha : ∀ j, |(a j : ℝ)| ≤ b)
    (hcost : (Fintype.card J : ℝ) * b * S ≤ R)
    (hA : A = E + P + Q)
    (hE : ∀ α j, |coefficients E α j| ≤ S / monomialScale T α)
    (hP : ∀ α, integerRowLinear a (coefficients P α) = 0)
    (hQ : ∀ α, coefficients Q α ∈ realDenominatorGrid q) :
    PolynomialRationalApproximation T R
      (MvPolynomial.homogeneousComponent h (integerRowPolynomial a A)) := by
  classical
  have hgrid := integerRowPolynomial_coefficientGrid a Q q hQ
  obtain ⟨Z, hZ⟩ := (realPolynomialCoefficientGrid_iff q _).mp hgrid
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hZcoeff (α : σ →₀ ℕ) :
      ((Z.coeff α : ℤ) : ℝ) / q = (integerRowPolynomial a Q).coeff α := by
    have hz := congrArg (fun polynomial : MvPolynomial σ ℝ => polynomial.coeff α) hZ
    simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul] at hz
    change ((Z.coeff α : ℤ) : ℝ) = (q : ℝ) * (integerRowPolynomial a Q).coeff α at hz
    rw [hz, mul_div_cancel_left₀ _ hq0]
  have hR : 0 ≤ R := (Nat.cast_nonneg q).trans hqR
  refine ⟨q, hq, hqR, MvPolynomial.homogeneousComponent h Z, ?_⟩
  intro α
  by_cases hα : α.degree = h
  · simp only [MvPolynomial.coeff_homogeneousComponent, ite_eq_left hα, hZcoeff]
    have heq : (integerRowPolynomial a A).coeff α - (integerRowPolynomial a Q).coeff α =
        ∑ j, (a j : ℝ) * coefficients E α j := by
      rw [hA]
      simp only [integerRowPolynomial_coeff, map_add, Finsupp.add_apply, Pi.add_apply,
        mul_add, Finset.sum_add_distrib]
      have hz := hP α
      rw [integerRowLinear_apply] at hz
      rw [hz]
      ring
    rw [heq]
    calc
      _ ≤ ∑ j, |(a j : ℝ) * coefficients E α j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : J, b * (S / monomialScale T α) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (ha j) (hE α j) (abs_nonneg _) hb
      _ = ((Fintype.card J : ℝ) * b * S) / monomialScale T α := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
      _ ≤ R / monomialScale T α :=
        div_le_div_of_nonneg_right hcost (monomialScale_pos T hT α).le
  · simp only [MvPolynomial.coeff_homogeneousComponent, ite_eq_right hα, Int.cast_zero,
      zero_div, sub_zero, abs_zero]
    exact div_nonneg hR (monomialScale_pos T hT α).le

theorem vectorPolynomial_coefficientGrid_of_coordinateGrids {σ J : Type*}
    (Q : VectorPolynomial σ ℝ (J → ℝ)) (q : ℕ)
    (hQ : ∀ j, realPolynomialCoefficientGrid q
      (coordinate (LinearMap.proj j : (J → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom Q)) :
    ∀ α, coefficients Q α ∈ realDenominatorGrid q := by
  classical
  choose z hz using hQ
  intro α
  refine ⟨fun j => z j α, funext fun j => ?_⟩
  have hj := congrFun (hz j) α
  simpa only [Pi.smul_apply, smul_eq_mul, coeff_coordinate,
    LinearMap.toAddMonoidHom_coe, LinearMap.proj_apply] using hj

theorem samplingRank_le_real_column_span_of_decomposition
    {σ J L : Type*} [Fintype J] [Fintype L]
    (B : Matrix J L ℚ) {H : ℕ} (hH : 1 ≤ H)
    (hB : ∀ j i, RationalHeightLE (B j i) H)
    (h : ℕ) (T : σ → ℝ) (R S : ℝ) (W : Submodule ℝ (J → ℝ))
    (A E P Q : VectorPolynomial σ ℝ (J → ℝ))
    (q : ℕ) (hq : 0 < q) (hT : ∀ i, 0 < T i)
    (hrank : HasLayerSamplingRank h T R W A)
    (hA : A = E + P + Q)
    (hE : ∀ α j, |coefficients E α j| ≤ S / monomialScale T α)
    (hP : ∀ α, coefficients P α ∈ Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ))))
    (hQ : ∀ α, coefficients Q α ∈ realDenominatorGrid q)
    (hqR : (q : ℝ) ≤ R)
    (hrowR : (realSpanIntegerRowBound (Fintype.card L) (Fintype.card J) H : ℝ) ≤ R)
    (hcost : (Fintype.card J : ℝ) *
      (realSpanIntegerRowBound (Fintype.card L) (Fintype.card J) H : ℝ) * S ≤ R) :
    W ≤ Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ))) := by
  classical
  obtain ⟨C, hC, hker⟩ := exists_real_span_integer_defining_matrix B hH hB
  intro x hx
  apply (real_column_span_mem_iff B x).mpr
  rw [← hker]
  change (fun i j => (C i j : ℝ)) *ᵥ x = 0
  ext i
  by_contra hix
  have hkill (α : σ →₀ ℕ) : integerRowLinear (C i) (coefficients P α) = 0 := by
    have hp : coefficients P α ∈ LinearMap.ker
        (Matrix.mulVecLin (fun i j => (C i j : ℝ))) := by
      rw [hker]
      exact (real_column_span_mem_iff B _).mp (hP α)
    have hh := congrFun hp i
    change (∑ j, (C i j : ℝ) * coefficients P α j) = 0 at hh
    simpa only [integerRowLinear_apply] using hh
  apply hrank (C i) (fun j => (hC i j).trans hrowR) ⟨⟨x, hx⟩, hix⟩
  exact integerRowPolynomial_homogeneous_approximation_of_decomposition h T R S
    (realSpanIntegerRowBound (Fintype.card L) (Fintype.card J) H : ℝ)
    (C i) A E P Q q hq hqR hT (Nat.cast_nonneg _) (hC i) hcost hA hE hkill hQ

end Erdos3

end

end OAI
