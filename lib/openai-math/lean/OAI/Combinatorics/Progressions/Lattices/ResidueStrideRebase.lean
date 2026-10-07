import OAI.Combinatorics.Progressions.Estimates.AuxiliaryStrideGeometry
import OAI.Combinatorics.Progressions.Nilpotent.NiltestAffineProjection

namespace OAI

section

namespace Erdos3

theorem residueTransitionNumerator_pos {M₀ M₁ : ℕ} (hM₁ : 0 < M₁) (hdiv : M₀ ∣ M₁) :
    0 < M₁ / M₀ := by
  apply Nat.pos_of_ne_zero
  intro hz
  have heq := Nat.mul_div_cancel' hdiv
  rw [hz, mul_zero] at heq
  exact hM₁.ne' heq.symm

theorem residueTransition_scale {M₀ M₁ d : ℕ} (hdiv : M₀ ∣ M₁) (hd : 0 < d) :
    ((M₀ : ℚ) * d) * (((M₁ / M₀ : ℕ) : ℚ) / d) = M₁ := by
  have heq : (M₀ : ℚ) * (M₁ / M₀ : ℕ) = M₁ := by
    exact_mod_cast Nat.mul_div_cancel' hdiv
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  calc
    _ = (M₀ : ℚ) * (M₁ / M₀ : ℕ) := by
      field_simp [hdq]
    _ = M₁ := heq

theorem residueTransition_shift {M₀ d : ℕ} (hM₀ : 0 < M₀) (hd : 0 < d) (a₀ a₁ : ℚ) :
    ((M₀ : ℚ) * d) * ((a₁ - a₀) / ((M₀ : ℚ) * d)) + a₀ = a₁ := by
  have hstep : (M₀ : ℚ) * d ≠ 0 := by positivity
  field_simp [hstep]
  ring

theorem residueTransition_physical {M₀ M₁ d : ℕ}
    (hM₀ : 0 < M₀) (hd : 0 < d) (hdiv : M₀ ∣ M₁)
    {ρ W S A : ℝ} (hρ : 0 ≤ ρ)
    (hold : ρ * W ≤ ((M₀ : ℝ) * d) * S) (hcurrent : (M₁ : ℝ) * A ≤ W) :
    ρ * (|((((M₁ / M₀ : ℕ) : ℚ) / d : ℚ) : ℝ)| * A) ≤ S := by
  have hstep : 0 < (M₀ : ℝ) * d := by positivity
  have hscale : ((M₀ : ℝ) * d) * ((((M₁ / M₀ : ℕ) : ℚ) / d : ℚ) : ℝ) = M₁ := by
    exact_mod_cast residueTransition_scale hdiv hd
  have hr : 0 ≤ ((((M₁ / M₀ : ℕ) : ℚ) / d : ℚ) : ℝ) := by positivity
  apply (mul_le_mul_iff_right₀ hstep).mp
  calc
    ((M₀ : ℝ) * d) * (ρ * (|((((M₁ / M₀ : ℕ) : ℚ) / d : ℚ) : ℝ)| * A)) =
        ρ * ((((M₀ : ℝ) * d) * ((((M₁ / M₀ : ℕ) : ℚ) / d : ℚ) : ℝ)) * A) := by
          rw [abs_of_nonneg hr]
          ring
    _ = ρ * ((M₁ : ℝ) * A) := by rw [hscale]
    _ ≤ ρ * W := mul_le_mul_of_nonneg_left hcurrent hρ
    _ ≤ ((M₀ : ℝ) * d) * S := hold

theorem residueTransition_denominator_bound {n d : ℕ} {B : ℝ}
    (hn : (n : ℝ) ≤ Real.exp B) (hd : (d : ℝ) ≤ Real.exp B) (s : ℕ) :
    ((n * d ^ s : ℕ) : ℝ) ≤ Real.exp (((s : ℝ) + 1) * B) := by
  push_cast
  calc
    (n : ℝ) * (d : ℝ) ^ s ≤ Real.exp B * Real.exp B ^ s :=
      mul_le_mul hn (pow_le_pow_left₀ (Nat.cast_nonneg _) hd s)
        (pow_nonneg (Nat.cast_nonneg _) _) (Real.exp_nonneg _)
    _ = Real.exp (((s : ℝ) + 1) * B) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

end Erdos3

end

section

namespace Erdos3

def residueBoxStrideValue {I : Type*} {a b r v : I → ℤ}
    (f : (I → ℤ) → ℂ) (u : I → ℤ) (M : ℕ) (x : IntegerResidueBox a b r v) : ℂ :=
  f (commonStrideIndex u M (fun i => (x i).val))

theorem integerInterval_abs_sub_le (a u x : ℤ) (N : ℕ)
    (hx : x ∈ Finset.Ico a (a + N)) :
    |(x : ℝ) - (u : ℝ)| ≤ |(a : ℝ) - (u : ℝ)| + (N : ℝ) := by
  have hlo : (a : ℝ) ≤ x := by exact_mod_cast (Finset.mem_Ico.mp hx).1
  have hhi : (x : ℝ) < (a : ℝ) + N := by exact_mod_cast (Finset.mem_Ico.mp hx).2
  have htri := abs_sub_le (x : ℝ) a u
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)] at htri
  linarith

theorem residueBox_stride_bound {I : Type*} (a : I → ℤ) (N : I → ℕ)
    (M : ℕ) (hM : 0 < M) (u r b : I → ℤ)
    (hbase : ∀ i (x : ℤ), x ≡ b i [ZMOD r i] → x ≡ u i [ZMOD (M : ℤ)])
    (A : I → ℝ)
    (hphysical : ∀ i, (u i : ℝ) - (M : ℝ) * A i ≤ (a i : ℝ) ∧
      (a i : ℝ) + (N i : ℝ) ≤ (u i : ℝ) + (M : ℝ) * A i)
    (x : IntegerResidueBox a (fun i => a i + N i) r b) :
    ∀ i, |(commonStrideIndex u M (fun j => (x j).val) i : ℝ)| ≤ A i := by
  apply commonStrideIndex_bound u hM _
    (fun i => hbase i (x i).val (Finset.mem_filter.mp (x i).property).2) A
  intro i
  have hx := Finset.mem_Ico.mp (Finset.mem_filter.mp (x i).property).1
  have hlo : (a i : ℝ) ≤ (x i).val := by exact_mod_cast hx.1
  have hhi : ((x i).val : ℝ) < (a i : ℝ) + (N i : ℝ) := by exact_mod_cast hx.2
  exact abs_le.mpr ⟨by linarith [(hphysical i).1], by linarith [(hphysical i).2]⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

def residueStepMatrix {I : Type*} [DecidableEq I] (J : I → ℕ) : I → I → ℤ :=
  fun i j => if i = j then (J i : ℤ) else 0

theorem integerAffineMap_residueStepMatrix {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (J : I → ℕ) (x : I → ℤ) :
    integerAffineMap (residueStepMatrix J) a x = fun i => a i + (J i : ℤ) * x i :=
  integerAffineMap_diagonal a (fun i => (J i : ℤ)) x

theorem commonStrideIndex_residue_affine {I : Type*} (u v : I → ℤ) {M : ℕ} (hM : 0 < M)
    (J : I → ℕ) (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]) (x : I → ℤ) :
    commonStrideIndex u M (fun i => v i + ((M * J i : ℕ) : ℤ) * x i) =
      fun i => commonStrideIndex u M v i + (J i : ℤ) * x i := by
  have heq : commonStridePoint u M (fun i => commonStrideIndex u M v i + (J i : ℤ) * x i) =
      (fun i => v i + ((M * J i : ℕ) : ℤ) * x i) := by
    funext i
    have hbase := congrFun (commonStridePoint_index_of_modEq u M v hv) i
    change u i + (M : ℤ) * commonStrideIndex u M v i = v i at hbase
    change u i + (M : ℤ) * (commonStrideIndex u M v i + (J i : ℤ) * x i) = _
    calc
      _ = (u i + (M : ℤ) * commonStrideIndex u M v i) + ((M * J i : ℕ) : ℤ) * x i := by
        push_cast
        ring
      _ = _ := by rw [hbase]
  rw [← heq, commonStrideIndex_point u hM]

theorem residueBoxStride_expect {I : Type*} [Fintype I] [DecidableEq I]
    (a b : I → ℤ) (M : ℕ) (hM : 0 < M) (u v : I → ℤ) (J : I → ℕ)
    (hJ : ∀ i, 0 < J i) (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]) (f : (I → ℤ) → ℂ) :
    (𝔼 x : IntegerResidueBox a b (fun i => (M * J i : ℕ)) v, residueBoxStrideValue f u M x) =
      𝔼 x ∈ translatedIntegerBox
        (fun i => residueIndexLower (a i) (M * J i : ℕ) (v i))
        (fun i => residueIndexLength (a i) (b i) (M * J i : ℕ) (v i)),
        f (fun i => commonStrideIndex u M v i + (J i : ℤ) * x i) := by
  change (𝔼 x : IntegerResidueBox a b (fun i => (M * J i : ℕ)) v,
    f (commonStrideIndex u M (fun i => (x i).val))) = _
  rw [integerResidueBox_expect a b (fun i => (M * J i : ℕ)) v
    (fun i => by exact_mod_cast Nat.mul_pos hM (hJ i)) (fun y => f (commonStrideIndex u M y))]
  apply Finset.expect_congr rfl
  intro x _
  exact congrArg f (commonStrideIndex_residue_affine u v hM J hv x)

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d}

theorem residueBoxStride_mean (T : D.Niltest (fun _ : σ => 1))
    (a b : σ → ℤ) (M : ℕ) (hM : 0 < M) (u v : σ → ℤ) (J : σ → ℕ)
    (hJ : ∀ i, 0 < J i) (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]) :
    (𝔼 x : IntegerResidueBox a b (fun i => (M * J i : ℕ)) v, residueBoxStrideValue T.eval u M x) =
      𝔼 x ∈ translatedIntegerBox
        (fun i => residueIndexLower (a i) (M * J i : ℕ) (v i))
        (fun i => residueIndexLength (a i) (b i) (M * J i : ℕ) (v i)),
        (T.affinePullback (residueStepMatrix J) (commonStrideIndex u M v)).eval x := by
  rw [residueBoxStride_expect a b M hM u v J hJ hv]
  apply Finset.expect_congr rfl
  intro x _
  rw [eval_affinePullback, integerAffineMap_residueStepMatrix]

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

section

namespace Erdos3

theorem scalarAffinePolynomial_comp {σ : Type*} (r₀ r₁ : ℚ) (h₀ h₁ : σ → ℚ) (i : σ) :
    MvPolynomial.aeval (scalarAffinePolynomial r₁ h₁) (scalarAffinePolynomial r₀ h₀ i) =
      scalarAffinePolynomial (r₀ * r₁) (fun j => r₀ * h₁ j + h₀ j) i := by
  simp only [scalarAffinePolynomial, map_add, map_mul, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq]
  ring

namespace RationalFilteredNilmanifold.Niltest

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

theorem scalarAffinePullback_comp_orbit (T : D.Niltest (fun _ : σ => 1))
    (r₀ r₁ : ℚ) (h₀ h₁ : σ → ℚ) :
    ((T.scalarAffinePullback r₀ h₀).scalarAffinePullback r₁ h₁).orbit =
      (T.scalarAffinePullback (r₀ * r₁) (fun i => r₀ * h₁ i + h₀ i)).orbit := by
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.substitute (scalarAffinePolynomial r₁ h₁)
      (VectorPolynomial.substitute (scalarAffinePolynomial r₀ h₀) T.orbit.log) =
    VectorPolynomial.substitute (scalarAffinePolynomial (r₀ * r₁) (fun i => r₀ * h₁ i + h₀ i))
      T.orbit.log
  rw [VectorPolynomial.substitute_comp]
  simp only [scalarAffinePolynomial_comp]

theorem scalarAffinePullback_comp_orbit_of_eq (T : D.Niltest (fun _ : σ => 1))
    (r₀ r₁ a : ℚ) (h₀ h₁ shift : σ → ℚ) (hr : r₀ * a = r₁)
    (hh : ∀ i, r₀ * shift i + h₀ i = h₁ i) :
    ((T.scalarAffinePullback r₀ h₀).scalarAffinePullback a shift).orbit =
      (T.scalarAffinePullback r₁ h₁).orbit := by
  rw [T.scalarAffinePullback_comp_orbit, hr, funext hh]

theorem scalarAffinePullback_transition_orbit (T : D.Niltest (fun _ : σ => 1))
    (r₀ r₁ : ℚ) (h₀ h₁ : σ → ℚ) (hr₀ : r₀ ≠ 0) :
    ((T.scalarAffinePullback r₀ h₀).scalarAffinePullback (r₁ / r₀)
      (fun i => (h₁ i - h₀ i) / r₀)).orbit = (T.scalarAffinePullback r₁ h₁).orbit := by
  apply T.scalarAffinePullback_comp_orbit_of_eq
  · field_simp
  · intro i
    field_simp
    ring

theorem scalarAffinePullback_transition_factorization (T : D.Niltest (fun _ : σ => 1))
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (r₀ r₁ : ℚ) (h₀ h₁ shift : σ → ℚ) {S H : σ → ℝ} {p q : ℝ} {M : ℕ}
    {U : LieSubalgebra ℚ D.filtration.AssociatedGraded}
    (h : D.filtration.SymbolFactorizationIn b ω hF S
      ((T.scalarAffinePullback r₀ h₀).symbol b ω hF) p M U)
    (a : ℤ) (m : ℕ) (ha : a ≠ 0) (hm : 0 < m)
    (hr : r₀ * ((a : ℚ) / m) = r₁) (hh : ∀ i, r₀ * shift i + h₀ i = h₁ i)
    (hS : ∀ i, 0 < S i) (hH : ∀ i, 0 < H i) (hq : 0 ≤ q)
    (hphysical : ∀ i, Real.exp (-q) * (|(((a : ℚ) / m : ℚ) : ℝ)| * H i) ≤ S i) :
    D.filtration.SymbolFactorizationIn b ω hF H
      ((T.scalarAffinePullback r₁ h₁).symbol b ω hF) (p + (s : ℝ) * q) (M * m ^ s) U := by
  have htransport := (T.scalarAffinePullback r₀ h₀).scalarAffinePullback_factorization
    b ω hF h a m ha hm shift hS hH hq hphysical
  have horbit := T.scalarAffinePullback_comp_orbit_of_eq r₀ r₁ ((a : ℚ) / m) h₀ h₁ shift hr hh
  have hsymbol :=
    ((T.scalarAffinePullback r₀ h₀).scalarAffinePullback ((a : ℚ) / m) shift).symbol_eq_of_orbit_eq
      (T.scalarAffinePullback r₁ h₁) horbit b ω hF
  rwa [hsymbol] at htransport

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

theorem residue_refinement_offset_identity {σ : Type*}
    (u v : σ → ℤ) (M : ℕ) (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]) (i : σ) :
    (M : ℚ) * (commonStrideIndex u M v i : ℚ) + (u i : ℚ) = (v i : ℚ) := by
  have h := congrFun (commonStridePoint_index_of_modEq u M v hv) i
  change u i + (M : ℤ) * commonStrideIndex u M v i = v i at h
  exact_mod_cast (show (M : ℤ) * commonStrideIndex u M v i + u i = v i by omega)

theorem commonStrideIndex_of_refinement {σ : Type*}
    (u v : σ → ℤ) {M N : ℕ} (hM : 0 < M) (hMN : M ∣ N)
    (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]) (x : σ → ℤ) :
    commonStrideIndex u M (commonStridePoint v N x) =
      fun i => ((N / M : ℕ) : ℤ) * x i + commonStrideIndex u M v i := by
  change commonStrideIndex u M (fun i => v i + (N : ℤ) * x i) = _
  have h := commonStrideIndex_residue_affine u v hM (fun _ : σ => N / M) hv x
  simpa only [Nat.mul_div_cancel' hMN, add_comm] using h

theorem residue_refinement_parameter_bounds {σ : Type*}
    (u v : σ → ℤ) {M N : ℕ} (hM : 0 < M) (hMN : M ∣ N)
    (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]) (A B : σ → ℝ)
    (hoffset : ∀ i, |(v i : ℝ) - (u i : ℝ)| ≤ (M : ℝ) * A i)
    (hspan : ∀ i, (N : ℝ) * B i ≤ (M : ℝ) * A i) :
    (∀ i, |(commonStrideIndex u M v i : ℝ)| ≤ A i) ∧
    (∀ i, |((N / M : ℕ) : ℝ)| * B i ≤ A i) := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hscale : (M : ℝ) * (N / M : ℕ) = N := by exact_mod_cast Nat.mul_div_cancel' hMN
  constructor
  · intro i
    have hshift : (M : ℝ) * (commonStrideIndex u M v i : ℝ) = (v i : ℝ) - (u i : ℝ) := by
      have h := residue_refinement_offset_identity u v M hv i
      have hh : (M : ℝ) * (commonStrideIndex u M v i : ℝ) + (u i : ℝ) = (v i : ℝ) := by
        exact_mod_cast h
      linarith
    apply (mul_le_mul_iff_right₀ hMr).mp
    calc
      (M : ℝ) * |(commonStrideIndex u M v i : ℝ)| =
          |(M : ℝ) * (commonStrideIndex u M v i : ℝ)| := by rw [abs_mul, abs_of_pos hMr]
      _ = |(v i : ℝ) - (u i : ℝ)| := by rw [hshift]
      _ ≤ (M : ℝ) * A i := hoffset i
  · intro i
    apply (mul_le_mul_iff_right₀ hMr).mp
    calc
      (M : ℝ) * (|((N / M : ℕ) : ℝ)| * B i) = ((M : ℝ) * (N / M : ℕ)) * B i := by
        rw [abs_of_nonneg (Nat.cast_nonneg _)]; ring
      _ = (N : ℝ) * B i := by rw [hscale]
      _ ≤ (M : ℝ) * A i := hspan i

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

theorem scalarAffinePullback_refinement_orbit (T : D.Niltest (fun _ : σ => 1))
    (u v : σ → ℤ) {M N : ℕ} (hMN : M ∣ N)
    (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]) :
    ((T.scalarAffinePullback (M : ℚ) (fun i => (u i : ℚ))).scalarAffinePullback
      (N / M : ℕ) (fun i => (commonStrideIndex u M v i : ℚ))).orbit =
      (T.scalarAffinePullback (N : ℚ) (fun i => (v i : ℚ))).orbit := by
  apply T.scalarAffinePullback_comp_orbit_of_eq
  · exact_mod_cast Nat.mul_div_cancel' hMN
  · exact residue_refinement_offset_identity u v M hv

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem integerAffinePolynomial_residue_scalar {σ : Type*} [Fintype σ] [DecidableEq σ]
    (J : ℕ) (shift : σ → ℤ) :
    integerAffinePolynomial (residueStepMatrix (fun _ : σ => J)) shift =
      scalarAffinePolynomial (J : ℚ) (fun i => (shift i : ℚ)) := by
  funext i
  simp [integerAffinePolynomial, residueStepMatrix, scalarAffinePolynomial, apply_ite, ite_mul]

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d}

theorem residue_scalar_affine_orbit (T : D.Niltest (fun _ : σ => 1))
    (J : ℕ) (shift : σ → ℤ) :
    (T.affinePullback (residueStepMatrix (fun _ : σ => J)) shift).orbit =
      (T.scalarAffinePullback (J : ℚ) (fun i => (shift i : ℚ))).orbit := by
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.substitute (integerAffinePolynomial (residueStepMatrix (fun _ : σ => J)) shift)
      T.orbit.log = VectorPolynomial.substitute (scalarAffinePolynomial (J : ℚ)
        (fun i => (shift i : ℚ))) T.orbit.log
  rw [integerAffinePolynomial_residue_scalar]

theorem residue_scalar_affine_symbol (T : D.Niltest (fun _ : σ => 1))
    (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (J : ℕ) (shift : σ → ℤ) :
    (T.affinePullback (residueStepMatrix (fun _ : σ => J)) shift).symbol D.basis ω hF =
      (T.scalarAffinePullback (J : ℚ) (fun i => (shift i : ℚ))).symbol D.basis ω hF :=
  (T.affinePullback (residueStepMatrix (fun _ : σ => J)) shift).symbol_eq_of_orbit_eq
    (T.scalarAffinePullback (J : ℚ) (fun i => (shift i : ℚ)))
    (T.residue_scalar_affine_orbit J shift) D.basis ω hF

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s e}

theorem scalarAffinePullback_residue_factorization (T : D.Niltest (fun _ : σ => 1))
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {M₀ M₁ d n : ℕ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (hd : 0 < d) (hdiv : M₀ ∣ M₁)
    (h₀ h₁ : σ → ℚ) {S A W : σ → ℝ} {p q : ℝ}
    {U : LieSubalgebra ℚ D.filtration.AssociatedGraded}
    (h : D.filtration.SymbolFactorizationIn b ω hF S
      ((T.scalarAffinePullback ((M₀ : ℚ) * d) h₀).symbol b ω hF) p n U)
    (hS : ∀ i, 0 < S i) (hA : ∀ i, 0 < A i) (hq : 0 ≤ q)
    (hold : ∀ i, Real.exp (-q) * W i ≤ ((M₀ : ℝ) * d) * S i)
    (hcurrent : ∀ i, (M₁ : ℝ) * A i ≤ W i) :
    D.filtration.SymbolFactorizationIn b ω hF A
      ((T.scalarAffinePullback (M₁ : ℚ) h₁).symbol b ω hF)
      (p + (s : ℝ) * q) (n * d ^ s) U := by
  let a : ℤ := (M₁ / M₀ : ℕ)
  have ha : a ≠ 0 := by
    dsimp only [a]
    exact_mod_cast (residueTransitionNumerator_pos hM₁ hdiv).ne'
  apply T.scalarAffinePullback_transition_factorization b ω hF
    ((M₀ : ℚ) * d) (M₁ : ℚ) h₀ h₁ (fun i => (h₁ i - h₀ i) / ((M₀ : ℚ) * d))
    h a d ha hd
  · simpa only [a, Int.cast_natCast] using residueTransition_scale hdiv hd
  · intro i
    exact residueTransition_shift hM₀ hd (h₀ i) (h₁ i)
  · exact hS
  · exact hA
  · exact hq
  · intro i
    simpa only [a, Int.cast_natCast] using
      residueTransition_physical hM₀ hd hdiv (Real.exp_nonneg (-q)) (hold i) (hcurrent i)

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

theorem physical_box_anchor_bounds {σ : Type*}
    (lo lo' u v : σ → ℤ) (N N' : σ → ℕ)
    (hu : ∀ i, lo i ≤ u i ∧ u i < lo i + N i)
    (hsub : ∀ i, lo i ≤ lo' i ∧ lo' i + N' i ≤ lo i + N i)
    (hv : ∀ i, lo' i ≤ v i ∧ v i < lo' i + N' i) :
    (∀ i, |(v i : ℝ) - (u i : ℝ)| ≤ (N i : ℝ)) ∧
    (∀ i, N' i ≤ N i) := by
  constructor
  · intro i
    have hleft : -(N i : ℤ) ≤ v i - u i := by
      have := hu i
      have := hsub i
      have := hv i
      omega
    have hright : v i - u i ≤ (N i : ℤ) := by
      have := hu i
      have := hsub i
      have := hv i
      omega
    exact abs_le.mpr ⟨by exact_mod_cast hleft, by exact_mod_cast hright⟩
  · intro i
    have := hsub i
    omega

theorem anchored_residue_refinement_bounds {σ : Type*}
    (lo lo' u v : σ → ℤ) (N N' : σ → ℕ) {M M' : ℕ}
    (hM : 0 < M) (hM' : 0 < M') (hdiv : M ∣ M')
    (hcompat : ∀ i, v i ≡ u i [ZMOD (M : ℤ)])
    (hu : ∀ i, lo i ≤ u i ∧ u i < lo i + N i)
    (hsub : ∀ i, lo i ≤ lo' i ∧ lo' i + N' i ≤ lo i + N i)
    (hv : ∀ i, lo' i ≤ v i ∧ v i < lo' i + N' i)
    (hN' : ∀ i, 0 < N' i) :
    let A : σ → ℝ := fun i => (N i : ℝ) / M
    let B : σ → ℝ := fun i => (N' i : ℝ) / M'
    (∀ i, 0 < B i) ∧
    (∀ i, |(commonStrideIndex u M v i : ℝ)| ≤ A i) ∧
    (∀ i, |((M' / M : ℕ) : ℝ)| * B i ≤ A i) ∧
    (∀ i, (v i : ℝ) - (M' : ℝ) * B i ≤ (lo' i : ℝ) ∧
      (lo' i : ℝ) + (N' i : ℝ) ≤ (v i : ℝ) + (M' : ℝ) * B i) := by
  intro A B
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hM'r : (0 : ℝ) < M' := by exact_mod_cast hM'
  have hmul : ∀ i, (M : ℝ) * A i = (N i : ℝ) := by
    intro i
    dsimp only [A]
    field_simp
  have hmul' : ∀ i, (M' : ℝ) * B i = (N' i : ℝ) := by
    intro i
    dsimp only [B]
    field_simp
  obtain ⟨hoffset, hlength⟩ := physical_box_anchor_bounds lo lo' u v N N' hu hsub hv
  have hparams := residue_refinement_parameter_bounds u v hM hdiv hcompat A B
    (fun i => by simpa only [hmul] using hoffset i)
    (fun i => by simpa only [hmul, hmul'] using (show (N' i : ℝ) ≤ (N i : ℝ) by exact_mod_cast hlength i))
  refine ⟨fun i => div_pos (by exact_mod_cast hN' i) hM'r, hparams.1, hparams.2, ?_⟩
  intro i
  rw [hmul']
  have hlow : (lo' i : ℝ) ≤ (v i : ℝ) := by exact_mod_cast (hv i).1
  have hhigh : (v i : ℝ) < (lo' i : ℝ) + (N' i : ℝ) := by exact_mod_cast (hv i).2
  constructor <;> linarith

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

theorem eval_commonStride_rebase (T : D.Niltest (fun _ : σ => 1))
    (u v : σ → ℤ) {M N : ℕ} (hM : 0 < M) (hMN : M ∣ N)
    (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]) (x : σ → ℤ)
    (hx : ∀ i, x i ≡ v i [ZMOD (N : ℤ)]) :
    T.eval (commonStrideIndex u M x) =
      (T.scalarAffinePullback (N / M : ℕ) (fun i => (commonStrideIndex u M v i : ℚ))).eval
        (commonStrideIndex v N x) := by
  have hindex := commonStrideIndex_of_refinement u v hM hMN hv (commonStrideIndex v N x)
  rw [commonStridePoint_index_of_modEq v N x hx] at hindex
  have heval := T.scalarAffinePullback_eval_integer ((N / M : ℕ) : ℤ)
    (commonStrideIndex u M v) (commonStrideIndex v N x)
  calc
    T.eval (commonStrideIndex u M x) =
        T.eval (fun i => ((N / M : ℕ) : ℤ) * commonStrideIndex v N x i + commonStrideIndex u M v i) :=
      congrArg T.eval hindex
    _ = _ := by simpa only [Int.cast_natCast] using heval.symm

theorem residueBoxStride_rebase [Fintype σ] [DecidableEq σ]
    (T : D.Niltest (fun _ : σ => 1)) (lo hi r z u v : σ → ℤ)
    {M N : ℕ} (hM : 0 < M) (hMN : M ∣ N)
    (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)])
    (hz : ∀ i (x : ℤ), x ≡ z i [ZMOD r i] → x ≡ v i [ZMOD (N : ℤ)]) :
    (𝔼 x : IntegerResidueBox lo hi r z, residueBoxStrideValue T.eval u M x) =
      𝔼 x : IntegerResidueBox lo hi r z,
        residueBoxStrideValue
          (T.scalarAffinePullback (N / M : ℕ) (fun i => (commonStrideIndex u M v i : ℚ))).eval v N x := by
  apply Finset.expect_congr rfl
  intro x _
  exact T.eval_commonStride_rebase u v hM hMN hv (fun i => (x i).val)
    (fun i => hz i (x i).val (Finset.mem_filter.mp (x i).property).2)

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
