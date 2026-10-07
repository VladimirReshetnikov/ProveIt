import Mathlib.Data.ZMod.Basic
import OAI.Combinatorics.Progressions.Dynamics.RecursivePatchStepBudget
import OAI.Combinatorics.Progressions.Lattices.AffineLiftInsertion
import OAI.Combinatorics.Progressions.Lattices.AffineResidualRecovery
import OAI.Combinatorics.Progressions.Linear.BufferedKernelFamily
import OAI.Combinatorics.Progressions.Polynomial.PolynomialPatchRankPadding
import OAI.Combinatorics.Progressions.Sampling.BufferedScalarScoreBound
import OAI.Combinatorics.Progressions.Sampling.BufferedScoreDiscount

namespace OAI

section

namespace Erdos3.PatchKernel

open scoped NNReal

variable {d : ℕ}

noncomputable def weightBounded (Φ : PatchKernel d) (f : (Fin d → ℝ) → ℝ)
    (L C : ℝ≥0) (hC : 1 ≤ C) (hf : LipschitzWith L f)
    (hbound : ∀ x, f x ∈ Set.Icc (0 : ℝ) C) : PatchKernel d :=
  Φ.weight (fun x => f x / C) (L / C)
    (by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Real.dist_eq, ← sub_div, abs_div, abs_of_nonneg C.coe_nonneg]
      have h := div_le_div_of_nonneg_right (hf.dist_le_mul x y) C.coe_nonneg
      simpa only [Real.dist_eq, NNReal.coe_div, mul_div_right_comm] using h)
    (fun x => ⟨div_nonneg (hbound x).1 C.coe_nonneg,
      (div_le_one (show (0 : ℝ) < C by exact lt_of_lt_of_le zero_lt_one hC)).mpr (hbound x).2⟩)

@[simp] theorem weightBounded_lip (Φ : PatchKernel d) (f : (Fin d → ℝ) → ℝ)
    (L C : ℝ≥0) (hC : 1 ≤ C) (hf : LipschitzWith L f)
    (hbound : ∀ x, f x ∈ Set.Icc (0 : ℝ) C) :
    (Φ.weightBounded f L C hC hf hbound).lip = Φ.lip + L / C := rfl

theorem weightBounded_value (Φ : PatchKernel d) (f : (Fin d → ℝ) → ℝ)
    (L C : ℝ≥0) (hC : 1 ≤ C) (hf : LipschitzWith L f)
    (hbound : ∀ x, f x ∈ Set.Icc (0 : ℝ) C) (x : Fin d → ℝ) :
    (Φ.weightBounded f L C hC hf hbound).value x = Φ.value x * f x / C := by
  change Φ.value x * (f x / C) = _
  ring

theorem weightBounded_tsum {ι : Type*} (Φ : PatchKernel d) (f : (Fin d → ℝ) → ℝ)
    (L C : ℝ≥0) (hC : 1 ≤ C) (hf : LipschitzWith L f)
    (hbound : ∀ x, f x ∈ Set.Icc (0 : ℝ) C) (x : ι → Fin d → ℝ) (a : ι → ℝ) :
    (∑' i, (Φ.weightBounded f L C hC hf hbound).value (x i) * a i) =
      (∑' i, Φ.value (x i) * f (x i) * a i) / C := by
  rw [← tsum_div_const]
  apply tsum_congr
  intro i
  rw [weightBounded_value]
  ring

end Erdos3.PatchKernel

end

section

namespace Erdos3

theorem recoveredIntegerLift_eq_add_sum {d m : ℕ} (M : Fin m → Fin d → ℤ)
    (c : Fin m → ℤ) (k : Fin d → ℤ) :
    recoveredIntegerLift M c k = c + ∑ j, k j • (fun i => M i j) := by
  ext i
  simp [recoveredIntegerLift, Finset.sum_apply, mul_comm]

theorem recoveredIntegerLift_projection {A : Type*} [AddCommGroup A] {d m : ℕ}
    (M : Fin m → Fin d → ℤ) (π : (Fin m → ℤ) →+ A)
    (hπ : ∀ j, π (fun i => M i j) = 0) (c : Fin m → ℤ) (k : Fin d → ℤ) :
    π (recoveredIntegerLift M c k) = π c := by
  rw [recoveredIntegerLift_eq_add_sum, map_add, map_sum]
  simp only [map_zsmul, hπ, zsmul_zero, Finset.sum_const_zero, add_zero]

theorem recoveredIntegerLift_residue {d m : ℕ} (M : Fin m → Fin d → ℤ) (q : ℕ)
    (hM : ∀ i j, (q : ℤ) ∣ M i j) (c : Fin m → ℤ) (k : Fin d → ℤ) :
    (fun i => (recoveredIntegerLift M c k i : ZMod q)) = fun i => (c i : ZMod q) := by
  funext i
  have hzero (j) : (M i j : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hM i j)
  simp only [recoveredIntegerLift, Int.cast_add, Int.cast_sum, Int.cast_mul, hzero,
    zero_mul, Finset.sum_const_zero, add_zero]

theorem recoveredIntegerLift_discrete_data {A X : Type*} [AddCommGroup A] {d m : ℕ}
    (M : Fin m → Fin d → ℤ) (q : ℕ) (hM : ∀ i j, (q : ℤ) ∣ M i j)
    (π : (Fin m → ℤ) →+ A) (hπ : ∀ j, π (fun i => M i j) = 0)
    (F : (Fin m → ZMod q) → A → X) (c : Fin m → ℤ) (k : Fin d → ℤ) :
    F (fun i => (recoveredIntegerLift M c k i : ZMod q)) (π (recoveredIntegerLift M c k)) =
      F (fun i => (c i : ZMod q)) (π c) := by
  rw [recoveredIntegerLift_residue M q hM, recoveredIntegerLift_projection M π hπ]

end Erdos3

end

section

namespace Erdos3.PolynomialPatch

open scoped NNReal

variable {σ : Type*} {s d E m : ℕ} {p : Fin m → ℕ}

noncomputable abbrev withRecoveredWeight (A : PolynomialPatch σ s d) (Ψ : PatchKernel m)
    (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) : PolynomialPatch σ s d :=
  { A with kernel := recoveredCellKernel A.kernel Ψ M a c K hM }

noncomputable def recoveredPatch (A : PolynomialPatch σ s d)
    (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (Ψ : PatchKernel m) (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K)
    (hweight : ∀ i j, M i j ≠ 0 → A.weight j ≤ p i) : PolynomialPatch σ s (d + E) :=
  (A.withRecoveredWeight Ψ M a c K hM).insertAffineLifts B
    (fun i => (c i : ℝ)) (fun i j => (M i j : ℝ))
    (fun i j h => hweight i j (by exact_mod_cast h))

@[simp] theorem recoveredPatch_lip (A : PolynomialPatch σ s d)
    (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (Ψ : PatchKernel m) (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K)
    (hweight : ∀ i j, M i j ≠ 0 → A.weight j ≤ p i) :
    (A.recoveredPatch B Ψ M a c K hM hweight).kernel.lip = A.kernel.lip + Ψ.lip * K + B.kernel.lip := rfl

theorem insertAffineLifts_value (A : PolynomialPatch σ s d)
    (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (c : Fin m → ℝ) (M : Fin m → Fin d → ℝ)
    (hweight : ∀ i j, M i j ≠ 0 → A.weight j ≤ p i) (t : σ → ℝ) :
    (A.insertAffineLifts B c M hweight).value t = ∑' k : Fin d → ℤ,
      A.kernel.value ((A.form.slots t).residual k) *
        B.value (Sum.elim t (fun i => c i + ∑ j, M i j * (k j : ℝ))) := by
  unfold insertAffineLifts
  rw [insertLifts_value]
  apply tsum_congr
  intro k
  rw [WeightedParameterPatch.reparam_value]
  simp only [affineLiftSubstitution_eval]

theorem recoveredPatch_value_at_lift (A : PolynomialPatch σ s d)
    (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (Ψ : PatchKernel m) (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K)
    (hweight : ∀ i j, M i j ≠ 0 → A.weight j ≤ p i)
    (t : σ → ℝ) (x : Fin d → ℝ) (hslots : A.form.slots t = constantSlots (x - a))
    (k : Fin d → ℤ) (hk : ∀ j, |(k j : ℝ) - (x - a) j| ≤ 1 / 3) :
    (A.recoveredPatch B Ψ M a c K hM hweight).value t =
      A.kernel.value (fun j => (k j : ℝ) - (x - a) j) *
        Ψ.value (fun i => realIntegerMatrix M x i - (recoveredIntegerLift M c k i : ℝ)) *
        B.value (Sum.elim t (fun i => (recoveredIntegerLift M c k i : ℝ))) := by
  have hres : (A.form.slots t).residual k = fun j => (k j : ℝ) - (x - a) j := by
    rw [hslots]
    rfl
  unfold recoveredPatch
  rw [insertAffineLifts_value_at_lift _ _ _ _ _ t k (by simpa only [withRecoveredWeight, hres] using hk)]
  change (recoveredCellKernel A.kernel Ψ M a c K hM).value ((A.form.slots t).residual k) * _ = _
  rw [hres, recoveredCellKernel_value, recoveredSmallLift_at_integer]
  simp only [recoveredIntegerLift, Int.cast_add, Int.cast_sum, Int.cast_mul]

theorem recoveredPatch_value (A : PolynomialPatch σ s d)
    (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (Ψ : PatchKernel m) (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K)
    (hweight : ∀ i j, M i j ≠ 0 → A.weight j ≤ p i)
    (t : σ → ℝ) (x : Fin d → ℝ) (hslots : A.form.slots t = constantSlots (x - a)) :
    let k := A.kernel.integerLift (x - a)
    (A.recoveredPatch B Ψ M a c K hM hweight).value t =
      A.kernel.periodicValue (x - a) *
        Ψ.value (fun i => realIntegerMatrix M x i - (recoveredIntegerLift M c k i : ℝ)) *
        B.value (Sum.elim t (fun i => (recoveredIntegerLift M c k i : ℝ))) := by
  intro k
  by_cases hactive : A.kernel.periodicValue (x - a) = 0
  · rw [hactive, zero_mul, zero_mul]
    unfold recoveredPatch
    rw [insertAffineLifts_value]
    calc
      _ = ∑' _b : Fin d → ℤ, (0 : ℝ) := by
        apply tsum_congr
        intro b
        have hb : A.kernel.value (fun j => (b j : ℝ) - (x - a) j) = 0 :=
          le_antisymm (by simpa only [hactive] using A.kernel.kernel_le_periodicValue (x - a) b)
            (A.kernel.nonneg _)
        change (A.kernel.value ((A.form.slots t).residual b) * _) * _ = 0
        rw [hslots]
        change (A.kernel.value (fun j => (b j : ℝ) - (x - a) j) * _) * _ = 0
        rw [hb, zero_mul, zero_mul]
      _ = 0 := tsum_zero
  · have hk : ∀ j, |(k j : ℝ) - (x - a) j| ≤ 1 / 3 := fun j =>
      (A.kernel.support _ (A.kernel.integerLift_contributes _ hactive) j).trans (by norm_num)
    rw [A.recoveredPatch_value_at_lift B Ψ M a c K hM hweight t x hslots k hk,
      A.kernel.periodicValue_eq_integerLift]

end Erdos3.PolynomialPatch

end

section

namespace Erdos3

open MvPolynomial
open scoped NNReal BigOperators

namespace PolynomialPatch

theorem recoveredPatch_value_eq_family {σ : Type*} {s d E m : ℕ} {p : Fin m → ℕ}
    (A : PolynomialPatch σ s d)
    (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (Ψ : (Fin m → ℤ) → PatchKernel m) (M : Fin m → Fin d → ℤ)
    (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K)
    (hweight : ∀ i j, M i j ≠ 0 → A.weight j ≤ p i)
    (hinvariant : ∀ k, (Ψ (recoveredIntegerLift M c k)).value = (Ψ c).value)
    (t : σ → ℝ) (x : Fin d → ℝ) (hslots : A.form.slots t = constantSlots (x - a))
    (β : Fin m → ℤ) (hβ : ∀ i, |realIntegerMatrix M x i - (β i : ℝ)| ≤ 1 / 2)
    (hmatch : A.kernel.periodicValue (x - a) ≠ 0 →
      (Ψ β).value (fun i => realIntegerMatrix M x i - (β i : ℝ)) ≠ 0 →
      recoveredIntegerLift M c (A.kernel.integerLift (x - a)) = β) :
    (A.recoveredPatch B (Ψ c) M a c K hM hweight).value t =
      A.kernel.periodicValue (x - a) * (Ψ β).value (fun i => realIntegerMatrix M x i - (β i : ℝ)) *
        B.value (Sum.elim t (fun i => (β i : ℝ))) := by
  rw [A.recoveredPatch_value B (Ψ c) M a c K hM hweight t x hslots]
  by_cases h : A.kernel.periodicValue (x - a) = 0
  · simp only [h, zero_mul]
  · simp only [mul_assoc]
    apply congrArg (fun z => A.kernel.periodicValue (x - a) * z)
    rw [← hinvariant (A.kernel.integerLift (x - a))]
    exact PatchKernel.buffered_family_lift_value_eq Ψ (realIntegerMatrix M x) β _ hβ
      (hmatch h) (fun β => B.value (Sum.elim t (fun i => (β i : ℝ))))

end PolynomialPatch

theorem exists_fiberwise_recovered_patch {σ Ω : Type*} [Fintype Ω] {s d E m : ℕ}
    (w : Fin d → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (P : Fin d → MvPolynomial σ ℝ) (hP : ∀ j, P j ∈ weightedSupportLE (fun _ : σ => 1) (w j))
    (p : Fin m → ℕ) (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (Ψ : (Fin m → ℤ) → PatchKernel m)
    (M : Fin m → Fin d → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (hinvariant : ∀ c k, (Ψ (recoveredIntegerLift M c k)).value = (Ψ c).value)
    (q : ℕ) (hq : 8 ≤ q) (hmesh : 16 * (K : ℝ) ≤ q)
    (t : Ω → σ → ℝ) (score : Ω → ℝ) {S : ℝ}
    (hscore : S ≤ 𝔼 u, score u * ∑' β : Fin m → ℤ,
      (Ψ β).value (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)) *
        B.value (Sum.elim (t u) (fun i => (β i : ℝ)))) :
    ∃ (c : Fin m → ℤ) (Q : PolynomialPatch σ s (d + E)),
      Q.kernel.lip = (q : ℝ≥0) * (2 * (q : ℝ≥0) ^ d + 1) + (Ψ c).lip * K + B.kernel.lip ∧
      S / (q : ℝ) ^ d ≤ 𝔼 u, score u * Q.value (t u) := by
  classical
  let x : Ω → Fin d → ℝ := fun u j => aeval (t u) (P j)
  let β : Ω → Fin m → ℤ := fun u => nearestIntegerLift (realIntegerMatrix M (x u))
  let H : Ω → ℝ := fun u => (Ψ (β u)).value (fun i => realIntegerMatrix M (x u) i - (β u i : ℝ)) *
    B.value (Sum.elim (t u) (fun i => (β u i : ℝ)))
  have hS : S ≤ 𝔼 u, score u * H u := by
    simpa only [PatchKernel.buffered_family_sum_eq_nearest] using hscore
  let cell : (Fin d → Fin q) → Ω → ℝ :=
    fun a u => (torusGridKernel d q hq a).periodicValue (x u - torusGridCenter q a)
  let : NeZero q := ⟨by omega⟩
  obtain ⟨a, ha⟩ := exists_weighted_partition_score (fun u => score u * H u) cell
    (fun u => sum_torusGridKernel_periodicValue d q hq (x u)) hS
  have hcellscore : S / (q : ℝ) ^ d ≤ 𝔼 u, (score u * H u) * cell a u := by
    simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using ha
  let active : Set Ω := {u | cell a u ≠ 0 ∧
    (Ψ (β u)).value (fun i => realIntegerMatrix M (x u) i - (β u i : ℝ)) ≠ 0}
  obtain ⟨c, hc⟩ := exists_torusCell_affine_recovery hq active M a x β hM hmesh
    (fun u hu => hu.1) (fun u hu => (Ψ (β u)).support _ hu.2)
  let A := polynomialTorusCell w hw hws hmono P hP q hq a
  have hweightA : ∀ i j, M i j ≠ 0 → A.weight j ≤ p i := hweight
  let Q := A.recoveredPatch B (Ψ c) M (torusGridCenter q a) c K hM hweightA
  refine ⟨c, Q, ?_, ?_⟩
  · change A.kernel.lip + (Ψ c).lip * K + B.kernel.lip = _
    exact congrArg (fun L => L + (Ψ c).lip * K + B.kernel.lip)
      (polynomialTorusCell_lip w hw hws hmono P hP q hq a)
  · have hvalue (u : Ω) : Q.value (t u) = cell a u * H u := by
      have hslots : A.form.slots (t u) = constantSlots (x u - torusGridCenter q a) := by
        apply TriangularSlots.ext
        intro z j
        have hshift : ∀ i, P i - C (torusGridCenter q a i) ∈
            weightedSupportLE (fun _ : σ => 1) (w i) :=
          fun i => (weightedSupportLE _ _).sub_mem (hP i) (weightedSupportLE_C _ _ _)
        change ((PolynomialSlots.ofCoordinates (w := w)
          (fun i => P i - C (torusGridCenter q a i)) hshift).slots (t u)).center z j = _
        rw [PolynomialSlots.ofCoordinates_center]
        simp [constantSlots, x]
      have hmatch : A.kernel.periodicValue (x u - torusGridCenter q a) ≠ 0 →
          (Ψ (β u)).value (fun i => realIntegerMatrix M (x u) i - (β u i : ℝ)) ≠ 0 →
          recoveredIntegerLift M c (A.kernel.integerLift (x u - torusGridCenter q a)) = β u := by
        intro h₁ h₂
        exact (hc u ⟨h₁, h₂⟩).symm
      change (A.recoveredPatch B (Ψ c) M (torusGridCenter q a) c K hM hweightA).value (t u) =
        A.kernel.periodicValue (x u - torusGridCenter q a) *
          ((Ψ (β u)).value (fun i => realIntegerMatrix M (x u) i - (β u i : ℝ)) *
            B.value (Sum.elim (t u) (fun i => (β u i : ℝ))))
      simpa only [mul_assoc] using A.recoveredPatch_value_eq_family B Ψ M (torusGridCenter q a)
        c K hM hweightA (hinvariant c) (t u) (x u) hslots (β u) (nearestIntegerLift_close _) hmatch
    apply hcellscore.trans_eq
    apply Finset.expect_congr rfl
    intro u _
    rw [hvalue]
    ring

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped NNReal BigOperators

namespace PolynomialPatch

theorem recoveredPatch_value_eq_buffered {σ : Type*} {s d E m : ℕ} {p : Fin m → ℕ}
    (A : PolynomialPatch σ s d)
    (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (Ψ : PatchKernel m) (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K)
    (hweight : ∀ i j, M i j ≠ 0 → A.weight j ≤ p i)
    (t : σ → ℝ) (x : Fin d → ℝ) (hslots : A.form.slots t = constantSlots (x - a))
    (β : Fin m → ℤ) (hβ : ∀ i, |realIntegerMatrix M x i - (β i : ℝ)| ≤ 1 / 2)
    (hmatch : A.kernel.periodicValue (x - a) ≠ 0 →
      Ψ.value (fun i => realIntegerMatrix M x i - (β i : ℝ)) ≠ 0 →
      recoveredIntegerLift M c (A.kernel.integerLift (x - a)) = β) :
    (A.recoveredPatch B Ψ M a c K hM hweight).value t =
      A.kernel.periodicValue (x - a) * Ψ.value (fun i => realIntegerMatrix M x i - (β i : ℝ)) *
        B.value (Sum.elim t (fun i => (β i : ℝ))) := by
  exact A.recoveredPatch_value_eq_family B (fun _ => Ψ) M a c K hM hweight
    (fun _ => rfl) t x hslots β hβ hmatch

end PolynomialPatch

theorem exists_buffered_recovered_patch {σ Ω : Type*} [Fintype Ω] {s d E m : ℕ}
    (w : Fin d → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (P : Fin d → MvPolynomial σ ℝ) (hP : ∀ j, P j ∈ weightedSupportLE (fun _ : σ => 1) (w j))
    (p : Fin m → ℕ) (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (Ψ : PatchKernel m) (M : Fin m → Fin d → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (q : ℕ) (hq : 8 ≤ q) (hmesh : 16 * (K : ℝ) ≤ q)
    (t : Ω → σ → ℝ) (score : Ω → ℝ) {S : ℝ}
    (hscore : S ≤ 𝔼 u, score u * ∑' β : Fin m → ℤ,
      Ψ.value (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)) *
        B.value (Sum.elim (t u) (fun i => (β i : ℝ)))) :
    ∃ Q : PolynomialPatch σ s (d + E),
      Q.kernel.lip = (q : ℝ≥0) * (2 * (q : ℝ≥0) ^ d + 1) + Ψ.lip * K + B.kernel.lip ∧
      S / (q : ℝ) ^ d ≤ 𝔼 u, score u * Q.value (t u) := by
  obtain ⟨c, Q, hQlip, hQscore⟩ := exists_fiberwise_recovered_patch w hw hws hmono P hP p B
    (fun _ => Ψ) M K hM hweight (fun _ _ => rfl) q hq hmesh t score hscore
  exact ⟨Q, hQlip, hQscore⟩

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped NNReal BigOperators

theorem exists_fiberwise_weighted_patch {σ Ω : Type*} [Fintype Ω] {s d E m : ℕ}
    (w : Fin d → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (P : Fin d → MvPolynomial σ ℝ) (hP : ∀ j, P j ∈ weightedSupportLE (fun _ : σ => 1) (w j))
    (p : Fin m → ℕ) (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (χ : PatchKernel m) (F : (Fin m → ℤ) → (Fin m → ℝ) → ℝ) (L C : ℝ≥0) (hC : 1 ≤ C)
    (hF : ∀ β, LipschitzWith L (F β)) (hFbound : ∀ β y, F β y ∈ Set.Icc (0 : ℝ) C)
    (M : Fin m → Fin d → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (hinvariant : ∀ c k, F (recoveredIntegerLift M c k) = F c)
    (q : ℕ) (hq : 8 ≤ q) (hmesh : 16 * (K : ℝ) ≤ q)
    (t : Ω → σ → ℝ) (score : Ω → ℝ) {S : ℝ}
    (hscore : S ≤ 𝔼 u, score u * ∑' β : Fin m → ℤ,
      χ.value (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)) *
        F β (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)) *
        B.value (Sum.elim (t u) (fun i => (β i : ℝ)))) :
    ∃ Q : PolynomialPatch σ s (d + E),
      Q.kernel.lip ≤ (q : ℝ≥0) * (2 * (q : ℝ≥0) ^ d + 1) +
        (χ.lip + L / C) * K + B.kernel.lip ∧
      S / ((C : ℝ) * (q : ℝ) ^ d) ≤ 𝔼 u, score u * Q.value (t u) := by
  let Ψ : (Fin m → ℤ) → PatchKernel m := fun β => χ.weightBounded (F β) L C hC (hF β) (hFbound β)
  have hΨ : ∀ c k, (Ψ (recoveredIntegerLift M c k)).value = (Ψ c).value := by
    intro c k
    funext y
    simp only [Ψ, PatchKernel.weightBounded_value, hinvariant]
  have hnormalized : S / (C : ℝ) ≤ 𝔼 u, score u * ∑' β : Fin m → ℤ,
      (Ψ β).value (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)) *
        B.value (Sum.elim (t u) (fun i => (β i : ℝ))) := by
    apply (div_le_div_of_nonneg_right hscore C.coe_nonneg).trans_eq
    rw [Finset.expect_div]
    apply Finset.expect_congr rfl
    intro u _
    simp only [Ψ, PatchKernel.weightBounded_value, div_mul_eq_mul_div]
    rw [tsum_div_const]
    ring
  obtain ⟨c, Q, hQlip, hQscore⟩ := exists_fiberwise_recovered_patch w hw hws hmono P hP p B Ψ
    M K hM hweight hΨ q hq hmesh t score hnormalized
  exact ⟨Q, hQlip.le, by simpa only [div_div] using hQscore⟩

theorem exists_discrete_weighted_recovered_patch {σ Ω A : Type*} [Fintype Ω] [AddCommGroup A]
    {s d E m : ℕ}
    (w : Fin d → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (P : Fin d → MvPolynomial σ ℝ) (hP : ∀ j, P j ∈ weightedSupportLE (fun _ : σ => 1) (w j))
    (p : Fin m → ℕ) (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (χ : PatchKernel m) (N : ℕ) (π : (Fin m → ℤ) →+ A)
    (F : (Fin m → ZMod N) → A → (Fin m → ℝ) → ℝ) (L C : ℝ≥0) (hC : 1 ≤ C)
    (hF : ∀ r z, LipschitzWith L (F r z)) (hFbound : ∀ r z y, F r z y ∈ Set.Icc (0 : ℝ) C)
    (M : Fin m → Fin d → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (hdiv : ∀ i j, (N : ℤ) ∣ M i j) (hπ : ∀ j, π (fun i => M i j) = 0)
    (q : ℕ) (hq : 8 ≤ q) (hmesh : 16 * (K : ℝ) ≤ q)
    (t : Ω → σ → ℝ) (score : Ω → ℝ) {S : ℝ}
    (hscore : S ≤ 𝔼 u, score u * ∑' β : Fin m → ℤ,
      χ.value (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)) *
        F (fun i => (β i : ZMod N)) (π β)
          (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)) *
        B.value (Sum.elim (t u) (fun i => (β i : ℝ)))) :
    ∃ Q : PolynomialPatch σ s (d + E),
      Q.kernel.lip ≤ (q : ℝ≥0) * (2 * (q : ℝ≥0) ^ d + 1) +
        (χ.lip + L / C) * K + B.kernel.lip ∧
      S / ((C : ℝ) * (q : ℝ) ^ d) ≤ 𝔼 u, score u * Q.value (t u) := by
  exact exists_fiberwise_weighted_patch w hw hws hmono P hP p B χ
    (fun β => F (fun i => (β i : ZMod N)) (π β)) L C hC
    (fun β => hF _ _) (fun β => hFbound _ _) M K hM hweight
    (recoveredIntegerLift_discrete_data M N hdiv π hπ F) q hq hmesh t score hscore

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped NNReal BigOperators

theorem exists_weighted_recovered_patch {σ Ω : Type*} [Fintype Ω] {s d E m : ℕ}
    (w : Fin d → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (P : Fin d → MvPolynomial σ ℝ) (hP : ∀ j, P j ∈ weightedSupportLE (fun _ : σ => 1) (w j))
    (p : Fin m → ℕ) (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (χ : PatchKernel m) (F : (Fin m → ℝ) → ℝ) (L C : ℝ≥0) (hC : 1 ≤ C)
    (hF : LipschitzWith L F) (hFbound : ∀ y, F y ∈ Set.Icc (0 : ℝ) C)
    (M : Fin m → Fin d → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (q : ℕ) (hq : 8 ≤ q) (hmesh : 16 * (K : ℝ) ≤ q)
    (t : Ω → σ → ℝ) (score : Ω → ℝ) {S : ℝ}
    (hscore : S ≤ 𝔼 u, score u * ∑' β : Fin m → ℤ,
      χ.value (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)) *
        F (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)) *
        B.value (Sum.elim (t u) (fun i => (β i : ℝ)))) :
    ∃ Q : PolynomialPatch σ s (d + E),
      Q.kernel.lip = (q : ℝ≥0) * (2 * (q : ℝ≥0) ^ d + 1) +
        (χ.lip + L / C) * K + B.kernel.lip ∧
      S / ((C : ℝ) * (q : ℝ) ^ d) ≤ 𝔼 u, score u * Q.value (t u) := by
  let Ψ := χ.weightBounded F L C hC hF hFbound
  have hnormalized : S / (C : ℝ) ≤ 𝔼 u, score u * ∑' β : Fin m → ℤ,
      Ψ.value (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)) *
        B.value (Sum.elim (t u) (fun i => (β i : ℝ))) := by
    apply (div_le_div_of_nonneg_right hscore C.coe_nonneg).trans_eq
    rw [Finset.expect_div]
    apply Finset.expect_congr rfl
    intro u _
    rw [χ.weightBounded_tsum F L C hC hF hFbound]
    ring
  obtain ⟨Q, hQlip, hQscore⟩ := exists_buffered_recovered_patch w hw hws hmono P hP p B Ψ M K
    hM hweight q hq hmesh t score hnormalized
  refine ⟨Q, ?_, ?_⟩
  · simpa only [Ψ, PatchKernel.weightBounded_lip] using hQlip
  · simpa only [div_div] using hQscore

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped NNReal BigOperators

theorem exists_discounted_recovered_patch {σ Ω : Type*} [Fintype Ω] {s d E m : ℕ}
    (w : Fin d → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (P : Fin d → MvPolynomial σ ℝ) (hP : ∀ j, P j ∈ weightedSupportLE (fun _ : σ => 1) (w j))
    (p : Fin m → ℕ) (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (χ : PatchKernel m) (F : (Fin m → ℤ) → (Fin m → ℝ) → ℝ) (L C : ℝ≥0) (hC : 1 ≤ C)
    (hF : ∀ β, LipschitzWith L (F β)) (hFbound : ∀ β y, F β y ∈ Set.Icc (0 : ℝ) C)
    (M : Fin m → Fin d → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (hinvariant : ∀ c k, F (recoveredIntegerLift M c k) = F c)
    (q : ℕ) (hq : 8 ≤ q) (hmesh : 16 * (K : ℝ) ≤ q)
    (t : Ω → σ → ℝ) (f : Ω → ℝ) (G : Ω → (Fin m → ℤ) → ℝ) {lam δ ε S : ℝ}
    (hf : ∀ u, 0 ≤ f u) (hlam : 0 ≤ lam) (hδ : 0 ≤ δ)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hlower : ∀ u β, (1 - δ) *
      F β (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)) ≤ G u β)
    (hupper : ∀ u β, G u β ≤ (1 + δ) *
      F β (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)))
    (hscore : S ≤ 𝔼 u, (f u - lam) * ∑' β : Fin m → ℤ,
      χ.value (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)) *
        G u β * B.value (Sum.elim (t u) (fun i => (β i : ℝ)))) :
    ∃ Q : PolynomialPatch σ s (d + E),
      Q.kernel.lip ≤ (q : ℝ≥0) * (2 * (q : ℝ≥0) ^ d + 1) +
        (χ.lip + L / C) * K + B.kernel.lip ∧
      S / ((1 + δ) * (C : ℝ) * (q : ℝ) ^ d) ≤
        𝔼 u, (f u - (1 - ε) * lam) * Q.value (t u) := by
  have hs := buffered_score_discount χ
    (fun u => realIntegerMatrix M (fun j => aeval (t u) (P j)))
    (fun u β => B.value (Sum.elim (t u) (fun i => (β i : ℝ)))) G
    (fun u β => F β (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)))
    f hδ hf hlam (fun u β => (B.value_mem_Icc _).1) (fun u β => (hFbound _ _).1)
    hlower hupper hdiscount hscore
  obtain ⟨Q, hQlip, hQscore⟩ := exists_fiberwise_weighted_patch w hw hws hmono P hP p B χ F
    L C hC hF hFbound M K hM hweight hinvariant q hq hmesh t
    (fun u => f u - (1 - ε) * lam) hs
  refine ⟨Q, hQlip, ?_⟩
  simpa only [div_div, mul_assoc] using hQscore

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped NNReal BigOperators

theorem exists_modeled_discounted_patch {σ Ω U I : Type*} [Fintype Ω] [Fintype U] [Fintype I] {s d E m : ℕ}
    (w : Fin d → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (P : Fin d → MvPolynomial σ ℝ) (hP : ∀ j, P j ∈ weightedSupportLE (fun _ : σ => 1) (w j))
    (p : Fin m → ℕ) (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (χ : PatchKernel m) (F : (Fin m → ℤ) → (Fin m → ℝ) → ℝ) (L C : ℝ≥0) (hC : 1 ≤ C)
    (hF : ∀ β, LipschitzWith L (F β)) (hFbound : ∀ β y, F β y ∈ Set.Icc (0 : ℝ) C)
    (M : Fin m → Fin d → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (hinvariant : ∀ c k, F (recoveredIntegerLift M c k) = F c)
    (q : ℕ) (hq : 8 ≤ q) (hmesh : 16 * (K : ℝ) ≤ q)
    (t : Ω → σ → ℝ) (f : Ω → ℝ) (G : Ω → (Fin m → ℤ) → ℝ) {lam δ ε S : ℝ}
    (hf : ∀ u, 0 ≤ f u) (hlam : 0 ≤ lam) (hδ : 0 ≤ δ)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hlower : ∀ u β, (1 - δ) *
      F β (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)) ≤ G u β)
    (hupper : ∀ u β, G u β ≤ (1 + δ) *
      F β (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)))
    (ψ : U → Ω) (e : Ω → ℂ) (J : I → Ω → ℂ) (c : I → ℂ)
    (hmodel : (fun u => (bufferedScalarScore χ
      (fun u => realIntegerMatrix M (fun j => aeval (t u) (P j)))
      (fun u b => B.value (Sum.elim (t u) (fun i => (b i : ℝ)))) f lam u : ℂ)) =
        (∑ i, c i • J i) + e)
    {M₀ η α β : ℝ} (hη : 0 ≤ η) (hc : (∑ i, ‖c i‖) ≤ M₀)
    (hatom : ∀ i, ‖(𝔼 u, (G u (nearestIntegerLift
      (realIntegerMatrix M (fun j => aeval (t u) (P j)))) : ℂ) * J i u) -
        (𝔼 a, J i (ψ a))‖ ≤ η)
    (heA : ‖𝔼 u, (G u (nearestIntegerLift
      (realIntegerMatrix M (fun j => aeval (t u) (P j)))) : ℂ) * e u‖ ≤ α)
    (heB : ‖𝔼 a, e (ψ a)‖ ≤ β)
    (hscore : S ≤ 𝔼 a, bufferedScalarScore χ
      (fun u => realIntegerMatrix M (fun j => aeval (t u) (P j)))
      (fun u b => B.value (Sum.elim (t u) (fun i => (b i : ℝ)))) f lam (ψ a)) :
    ∃ Q : PolynomialPatch σ s (d + E),
      Q.kernel.lip ≤ (q : ℝ≥0) * (2 * (q : ℝ≥0) ^ d + 1) +
        (χ.lip + L / C) * K + B.kernel.lip ∧
      (S - (M₀ * η + α + β)) / ((1 + δ) * (C : ℝ) * (q : ℝ) ^ d) ≤
        𝔼 u, (f u - (1 - ε) * lam) * Q.value (t u) := by
  have hs := buffered_model_score_transfer χ
    (fun u => realIntegerMatrix M (fun j => aeval (t u) (P j)))
    (fun u b => B.value (Sum.elim (t u) (fun i => (b i : ℝ)))) G f lam ψ e J c
    hmodel hη hc hatom heA heB hscore
  exact exists_discounted_recovered_patch w hw hws hmono P hP p B χ F L C hC hF hFbound
    M K hM hweight hinvariant q hq hmesh t f G hf hlam hδ hdiscount hlower hupper hs

end Erdos3

end

section

namespace Erdos3.PolynomialPatch

open scoped NNReal BigOperators

variable {σ : Type*} {s d₀ d D j detector E m : ℕ} {p : Fin m → ℕ}

noncomputable def recursiveRecoveredPatch (A : PolynomialPatch σ s detector)
    (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (Ψ : PatchKernel m) (M : Fin m → Fin detector → ℤ)
    (a : Fin detector → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ k, |(M i k : ℝ)|) ≤ K)
    (hweight : ∀ i k, M i k ≠ 0 → A.weight k ≤ p i)
    (hs : 1 ≤ s) (hD : D ≤ d) (hE : E ≤ d₀ + s * (d-D))
    (hdetector : detector ≤ j * D) (hj : j ≤ s) :
    PolynomialPatch σ s (d₀ + s * d) :=
  (A.recoveredPatch B Ψ M a c K hM hweight).padRank hs
    (recursive_patch_step_rank_bound hD hE hdetector hj)

@[simp] theorem recursiveRecoveredPatch_value (A : PolynomialPatch σ s detector)
    (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (Ψ : PatchKernel m) (M : Fin m → Fin detector → ℤ)
    (a : Fin detector → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ k, |(M i k : ℝ)|) ≤ K)
    (hweight : ∀ i k, M i k ≠ 0 → A.weight k ≤ p i)
    (hs : 1 ≤ s) (hD : D ≤ d) (hE : E ≤ d₀ + s * (d-D))
    (hdetector : detector ≤ j * D) (hj : j ≤ s) (t : σ → ℝ) :
    (A.recursiveRecoveredPatch B Ψ M a c K hM hweight hs hD hE hdetector hj).value t =
      (A.recoveredPatch B Ψ M a c K hM hweight).value t :=
  padRank_value _ _ _ _

@[simp] theorem recursiveRecoveredPatch_lip (A : PolynomialPatch σ s detector)
    (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (Ψ : PatchKernel m) (M : Fin m → Fin detector → ℤ)
    (a : Fin detector → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ k, |(M i k : ℝ)|) ≤ K)
    (hweight : ∀ i k, M i k ≠ 0 → A.weight k ≤ p i)
    (hs : 1 ≤ s) (hD : D ≤ d) (hE : E ≤ d₀ + s * (d-D))
    (hdetector : detector ≤ j * D) (hj : j ≤ s) :
    (A.recursiveRecoveredPatch B Ψ M a c K hM hweight hs hD hE hdetector hj).kernel.lip =
      A.kernel.lip + Ψ.lip * K + B.kernel.lip + 4 := by
  rw [recursiveRecoveredPatch, padRank_lip, recoveredPatch_lip]

end Erdos3.PolynomialPatch

namespace Erdos3
open MvPolynomial
open scoped NNReal BigOperators

theorem exists_recursive_discounted_recovered_patch
    {σ Ω : Type*} [Fintype Ω] {s d₀ d D j detector E m : ℕ}
    (hs : 1 ≤ s) (hD : D ≤ d) (hE : E ≤ d₀ + s * (d-D))
    (hdetector : detector ≤ j * D) (hj : j ≤ s)
    (w : Fin detector → ℕ) (hw : ∀ k, 1 ≤ w k)
    (hws : ∀ k, w k ≤ s) (hmono : Monotone w)
    (P : Fin detector → MvPolynomial σ ℝ)
    (hP : ∀ k, P k ∈ weightedSupportLE (fun _ : σ => 1) (w k))
    (p : Fin m → ℕ) (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (χ : PatchKernel m) (F : (Fin m → ℤ) → (Fin m → ℝ) → ℝ)
    (L C : ℝ≥0) (hC : 1 ≤ C)
    (hF : ∀ β, LipschitzWith L (F β)) (hFbound : ∀ β y, F β y ∈ Set.Icc (0 : ℝ) C)
    (M : Fin m → Fin detector → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ k, |(M i k : ℝ)|) ≤ K)
    (hweight : ∀ i k, M i k ≠ 0 → w k ≤ p i)
    (hinvariant : ∀ c k, F (recoveredIntegerLift M c k) = F c)
    (q : ℕ) (hq : 8 ≤ q) (hmesh : 16 * (K : ℝ) ≤ q)
    (t : Ω → σ → ℝ) (f : Ω → ℝ) (G : Ω → (Fin m → ℤ) → ℝ) {lam δ ε S : ℝ}
    (hf : ∀ u, 0 ≤ f u) (hlam : 0 ≤ lam) (hδ : 0 ≤ δ)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hlower : ∀ u β, (1 - δ) * F β
      (fun i => realIntegerMatrix M (fun k => aeval (t u) (P k)) i - (β i : ℝ)) ≤ G u β)
    (hupper : ∀ u β, G u β ≤ (1 + δ) * F β
      (fun i => realIntegerMatrix M (fun k => aeval (t u) (P k)) i - (β i : ℝ)))
    (hscore : S ≤ 𝔼 u, (f u - lam) * ∑' β : Fin m → ℤ,
      χ.value (fun i => realIntegerMatrix M (fun k => aeval (t u) (P k)) i - (β i : ℝ)) *
        G u β * B.value (Sum.elim (t u) (fun i => (β i : ℝ)))) :
    ∃ Q : PolynomialPatch σ s (d₀ + s * d),
      Q.kernel.lip ≤ (q : ℝ≥0) * (2 * (q : ℝ≥0) ^ detector + 1) +
        (χ.lip + L / C) * K + B.kernel.lip + 4 ∧
      S / ((1 + δ) * (C : ℝ) * (q : ℝ) ^ detector) ≤
        𝔼 u, (f u - (1 - ε) * lam) * Q.value (t u) := by
  obtain ⟨Q, hQlip, hQscore⟩ := exists_discounted_recovered_patch w hw hws hmono P hP
    p B χ F L C hC hF hFbound M K hM hweight hinvariant q hq hmesh t f G hf hlam hδ
    hdiscount hlower hupper hscore
  let hRank := recursive_patch_step_rank_bound hD hE hdetector hj
  refine ⟨Q.padRank hs hRank, ?_, ?_⟩
  · rw [PolynomialPatch.padRank_lip]
    exact add_le_add hQlip le_rfl
  · simpa only [PolynomialPatch.padRank_value] using hQscore

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

theorem finite_model_test_difference_weighted
    {V I : Type*} [AddCommGroup V] [Module ℂ V] [Fintype I]
    (A B : V →ₗ[ℂ] ℂ) (v e : V) (J : I → V) (c : I → ℂ)
    (hmodel : v = (∑ i, c i • J i) + e) :
    ‖A v - B v‖ ≤ (∑ i, ‖c i‖ * ‖A (J i) - B (J i)‖) + ‖A e‖ + ‖B e‖ := by
  have hid : A v - B v = (∑ i, c i * (A (J i) - B (J i))) + (A e - B e) := by
    rw [hmodel, map_add, map_add, map_sum, map_sum]
    simp only [map_smul, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    abel
  rw [hid]
  have hsum : ‖∑ i, c i * (A (J i) - B (J i))‖ ≤
      ∑ i, ‖c i‖ * ‖A (J i) - B (J i)‖ := by
    simpa only [norm_mul] using norm_sum_le Finset.univ (fun i => c i * (A (J i) - B (J i)))
  exact (norm_add_le _ _).trans ((add_le_add hsum (norm_sub_le _ _)).trans_eq (by ring))

theorem exists_productive_averaged_model_transfer
    {H V I : Type*} [Fintype H] [AddCommGroup V] [Module ℂ V] [Fintype I]
    (law : FiniteProbabilityWeights H) (productive : Finset H)
    (A B : H → V →ₗ[ℂ] ℂ) (v e : V) (J : I → V) (c : I → ℂ)
    (hmodel : v = (∑ i, c i • J i) + e) {τ ρ : ℝ}
    (hτ : 0 < τ) (hρ : 0 < ρ) (hmass : τ ≤ law.mass productive)
    (hmean : law.mean (fun h =>
      (∑ i, ‖c i‖ * ‖A h (J i) - B h (J i)‖) + ‖A h e‖ + ‖B h e‖) ≤ τ * ρ / 8)
    (hscore : ∀ h ∈ productive, ρ ≤ (B h v).re) :
    ∃ h ∈ productive, ρ / 2 ≤ (A h v).re := by
  let err := fun h => (∑ i, ‖c i‖ * ‖A h (J i) - B h (J i)‖) + ‖A h e‖ + ‖B h e‖
  have herr : ∀ h, 0 ≤ err h := by intro h; dsimp only [err]; positivity
  obtain ⟨h, hp, _, he⟩ := exists_productive_good_path law productive ∅ err
    hτ (show 0 < ρ / 2 by positivity) herr hmass
    (by simp only [FiniteProbabilityWeights.mass, Finset.sum_empty]; positivity)
    (by dsimp only [err]; convert hmean using 1; ring)
  refine ⟨h, hp, ?_⟩
  have hd := (finite_model_test_difference_weighted (A h) (B h) v e J c hmodel).trans he
  have hre := (neg_le_abs ((A h v - B h v).re)).trans ((Complex.abs_re_le_norm _).trans hd)
  simp only [Complex.sub_re] at hre
  linarith [hscore h hp]

theorem exists_averaged_buffered_score
    {H Ω U I : Type*} [Fintype H] [Fintype Ω] [Fintype U] [Fintype I] {m : ℕ}
    (law : FiniteProbabilityWeights H) (productive : Finset H)
    (χ : PatchKernel m) (x : Ω → Fin m → ℝ)
    (T : Ω → (Fin m → ℤ) → ℝ) (G : H → Ω → (Fin m → ℤ) → ℝ)
    (f : Ω → ℝ) (lam : ℝ) (ψ : H → U → Ω)
    (e : Ω → ℂ) (J : I → Ω → ℂ) (c : I → ℂ)
    (hmodel : (fun u => (bufferedScalarScore χ x T f lam u : ℂ)) =
      (∑ i, c i • J i) + e) {τ ρ : ℝ}
    (hτ : 0 < τ) (hρ : 0 < ρ) (hmass : τ ≤ law.mass productive)
    (hmean : law.mean (fun h =>
      (∑ i, ‖c i‖ * ‖(𝔼 u, (G h u (nearestIntegerLift (x u)) : ℂ) * J i u) -
        (𝔼 a, J i (ψ h a))‖) +
      ‖𝔼 u, (G h u (nearestIntegerLift (x u)) : ℂ) * e u‖ +
      ‖𝔼 a, e (ψ h a)‖) ≤ τ * ρ / 8)
    (hscore : ∀ h ∈ productive, ρ ≤ 𝔼 a, bufferedScalarScore χ x T f lam (ψ h a)) :
    ∃ h ∈ productive, ρ / 2 ≤ 𝔼 u, (f u - lam) * ∑' b,
      χ.value (fun i => x u i - (b i : ℝ)) * G h u b * T u b := by
  let A := fun h => finiteWeightedTest id (fun u => (G h u (nearestIntegerLift (x u)) : ℂ))
  let B := fun h => finiteWeightedTest (ψ h) (fun _ => (1 : ℂ))
  have hmean' : law.mean (fun h => (∑ i, ‖c i‖ * ‖A h (J i) - B h (J i)‖) +
      ‖A h e‖ + ‖B h e‖) ≤ τ * ρ / 8 := by
    simpa only [A, B, finiteWeightedTest, LinearMap.coe_mk, AddHom.coe_mk, id_eq, one_mul] using hmean
  have hscore' : ∀ h ∈ productive, ρ ≤ (B h (fun u => (bufferedScalarScore χ x T f lam u : ℂ))).re := by
    intro h hh
    simpa only [B, ← Complex.ofReal_one, finiteWeightedTest_real, one_mul] using hscore h hh
  obtain ⟨h, hh, hs⟩ := exists_productive_averaged_model_transfer law productive A B
    _ e J c hmodel hτ hρ hmass hmean' hscore'
  refine ⟨h, hh, ?_⟩
  simpa only [A, finiteWeightedTest_real, id_eq, bufferedScalarScore_weighted] using hs

open MvPolynomial
open scoped NNReal

theorem exists_averaged_modeled_discounted_patch
    {H σ Ω U I : Type*} [Fintype H] [Fintype Ω] [Fintype U] [Fintype I]
    {s d E m : ℕ} (law : FiniteProbabilityWeights H) (productive : Finset H)
    (w : Fin d → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (P : Fin d → MvPolynomial σ ℝ) (hP : ∀ j, P j ∈ weightedSupportLE (fun _ : σ => 1) (w j))
    (p : Fin m → ℕ) (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (χ : PatchKernel m) (F : H → (Fin m → ℤ) → (Fin m → ℝ) → ℝ)
    (L C : ℝ≥0) (hC : 1 ≤ C)
    (hF : ∀ h ∈ productive, ∀ β, LipschitzWith L (F h β))
    (hFbound : ∀ h ∈ productive, ∀ β y, F h β y ∈ Set.Icc (0 : ℝ) C)
    (M : Fin m → Fin d → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (hinvariant : ∀ h ∈ productive, ∀ c k, F h (recoveredIntegerLift M c k) = F h c)
    (q : ℕ) (hq : 8 ≤ q) (hmesh : 16 * (K : ℝ) ≤ q)
    (t : Ω → σ → ℝ) (f : Ω → ℝ) (G : H → Ω → (Fin m → ℤ) → ℝ) {lam δ ε : ℝ}
    (hf : ∀ u, 0 ≤ f u) (hlam : 0 ≤ lam) (hδ : 0 ≤ δ)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hlower : ∀ h ∈ productive, ∀ u β, (1 - δ) *
      F h β (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)) ≤ G h u β)
    (hupper : ∀ h ∈ productive, ∀ u β, G h u β ≤ (1 + δ) *
      F h β (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)))
    (ψ : H → U → Ω) (e : Ω → ℂ) (J : I → Ω → ℂ) (c : I → ℂ)
    (hmodel : (fun u => (bufferedScalarScore χ
      (fun u => realIntegerMatrix M (fun j => aeval (t u) (P j)))
      (fun u b => B.value (Sum.elim (t u) (fun i => (b i : ℝ)))) f lam u : ℂ)) =
        (∑ i, c i • J i) + e)
    {τ ρ : ℝ} (hτ : 0 < τ) (hρ : 0 < ρ) (hmass : τ ≤ law.mass productive)
    (hmean : law.mean (fun h =>
      (∑ i, ‖c i‖ * ‖(𝔼 u, (G h u (nearestIntegerLift
        (realIntegerMatrix M (fun j => aeval (t u) (P j)))) : ℂ) * J i u) -
        (𝔼 a, J i (ψ h a))‖) +
      ‖𝔼 u, (G h u (nearestIntegerLift
        (realIntegerMatrix M (fun j => aeval (t u) (P j)))) : ℂ) * e u‖ +
      ‖𝔼 a, e (ψ h a)‖) ≤ τ * ρ / 8)
    (hscore : ∀ h ∈ productive, ρ ≤ 𝔼 a, bufferedScalarScore χ
      (fun u => realIntegerMatrix M (fun j => aeval (t u) (P j)))
      (fun u b => B.value (Sum.elim (t u) (fun i => (b i : ℝ)))) f lam (ψ h a)) :
    ∃ Q : PolynomialPatch σ s (d + E),
      Q.kernel.lip ≤ (q : ℝ≥0) * (2 * (q : ℝ≥0) ^ d + 1) +
        (χ.lip + L / C) * K + B.kernel.lip ∧
      (ρ / 2) / ((1 + δ) * (C : ℝ) * (q : ℝ) ^ d) ≤
        𝔼 u, (f u - (1 - ε) * lam) * Q.value (t u) := by
  obtain ⟨h, hh, hs⟩ := exists_averaged_buffered_score law productive χ
    (fun u => realIntegerMatrix M (fun j => aeval (t u) (P j)))
    (fun u b => B.value (Sum.elim (t u) (fun i => (b i : ℝ)))) G
    f lam ψ e J c hmodel hτ hρ hmass hmean hscore
  exact exists_discounted_recovered_patch w hw hws hmono P hP p B χ (F h) L C hC
    (hF h hh) (hFbound h hh) M K hM hweight (hinvariant h hh) q hq hmesh
    t f (G h) hf hlam hδ hdiscount (hlower h hh) (hupper h hh) hs

end Erdos3

end

end OAI
