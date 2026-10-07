import OAI.Combinatorics.Progressions.Lattices.ScalarResidueInteriorCell

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def residueCellPosition {I : Type*} (L N K : ℕ)
    (m : Option I → ℕ) (res : ∀ i, ZMod (m i))
    (k : Option I → Fin K) (t : Option I → Fin N) : Option I → ℝ :=
  fun i => progressionCellCorner (fun _ => N) (paddedResidueOffset L m res)
    (paddedResidueStep L m) k i + paddedResidueStep L m i * (t i).val

theorem scalarCubeResidue_supported_weight_cell (I : Type*) [Fintype I] [DecidableEq I]
    (L M N K : ℕ) (hL : 0 < L) (hN : 0 < N) (hK : 0 < K)
    (hcover : 2 * L ≤ K * N) (hupper : K * N ≤ 4 * L)
    (m : Option I → ℕ) (res : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L)
    (w : (Option I → ℝ) → ℝ) {Q : ℝ≥0} (hLip : LipschitzWith Q w)
    {δ η ζ B : ℝ} (hδ : 0 ≤ δ) (hη : 0 < η) (hB : 0 < B)
    (hmesh : ∀ i, |paddedResidueStep L m i| * N ≤ δ)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B)
    (hsupport : Function.support w ⊆ halfOpenScalarCubeDomain I)
    (hsafe : ∀ x, 0 < w x → ∀ y, dist y x ≤ δ → y ∈ scalarCubeDomain I)
    (herror : paddedResidueDensityCap I M * (Q * δ + B * η) ≤ ζ)
    (F : (Option I → ℝ) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    (hbias : ζ ≤ ‖(scalarCubeResidueWeights I L M hL m res hm hmM hsize).complexMean
      (fun z => (w (fun i => (z i : ℝ) / L) : ℂ) * F (fun i => (z i : ℝ) / L))‖) :
    ∃ k : Option I → Fin K,
      (∀ t : Option I → Fin N, residueCellPosition L N K m res k t ∈ scalarCubeDomain I) ∧
      η ≤ ‖𝔼 t : Option I → Fin N, F (residueCellPosition L N K m res k t)‖ := by
  have hcap : 0 < paddedResidueDensityCap I M := by
    exact mul_pos (by positivity)
      (scalarCubeResidueDensityCap_pos I M ((hm none).trans_le (hmM none)))
  have hpad := scalarCubeResidueWeights_padded_bias I L M (K * N) hL hcover hupper
    m res hm hmM hsize w hsupport F hbias
  have hthreshold : Q * δ + B * η ≤ ζ / paddedResidueDensityCap I M := by
    apply (le_div_iff₀ hcap).mpr
    nlinarith
  have hpad' := hthreshold.trans hpad
  obtain ⟨k, hinside, hphase⟩ := exists_interior_progression_cell
    (fun _ : Option I => K) (fun _ => N) (fun _ => hK) (fun _ => hN)
    (paddedResidueOffset L m res) (paddedResidueStep L m) w (scalarCubeDomain I)
    hLip hδ hB (show (Q : ℝ) * δ < Q * δ + B * η by nlinarith)
    hmesh hw hsafe
    (fun x => F (fun i => paddedResidueOffset L m res i + paddedResidueStep L m i * (x i).val))
    (fun x => hF _) hpad'
  refine ⟨k, hinside, ?_⟩
  have he (t : Option I → Fin N) := finiteRectangleRefinement_affine
    (fun _ : Option I => K) (fun _ => N) (paddedResidueOffset L m res) (paddedResidueStep L m) k t
  have hmean :
      (𝔼 t : Option I → Fin N, F (fun i => paddedResidueOffset L m res i +
        paddedResidueStep L m i *
          (finiteRectangleRefinement (fun _ : Option I => K) (fun _ => N) (k, t) i).val)) =
      𝔼 t : Option I → Fin N, F (residueCellPosition L N K m res k t) := by
    apply Finset.expect_congr rfl
    intro t _
    exact congrArg F (he t)
  rw [hmean] at hphase
  simpa only [add_sub_cancel_left, mul_div_cancel_left₀ _ hB.ne'] using hphase

end Erdos3

end

section

namespace Erdos3

def residueCellIntegerPoint {I : Type*} (L N K : ℕ)
    (m : Option I → ℕ) (res : ∀ i, ZMod (m i))
    (k : Option I → Fin K) (t : Option I → Fin N) : Option I → ℤ :=
  scalarResidueGridPoint m res (fun i => (N : ℤ) * (k i).val + (t i).val - L)

theorem residueCellIntegerPoint_normalized {I : Type*} (L N K : ℕ)
    (m : Option I → ℕ) (res : ∀ i, ZMod (m i))
    (k : Option I → Fin K) (t : Option I → Fin N) :
    (fun i => (residueCellIntegerPoint L N K m res k t i : ℝ) / L) =
      residueCellPosition L N K m res k t := by
  funext i
  simp only [residueCellIntegerPoint, scalarResidueGridPoint, residueCellPosition,
    progressionCellCorner, paddedResidueOffset, paddedResidueStep,
    Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  ring

theorem residueCellIntegerPoint_residue {I : Type*} (L N K : ℕ)
    (m : Option I → ℕ) (res : ∀ i, ZMod (m i)) (hm : ∀ i, 0 < m i)
    (k : Option I → Fin K) (t : Option I → Fin N) (i : Option I) :
    (residueCellIntegerPoint L N K m res k t i : ZMod (m i)) = res i :=
  scalarResidueGridPoint_residue m res hm _ i

theorem residueCellIntegerPoint_is_cube {I : Type*} [Fintype I] [DecidableEq I]
    {L N K : ℕ} (hL : 0 < L) (m : Option I → ℕ) (res : ∀ i, ZMod (m i))
    (k : Option I → Fin K) (t : Option I → Fin N)
    (ht : residueCellPosition L N K m res k t ∈ scalarCubeDomain I) :
    IntegerScalarCube L (residueCellIntegerPoint L N K m res k t) := by
  apply (integerScalarCube_iff_normalized hL _).mpr
  rw [residueCellIntegerPoint_normalized]
  exact scalarCubeDomain_subset_halfOpen I ht

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem scalarCubeResidue_weighted_interior_cell (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (res : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L)
    (hsmall : scalarCubeGridBoundaryConstant I * ((M : ℝ) / L) <
      volume.real (scalarCubeDomain I))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {r : ℝ≥0} (hr : 0 < r)
    (w : (Option I → ℝ) → ℝ) {B T : ℝ≥0} (hB : 0 < B)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    {δ η ζ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 < η)
    (hlarge : 2 * (M : ℝ) ≤ δ * L)
    (hmargin : ((Fintype.card I : ℝ) + 1) * δ < r)
    (herror : B * scalarCubeResidueCutoffBudget I A r L M +
      paddedResidueDensityCap I M *
        (((T : ℝ) + B * scalarCubeCutoffLipschitzConstant I A r) * δ + B * η) ≤ ζ)
    (F : (Option I → ℝ) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    (hbias : ζ ≤ ‖(scalarCubeResidueWeights I L M hL m res hm hmM hsize).complexMean
      (fun z => (w (fun i => (z i : ℝ) / L) : ℂ) * F (fun i => (z i : ℝ) / L))‖) :
    let N := residueCellLength δ L M
    let K := residueCellCount L N
    ∃ k : Option I → Fin K,
      (∀ t : Option I → Fin N, residueCellPosition L N K m res k t ∈ scalarCubeDomain I) ∧
      η ≤ ‖𝔼 t : Option I → Fin N, F (residueCellPosition L N K m res k t)‖ := by
  let N := residueCellLength δ L M
  let K := residueCellCount L N
  have hM : 0 < M := (hm none).trans_le (hmM none)
  have hN := residueCellLength_bounds hδ hδ1 hL hM hlarge
  have hP : 2 * L ≤ K * N ∧ K * N ≤ 3 * L := residueCellCount_padding hN.1 hN.2.1
  let b := inequalityBoundaryCutoff (fun _ : Bool × Finset I => (r : ℝ)) scalarCubeFace
  let g := fun x => w x * b x
  have hb (x) : b x ∈ Set.Icc (0 : ℝ) 1 := inequalityBoundaryCutoff_range _ _ x
  have hwabs (x) : |w x| ≤ B := by rw [abs_of_nonneg (hw x).1]; exact (hw x).2
  have hbabs (x) : |b x| ≤ 1 := by rw [abs_of_nonneg (hb x).1]; exact (hb x).2
  have hglip : LipschitzWith (T + B * scalarCubeCutoffLipschitzConstant I A r) g :=
    bounded_weight_cutoff_lipschitz w b hwabs hbabs hLip (scalarCubeBoundaryCutoff_lipschitz I A hA hr)
  have hg (x) : 0 ≤ g x ∧ g x ≤ B :=
    ⟨mul_nonneg (hw x).1 (hb x).1,
      (mul_le_of_le_one_right (hw x).1 (hb x).2).trans (hw x).2⟩
  have hsupport : Function.support g ⊆ halfOpenScalarCubeDomain I := by
    intro x hx
    exact scalarCubeDomain_subset_halfOpen I
      (scalarCubeBoundaryCutoff_tsupport_domain I (show (0 : ℝ) < r from hr)
        (tsupport_mul_subset_right (subset_closure hx)))
  have hsafe := scalarCube_cutoff_safe (show (0 : ℝ) < r from hr) hmargin g tsupport_mul_subset_right
  have hcut := FiniteProbabilityWeights.weighted_cutoff_bias_lower
    (scalarCubeResidueWeights I L M hL m res hm hmM hsize)
    (fun z => b (fun i => (z i : ℝ) / L)) (fun z => w (fun i => (z i : ℝ) / L))
    (fun z => F (fun i => (z i : ℝ) / L)) B.coe_nonneg
    (fun z => hb _) (fun z => hwabs _) (fun z => hF _) hbias
    (scalarCubeResidueCutoff_loss I L M hL m res hm hmM hsize hsmall A hA hr)
  apply scalarCubeResidue_supported_weight_cell I L M N K hL hN.1
    (residueCellCount_pos L N) hP.1 (by omega) m res hm hmM hsize g hglip
    hδ.le hη (show (0 : ℝ) < B from hB)
    (fun i => residueCellLength_stride_mesh hδ hδ1 hL hM hlarge (hmM i))
    hg hsupport hsafe _ F hF hcut
  simp only [NNReal.coe_add, NNReal.coe_mul]
  linarith

end Erdos3

end

end OAI
