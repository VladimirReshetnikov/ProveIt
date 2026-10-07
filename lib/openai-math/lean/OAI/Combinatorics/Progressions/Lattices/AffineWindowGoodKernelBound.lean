import OAI.Combinatorics.Progressions.Estimates.CubeTranslation
import OAI.Combinatorics.Progressions.Estimates.ScalarCubeRootTranslation
import OAI.Combinatorics.Progressions.Linear.WindowGoodKernelBound

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def integerStrideHom (m : ℤ) : ℤ →+ ℤ where
  toFun x := m * x
  map_zero' := mul_zero m
  map_add' := mul_add m

theorem integerStride_reflectsPairSums (m : ℤ) (hm : m ≠ 0) (Q : Set ℤ) :
    ReflectsPairSums (integerStrideHom m) Q := by
  intro a _ b _ c _ d _ h
  apply mul_left_cancel₀ hm
  simpa only [integerStrideHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, mul_add] using h

noncomputable def integerProgressionSupport (c m : ℤ) (L : ℕ) : Finset ℤ :=
  translateSupport c ((Finset.Ico (0 : ℤ) (L : ℤ)).image (integerStrideHom m))

noncomputable def supportedIntervalProgressionEquiv (q L : ℕ) (c m : ℤ) (hm : m ≠ 0) :
    SupportedCube q (Set.Ico (0 : ℤ) (L : ℤ)) ≃
      SupportedCube q (integerProgressionSupport c m L : Set ℤ) := by
  let e := supportedCubeEquiv (integerStride_reflectsPairSums m hm (Set.Ico 0 (L : ℤ))) q
  let e' : SupportedCube q (integerStrideHom m '' Set.Ico (0 : ℤ) (L : ℤ)) ≃
      SupportedCube q (((Finset.Ico (0 : ℤ) (L : ℤ)).image (integerStrideHom m)) : Set ℤ) :=
    Equiv.subtypeEquivRight (fun p => by simp only [Finset.coe_image, Finset.coe_Ico])
  exact (e.trans e').trans (supportedCubeTranslateEquiv q _ c)

theorem supportedIntervalProgressionEquiv_value (q L : ℕ) (c m : ℤ) (hm : m ≠ 0)
    (p : SupportedCube q (Set.Ico (0 : ℤ) (L : ℤ))) :
    (supportedIntervalProgressionEquiv q L c m hm p).val =
      (fun i => m * p.val.1 i, c + m * p.val.2) := rfl

theorem integerScalarCubeWeights_progression_mean (q L : ℕ) (hL : 0 < L)
    (c m : ℤ) (hm : m ≠ 0) (f : ((Fin q → ℤ) × ℤ) → ℝ) :
    (integerScalarCubeWeights (Fin q) L hL).mean
        (fun x => f (fun i => m * (x (some i) : ℤ), c + m * (x none : ℤ))) =
      𝔼 p : SupportedCube q (integerProgressionSupport c m L : Set ℤ), f p.val := by
  calc
    _ = 𝔼 p : SupportedCube q (Set.Ico (0 : ℤ) (L : ℤ)),
        f (fun i => m * p.val.1 i, c + m * p.val.2) :=
      integerScalarCubeWeights_supported_mean q L hL
        (fun p => f (fun i => m * p.1 i, c + m * p.2))
    _ = _ := Fintype.expect_equiv (supportedIntervalProgressionEquiv q L c m hm) _ _
      (fun _ => rfl)

end Erdos3

end

section

namespace Erdos3

abbrev TranslatedResidueSupportedCube (q K : ℕ) (c : ℤ) (m : Option (Fin q) → ℕ)
    (r : ∀ i, ZMod (m i)) :=
  {p : SupportedCube q (Set.Ico c (c + K)) //
    ∀ i, ((supportedCubeCoordinates p.val i : ℤ) : ZMod (m i)) = r i}

noncomputable def shiftedScalarCubeResidueEquiv (q K : ℕ) (c : ℤ)
    (m : Option (Fin q) → ℕ) (r : ∀ i, ZMod (m i)) :
    ↥((integerScalarCubeSet (Fin q) K) ∩
      scalarCubeResidueSet (Fin q) K m (shiftScalarCubeResidues c m r)) ≃
      TranslatedResidueSupportedCube q K c m r := by
  let e := shiftedScalarCubeEquiv q K c
  refine {
    toFun := fun x => ⟨e ⟨x.val, (Finset.mem_inter.mp x.property).1⟩, ?_⟩
    invFun := fun y => ⟨(e.symm y.val).val, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · change ∀ i, ((supportedCubeCoordinates (shiftedScalarCubeEquiv q K c
      ⟨x.val, (Finset.mem_inter.mp x.property).1⟩).val i : ℤ) : ZMod (m i)) = r i
    rw [shiftedScalarCubeEquiv_coordinates]
    exact (shiftScalarCube_residues_iff c m r _).mpr
      ((mem_scalarCubeResidueSet K m (shiftScalarCubeResidues c m r) x.val).mp
        (Finset.mem_inter.mp x.property).2)
  · refine Finset.mem_inter.mpr ⟨(e.symm y.val).property, ?_⟩
    apply (mem_scalarCubeResidueSet K m (shiftScalarCubeResidues c m r) _).mpr
    apply (shiftScalarCube_residues_iff c m r _).mp
    rw [← shiftedScalarCubeEquiv_coordinates]
    simpa only [e, Equiv.apply_symm_apply] using y.property
  · intro x
    apply Subtype.ext
    change (e.symm (e ⟨x.val, (Finset.mem_inter.mp x.property).1⟩)).val = x.val
    rw [e.symm_apply_apply]
  · intro y
    apply Subtype.ext
    change e (e.symm y.val) = y.val
    exact e.apply_symm_apply y.val

theorem shiftedScalarCubeResidueEquiv_coordinates (q K : ℕ) (c : ℤ)
    (m : Option (Fin q) → ℕ) (r : ∀ i, ZMod (m i))
    (x : ↥((integerScalarCubeSet (Fin q) K) ∩
      scalarCubeResidueSet (Fin q) K m (shiftScalarCubeResidues c m r))) :
    supportedCubeCoordinates (shiftedScalarCubeResidueEquiv q K c m r x).val.val =
      shiftScalarCube c (fun i => (x.val i : ℤ)) := by
  funext i
  cases i <;> rfl

end Erdos3

end

section

namespace Erdos3

theorem mem_integerProgressionSupport_iff (c : ℤ) (m H : ℕ) (hm : 0 < m) (x : ℤ) :
    x ∈ integerProgressionSupport c (m : ℤ) H ↔
      c ≤ x ∧ x < c + (m * H : ℕ) ∧ (x : ZMod m) = (c : ZMod m) := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  rw [integerProgressionSupport, mem_translateSupport, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, he⟩
    have hy' := Finset.mem_Ico.mp hy
    change (m : ℤ) * y = x - c at he
    have hx : x = c + (m : ℤ) * y := by omega
    constructor
    · nlinarith
    constructor
    · push_cast
      nlinarith
    · rw [hx]
      simp
  · rintro ⟨hlo, hhi, hr⟩
    have hz : ((x - c : ℤ) : ZMod m) = 0 := by simp [hr]
    obtain ⟨y, hy⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (x - c) m).mp hz
    have hy0 : 0 ≤ y := by nlinarith
    have hyH : y < H := by push_cast at hhi; nlinarith
    exact ⟨y, Finset.mem_Ico.mpr ⟨hy0, hyH⟩, hy.symm⟩

def progressionCubeResidues (q m : ℕ) (c : ℤ) : Option (Fin q) → ZMod m
  | none => (c : ZMod m)
  | some _ => 0

noncomputable def progressionResidueSupportedCubeEquiv (q m H : ℕ) (c : ℤ) (hm : 0 < m) :
    SupportedCube q (integerProgressionSupport c (m : ℤ) H : Set ℤ) ≃
      TranslatedResidueSupportedCube q (m * H) c (fun _ => m) (progressionCubeResidues q m c) where
  toFun p := by
    let p' : SupportedCube q (Set.Ico c (c + (m * H : ℕ))) := ⟨p.val, fun ω => by
      have h := (mem_integerProgressionSupport_iff c m H hm _).mp (p.property ω)
      exact ⟨h.1, h.2.1⟩⟩
    refine ⟨p', ?_⟩
    intro i
    cases i with
    | none => exact ((mem_integerProgressionSupport_iff c m H hm _).mp p.base_mem).2.2
    | some i =>
      have h0 := ((mem_integerProgressionSupport_iff c m H hm _).mp p.base_mem).2.2
      have hi := ((mem_integerProgressionSupport_iff c m H hm _).mp (p.axis_mem i)).2.2
      change (p.val.1 i : ZMod m) = 0
      push_cast at hi
      rw [h0] at hi
      exact add_left_cancel (hi.trans (add_zero _).symm)
  invFun p := by
    refine ⟨p.val.val, fun ω => ?_⟩
    apply (mem_integerProgressionSupport_iff c m H hm _).mpr
    have h := p.val.property ω
    refine ⟨h.1, h.2, ?_⟩
    have h0 : (p.val.val.2 : ZMod m) = (c : ZMod m) := p.property none
    have hi (i : Fin q) : (p.val.val.1 i : ZMod m) = 0 := p.property (some i)
    simp only [Int.cast_add, h0, cubeShift, Int.cast_sum, apply_ite, hi, Int.cast_zero, ite_self,
      Finset.sum_const_zero, add_zero]
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by apply Subtype.ext; apply Subtype.ext; rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def affineScalarCubeWindowWeights (I : Type*) [Fintype I] [DecidableEq I]
    (L K M D : ℕ) (c : ℤ) (hL : 0 < L) (hKL : K ≤ L) (hDK : L ≤ D * K)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ K) :
    FiniteProbabilityWeights (IntegerScalarCubeBox I L) :=
  scalarCubeWindowWeights I L K M D hL hKL hDK m (shiftScalarCubeResidues c m r) hm hmM hsize

theorem affineScalarCubeWindowWeights_supported_mean (q L K M D : ℕ) (c : ℤ)
    (hL : 0 < L) (hKL : K ≤ L) (hDK : L ≤ D * K)
    (m : Option (Fin q) → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card (Fin q) + 1) * M ≤ K) (f : (Option (Fin q) → ℤ) → ℝ) :
    (affineScalarCubeWindowWeights (Fin q) L K M D c hL hKL hDK m r hm hmM hsize).mean
        (fun x => f (shiftScalarCube c (fun i => (x i : ℤ)))) =
      𝔼 p : TranslatedResidueSupportedCube q K c m r, f (supportedCubeCoordinates p.val.val) := by
  classical
  have hM : 0 < M := (hm none).trans_le (hmM none)
  have hK : 0 < K := (Nat.mul_pos (Nat.succ_pos _) hM).trans_le hsize
  unfold affineScalarCubeWindowWeights
  rw [scalarCubeWindowWeights_small_mean (Fin q) L K M D hL hK hKL hDK,
    scalarCubeResidueWeights_mean]
  apply Fintype.expect_equiv (shiftedScalarCubeResidueEquiv q K c m r)
  intro x
  rw [shiftedScalarCubeResidueEquiv_coordinates]
  rfl

theorem affineScalarCubeWindowWeights_weight_le (I : Type*) [Fintype I] [DecidableEq I]
    (L K M D : ℕ) (c : ℤ) (hL : 0 < L) (hKL : K ≤ L) (hDK : L ≤ D * K)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ K) (x : IntegerScalarCubeBox I L) :
    (affineScalarCubeWindowWeights I L K M D c hL hKL hDK m r hm hmM hsize).weight x ≤
      scalarCubeResidueDensityCap I (M * D) * (integerScalarCubeWeights I L hL).weight x :=
  scalarCubeWindowWeights_weight_le I L K M D hL hKL hDK m (shiftScalarCubeResidues c m r) hm hmM hsize x

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem affineScalarCubeWindowWeights_progression_mean (q L m H M D : ℕ) (c : ℤ)
    (hL : 0 < L) (hm : 0 < m) (hmM : m ≤ M) (hKL : m * H ≤ L) (hDK : L ≤ D * (m * H))
    (hsize : (Fintype.card (Fin q) + 1) * M ≤ m * H) (f : (Option (Fin q) → ℤ) → ℝ) :
    (affineScalarCubeWindowWeights (Fin q) L (m * H) M D c hL hKL hDK
      (fun _ => m) (progressionCubeResidues q m c) (fun _ => hm) (fun _ => hmM) hsize).mean
        (fun x => f (shiftScalarCube c (fun i => (x i : ℤ)))) =
      𝔼 p : SupportedCube q (integerProgressionSupport c (m : ℤ) H : Set ℤ),
        f (supportedCubeCoordinates p.val) := by
  rw [affineScalarCubeWindowWeights_supported_mean]
  exact (Fintype.expect_equiv (progressionResidueSupportedCubeEquiv q m H c hm) _ _
    (fun _ => rfl)).symm

end Erdos3

end

section

namespace Erdos3

theorem scalarKernelCutoff_window_size (I J : Type*) [Fintype I] [Fintype J]
    {M D L K : ℕ} {η : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η)
    (hlarge : scalarKernelCutoff I J M D η ≤ L) (hDK : L ≤ D * K) :
    (Fintype.card I + 1) * M ≤ K :=
  scalarCubeWindow_size hD ((scalarKernelCutoff_bounds I J hM hD hη).2.2.1.trans hlarge) hDK

theorem affineKernel_explicit_probability_le (I J : Type*)
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    (hJ : Fintype.card J = Fintype.card I * (Fintype.card I + 2)) (s : I ↪ J)
    {M D L : ℕ} {η : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η) (hL : 0 < L)
    (hlarge : scalarKernelCutoff I J M D η ≤ L) (K : J → ℕ)
    (hKL : ∀ j, K j ≤ L) (hDK : ∀ j, L ≤ D * K j) (c : J → ℤ)
    (m : J → Option I → ℕ) (r : ∀ j i, ZMod (m j i))
    (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M) :
    (FiniteProbabilityWeights.pi (fun j =>
      affineScalarCubeWindowWeights I L (K j) M D (c j) hL (hKL j) (hDK j)
        (m j) (r j) (hm j) (hmM j) (scalarKernelCutoff_window_size I J hM hD hη hlarge (hDK j)))).eventProbability
      (fun x => ¬ GoodScalarKernelTuple s (1 / (scalarKernelCutoff I J M D η : ℝ))
        (scalarKernelCutoff I J M D η) x) ≤ η := by
  let C := scalarKernelConditioningConstant I J M D
  have hC : 0 < C := scalarKernelConditioningConstant_pos I J hM hD
  have h := scalarCubeWindow_pi_eventProbability_le I J L M D K hL hKL hDK m
    (fun j => shiftScalarCubeResidues (c j) (m j) (r j)) hm hmM
    (fun j => scalarKernelCutoff_window_size I J hM hD hη hlarge (hDK j))
    (fun x => ¬ GoodScalarKernelTuple s (1 / (scalarKernelCutoff I J M D η : ℝ))
      (scalarKernelCutoff I J M D η) x)
  apply h.trans
  calc
    _ ≤ C * scalarKernelAdjustedAccuracy I J M D η := mul_le_mul_of_nonneg_left
      (scalarKernel_explicit_probability_le I J hJ s hM hD hη hL hlarge) hC.le
    _ = η := by
      change C * (η / C) = η
      field_simp

end Erdos3

end

section

namespace Erdos3

theorem exists_affine_window_good_scalar_kernel_bound (I J : Type*)
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    (hJ : Fintype.card J = Fintype.card I * (Fintype.card I + 2)) :
    ∃ s : I ↪ J, ∀ (M D : ℕ), 0 < M → ∀ hD : 0 < D, ∀ η : ℝ, 0 < η → ∃ B L₀ : ℕ,
      0 < B ∧ ∃ hsize : D * ((Fintype.card I + 1) * M) ≤ L₀,
      ∀ (L : ℕ) (hL : 0 < L) (hlarge : L₀ ≤ L) (K : J → ℕ)
        (hKL : ∀ j, K j ≤ L) (hDK : ∀ j, L ≤ D * K j) (c : J → ℤ)
        (m : J → Option I → ℕ) (r : ∀ j i, ZMod (m j i))
        (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M),
        (FiniteProbabilityWeights.pi (fun j =>
          affineScalarCubeWindowWeights I L (K j) M D (c j) hL (hKL j) (hDK j)
            (m j) (r j) (hm j) (hmM j)
            (scalarCubeWindow_size hD (hsize.trans hlarge) (hDK j)))).eventProbability
              (fun x => ¬ GoodScalarKernelTuple s (1 / (B : ℝ)) B x) ≤ η := by
  obtain ⟨s, hs⟩ := exists_window_good_scalar_kernel_bound I J hJ
  refine ⟨s, fun M D hM hD η hη => ?_⟩
  obtain ⟨B, L₀, hB, hsize, hprob⟩ := hs M D hM hD η hη
  refine ⟨B, L₀, hB, hsize, ?_⟩
  intro L hL hlarge K hKL hDK c m r hm hmM
  exact hprob L hL hlarge K hKL hDK m (fun j => shiftScalarCubeResidues (c j) (m j) (r j)) hm hmM

end Erdos3

end

end OAI
