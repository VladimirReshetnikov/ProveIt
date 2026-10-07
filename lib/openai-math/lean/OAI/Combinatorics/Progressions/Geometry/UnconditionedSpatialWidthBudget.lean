import OAI.Combinatorics.Progressions.Estimates.CenteredReferenceCap
import OAI.Combinatorics.Progressions.Estimates.SelectedPhysicalReferenceCap

namespace OAI

section

namespace Erdos3

theorem rectangularWeightIndices_zero_bound {I : Type*} [Fintype I]
    (W : I → ℝ) {z : I → ℤ} (hz : z ∈ rectangularWeightIndices 0 W 1) (i : I) :
    |(z i : ℝ)| ≤ W i := by
  classical
  have hi := Fintype.mem_piFinset.mp hz i
  change z i ∈ sampledWeightIndices 0 (W i) 1 at hi
  simp only [sampledWeightIndices, mul_one, zero_sub, zero_add, Finset.mem_Icc] at hi
  exact abs_le.mpr ⟨Int.ceil_le.mp hi.1, Int.le_floor.mp hi.2⟩

theorem integer_center_quarter_mem (N : ℕ) (hN : 4 ≤ N) (x : ℤ) (hx : 4*|x| ≤ (N : ℤ)) :
    0 ≤ (N / 2 : ℕ) + x ∧ (N / 2 : ℕ) + x < (N : ℤ) := by
  have hleft : -(N : ℤ) ≤ 4*x := by linarith [neg_abs_le x]
  have hright : 4*x ≤ (N : ℤ) := by linarith [le_abs_self x]
  omega

namespace BooleanCubeKernel

theorem centeredIntegerPhysicalSite_mem_box {K I : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    (root : K → ℤ) (N : I → ℕ) (hN : ∀ i, 4 ≤ N i) (W : Option K × I → ℝ)
    (hwidth : ∀ i, 4 * physicalSiteWidth root W i ≤ (N i : ℝ))
    {z : Option K × I → ℤ} (hz : z ∈ rectangularWeightIndices 0 W 1) :
    centeredIntegerPhysicalSite root N z ∈ integerBox N := by
  apply (mem_integerBox N _).mpr
  intro i
  have hb := integerPhysicalSite_abs_bound root W z (rectangularWeightIndices_zero_bound W hz) i
  have hr : 4 * |(integerPhysicalSite root z i : ℝ)| ≤ (N i : ℝ) := by linarith [hwidth i]
  have hi : 4 * |integerPhysicalSite root z i| ≤ (N i : ℤ) := by exact_mod_cast hr
  exact integer_center_quarter_mem (N i) (hN i) (integerPhysicalSite root z i) hi

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

theorem mem_rectangularWeightIndices_zero_iff {I : Type*} [Fintype I]
    (W : I → ℝ) (z : I → ℤ) :
    z ∈ rectangularWeightIndices 0 W 1 ↔ ∀ i, |(z i : ℝ)| ≤ W i := by
  classical
  constructor
  · exact fun hz => rectangularWeightIndices_zero_bound W hz
  · intro hz
    apply Fintype.mem_piFinset.mpr
    intro i
    change z i ∈ sampledWeightIndices 0 (W i) 1
    simp only [sampledWeightIndices, mul_one, zero_sub, zero_add, Finset.mem_Icc]
    exact ⟨Int.ceil_le.mpr (abs_le.mp (hz i)).1, Int.le_floor.mpr (abs_le.mp (hz i)).2⟩

theorem rectangularWeightIndices_zero_mono {I : Type*} [Fintype I]
    {V W : I → ℝ} (hVW : ∀ i, V i ≤ W i) :
    rectangularWeightIndices 0 V 1 ⊆ rectangularWeightIndices 0 W 1 := by
  intro z hz
  apply (mem_rectangularWeightIndices_zero_iff W z).mpr
  exact fun i => (rectangularWeightIndices_zero_bound V hz i).trans (hVW i)

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

theorem selectedResidueDensityPMF_centered_mem_box {K X : Type*}
    [Fintype K] [Fintype X] [DecidableEq X]
    (root : K → ℤ) (N : X → ℕ) (hN : ∀ i, 4 ≤ N i)
    (modulus : X → ℕ) (T : Finset (ColumnResiduePattern (Option K) X modulus))
    (W : Option K × X → ℝ) (hW : ∀ z, 0 < W z)
    (hfit : ∀ i, 4*physicalSiteWidth root W i ≤ (N i : ℝ))
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (D : (Option K × X → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus T W D)
    (z : Option K × X → ℤ)
    (hz : 0 < (selectedResidueDensityPMF modulus T W hW hZ D hD0 hD z).toReal) :
    centeredIntegerPhysicalSite root N z ∈ integerBox N := by
  apply centeredIntegerPhysicalSite_mem_box root N hN W hfit
  by_contra h
  exact (ne_of_gt hz) (selectedResidueDensityPMF_zero_off modulus T W hW hZ D hD0 hD z h)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem selectedResidue_trimmed_reference_compare {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (root : K → ℤ) (N R : I → ℕ) (hR : ∀ i, 2 * R i < N i)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern (Option K) I modulus))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hwidth : ∀ i, physicalSiteWidth root W i ≤ (R i : ℝ))
    (f : (I → ℤ) → ℂ) (hf : ∀ x ∈ integerBox N, ‖f x‖ ≤ 1) :
    ‖(𝔼 a ∈ trimmedIntegerBox N R,
        ∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ) *
          f (a + integerPhysicalSite root z)) - 𝔼 x ∈ integerBox N, f x‖ ≤
      2 * ∑ i, 2 * (R i : ℝ) / N i := by
  let p := selectedResidueFiniteLaw modulus T W hW hZ
  have hnoise (z : rectangularWeightIndices 0 W 1) (i : I) :
      |integerPhysicalSite root z.val i| ≤ (R i : ℤ) := by
    have h := (integerPhysicalSite_abs_bound root W z.val
      (rectangularWeightIndices_zero_bound W z.property) i).trans (hwidth i)
    exact_mod_cast h
  have h := p.translated_subset_mixture_compare (trimmedIntegerBox N R) (integerBox N)
    (trimmedIntegerBox_nonempty N R hR) (fun z a => a + integerPhysicalSite root z.val)
    (fun _ _ _ _ _ he => add_right_cancel he)
    (fun z _ ha => trimmedIntegerBox_add_mem N R (fun i => (hR i).le) ha _ (hnoise z)) f hf
  have hdef := trimmedIntegerBox_card_deficit N R
    (fun i => lt_of_le_of_lt (Nat.zero_le _) (hR i)) (fun i => (hR i).le)
  have hbound := h.trans (mul_le_mul_of_nonneg_left hdef (by norm_num : (0 : ℝ) ≤ 2))
  dsimp only [p] at hbound
  have he (a : I → ℤ) := selectedResidueFiniteLaw_complexMean modulus T W hW hZ
    (fun z => f (a + integerPhysicalSite root z))
  simpa only [he] using hbound

theorem selectedResidue_trimmed_comparison_transfer {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (root : K → ℤ) (N R : I → ℕ) (hR : ∀ i, 2 * R i < N i)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern (Option K) I modulus))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hwidth : ∀ i, physicalSiteWidth root W i ≤ (R i : ℝ))
    (f : (I → ℤ) → ℂ) (hf : ∀ x ∈ integerBox N, ‖f x‖ ≤ 1)
    (L : (I → ℤ) → ℂ) {ε : ℝ}
    (hL : ∀ a ∈ trimmedIntegerBox N R,
      ‖L a - ∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ) *
        f (a + integerPhysicalSite root z)‖ ≤ ε) :
    ‖(𝔼 a ∈ trimmedIntegerBox N R, L a) - 𝔼 x ∈ integerBox N, f x‖ ≤
      ε + 2 * ∑ i, 2 * (R i : ℝ) / N i := by
  have hlocal : ‖(𝔼 a ∈ trimmedIntegerBox N R, L a) -
      (𝔼 a ∈ trimmedIntegerBox N R,
        ∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ) *
          f (a + integerPhysicalSite root z))‖ ≤ ε := by
    rw [← Finset.expect_sub_distrib]
    exact (RCLike.norm_expect_le (K := ℂ)).trans
      (Finset.expect_le (trimmedIntegerBox_nonempty N R hR) hL)
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add hlocal (selectedResidue_trimmed_reference_compare
      root N R hR modulus T W hW hZ hwidth f hf))

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators

theorem shiftedSmoothProductMass_pos_of_scales {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 8*(probabilityProfileLipschitz : ℝ) ≤ S i) :
    0 < shiftedSmoothProductMass a S := by
  rw [shiftedSmoothProductMass_eq_prod a S (fun i => smoothSamplingScale_pos (hS i))]
  exact Finset.prod_pos (fun i _ => shiftedSmoothSampleSum_pos (a i) (hS i))

namespace BooleanCubeKernel

theorem exists_selectedResidue_physical_cap {K I : Type*} [Fintype K] [Fintype I]
    (root : K → ℤ) (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (T : Finset (ColumnResiduePattern (Option K) I modulus)) (hT : T.Nonempty)
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z) :
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z,
      ∀ y, ((selectedResidueSmoothPMF modulus T W hW hZ).map (physicalAffineSite root) y).toReal ≤
        ∏ i, 2*(modulus i : ℝ)/W (none,i) := by
  have hc (r : T) : 0 < shiftedSmoothProductMass
      (residueProfileCenter (columnResidueRepresentative modulus r.val) modulus) (residueProfileWidth modulus W) :=
    shiftedSmoothProductMass_pos_of_scales _ _ hscale
  have hZ := selectedResidueSmoothWeight_mass_pos modulus T hT W hW (fun r => by
    rw [← residueSmoothWeight_mass _ modulus hmodulus W hW]
    exact hc r)
  exact ⟨hZ, selectedResidueSmoothPMF_physical_cap root modulus hmodulus T hT W hW hZ hc
    (fun i => hscale (none,i))⟩

end BooleanCubeKernel

theorem spatialBaseCap_exp_bound {I : Type*} [Fintype I]
    (modulus : I → ℕ) (W H : I → ℝ) (hW : ∀ i, 0 < W i) (hH : ∀ i, 0 ≤ H i)
    {P ρ : ℝ} (hP : 0 ≤ P) (hρ : 0 < ρ) (hρP : ρ⁻¹ ≤ Real.exp P)
    (hI : (Fintype.card I : ℝ) ≤ P) (hmodulus : ∀ i, (modulus i : ℝ) ≤ Real.exp P)
    (hwidth : ∀ i, ρ*H i ≤ W i) :
    (∏ i, H i) * (∏ i, 2*(modulus i : ℝ)/W i) ≤ Real.exp (2*P^2+2*P) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hc : 2*Real.exp P/ρ ≤ Real.exp (2*P+2) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp 2 * Real.exp P * Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hp := pow_le_exp_mul_of_le_exp (by positivity) hc (by positivity) (Fintype.card I) hI
  exact (spatialBaseCap_volume_bound modulus W H hW hH hρ (Real.exp_nonneg P) hmodulus hwidth).trans
    (hp.trans_eq (by congr 1; ring))

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem exists_selected_reference_box_domination {K I : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    (root : K → ℤ) (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (T : Finset (ColumnResiduePattern (Option K) I modulus)) (hT : T.Nonempty)
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    (N : I → ℕ) (hN : ∀ i, 4 ≤ N i)
    (hfit : ∀ i, 4*physicalSiteWidth root W i ≤ (N i : ℝ))
    {S ρ : ℝ} (hS : 0 ≤ S) (hρ : 0 < ρ) (hmodulusS : ∀ i, (modulus i : ℝ) ≤ S)
    (hbase : ∀ i, ρ*(N i : ℝ) ≤ W (none,i)) :
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z,
      ∀ φ : (I → ℝ) → ℝ, (∀ x ∈ integerBox N, 0 ≤ φ (fun i => (x i : ℝ))) →
        (∑' z, (selectedResidueSmoothPMF modulus T W hW hZ z).toReal *
          φ ((fun i => (integerBoxCenter N i : ℝ)) + physicalAffineSite root z)) ≤
        (2*S/ρ)^Fintype.card I * (𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ))) := by
  obtain ⟨hZ, hp⟩ := exists_selectedResidue_physical_cap root modulus hmodulus T hT W hW hscale
  refine ⟨hZ, ?_⟩
  intro φ hφ
  let p := selectedResidueFiniteLaw modulus T W hW hZ
  let F : rectangularWeightIndices 0 W 1 → (I → ℤ) :=
    fun z => centeredIntegerPhysicalSite root N z.val
  let B := ∏ i, 2*(modulus i : ℝ)/W (none,i)
  have hB : 0 ≤ B := Finset.prod_nonneg (fun i _ =>
    div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (hW _).le)
  have hF (z : rectangularWeightIndices 0 W 1) : F z ∈ integerBox N :=
    centeredIntegerPhysicalSite_mem_box root N hN W hfit z.property
  have hpoint (y : I → ℤ) : p.mean (fun z => if F z = y then 1 else 0) ≤ B := by
    exact (selectedResidueFiniteLaw_mean modulus T W hW hZ
      (fun z => if centeredIntegerPhysicalSite root N z = y then 1 else 0)).trans_le
      ((pmf_map_toReal_indicator (selectedResidueSmoothPMF modulus T W hW hZ)
        (centeredIntegerPhysicalSite root N) y).symm.trans_le
        (pmf_centeredPhysicalSite_cap _ root N hB hp y))
  have hf := p.image_mean_le_uniform F (integerBox N) hF hpoint
    (fun x => φ (fun i => (x i : ℝ))) hφ
  dsimp only [p, F] at hf
  rw [selectedResidueFiniteLaw_mean modulus T W hW hZ
    (fun z => φ (fun i => (centeredIntegerPhysicalSite root N z i : ℝ)))] at hf
  simp only [centeredIntegerPhysicalSite_cast] at hf
  have hcap : B*((integerBox N).card : ℝ) ≤ (2*S/ρ)^Fintype.card I := by
    calc
      _ = (∏ i, (N i : ℝ))*B := by rw [card_integerBox, Nat.cast_prod]; ring
      _ ≤ _ := spatialBaseCap_volume_bound modulus (fun i => W (none,i)) (fun i => (N i : ℝ))
        (fun i => hW _) (fun i => Nat.cast_nonneg _) hρ hS hmodulusS hbase
  exact hf.trans (mul_le_mul_of_nonneg_right hcap (Finset.expect_nonneg hφ))

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def centeredSpatialWidths {K I : Type*} (B σ : ℝ) (N : I → ℕ) : Option K × I → ℝ :=
  fun z => match z.1 with
    | none => (N z.2 : ℝ)/8
    | some _ => σ*(N z.2 : ℝ)/(8*(1+B))

theorem centeredSpatialWidths_pos {K I : Type*} {B σ : ℝ} (hB : 0 ≤ B) (hσ : 0 < σ)
    (N : I → ℕ) (hN : ∀ i, 0 < N i) (z : Option K × I) :
    0 < centeredSpatialWidths B σ N z := by
  have hn : (0 : ℝ) < N z.2 := by exact_mod_cast hN z.2
  rcases z with ⟨k,i⟩
  cases k <;> dsimp only [centeredSpatialWidths] <;> positivity

theorem centeredSpatialWidths_scale {K I : Type*} {B σ : ℝ} (hB : 0 ≤ B) (hσ1 : σ ≤ 1)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i) (N : I → ℕ)
    (hsize : ∀ i, 64*(probabilityProfileLipschitz : ℝ)*(modulus i : ℝ)*(1+B) ≤ σ*(N i : ℝ))
    (z : Option K × I) :
    8*(probabilityProfileLipschitz : ℝ) ≤
      residueProfileWidth modulus (centeredSpatialWidths B σ N) z := by
  rcases z with ⟨k,i⟩
  have hm : (0 : ℝ) < modulus i := by exact_mod_cast hmodulus i
  change 8*(probabilityProfileLipschitz : ℝ) ≤ centeredSpatialWidths B σ N (k,i)/(modulus i : ℝ)
  apply (le_div_iff₀ hm).mpr
  cases k with
  | none =>
    change _ ≤ (N i : ℝ)/8
    apply (le_div_iff₀ (by norm_num : (0 : ℝ)<8)).mpr
    have hl : 64*(probabilityProfileLipschitz : ℝ)*(modulus i : ℝ) ≤
        64*(probabilityProfileLipschitz : ℝ)*(modulus i : ℝ)*(1+B) := by
      apply le_mul_of_one_le_right (by positivity)
      linarith
    have hn := mul_le_mul_of_nonneg_right hσ1 (Nat.cast_nonneg (α := ℝ) (N i))
    nlinarith [hsize i]
  | some k =>
    change _ ≤ σ*(N i : ℝ)/(8*(1+B))
    apply (le_div_iff₀ (by positivity : (0 : ℝ)<8*(1+B))).mpr
    nlinarith [hsize i]

namespace BooleanCubeKernel

theorem centeredSpatialWidths_fit {K I : Type*} [Fintype K] {B σ : ℝ}
    (hB : 0 ≤ B) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (root : K → ℤ)
    (hroot : (∑ k, |(root k : ℝ)|) ≤ B) (N : I → ℕ) (i : I) :
    4 * physicalSiteWidth root (centeredSpatialWidths B σ N) i ≤ (N i : ℝ) := by
  have hn := Nat.cast_nonneg (α := ℝ) (N i)
  have hb : 1+B ≠ 0 := ne_of_gt (by linarith)
  have hv : 0 ≤ σ*(N i : ℝ)/(8*(1+B)) := by positivity
  have ht : B*(σ*(N i : ℝ)/(8*(1+B))) ≤ (N i : ℝ)/8 := by
    calc
      _ ≤ (1+B)*(σ*(N i : ℝ)/(8*(1+B))) :=
        mul_le_mul_of_nonneg_right (by linarith) hv
      _ = σ*(N i : ℝ)/8 := by field_simp
      _ ≤ (N i : ℝ)/8 := by
        exact div_le_div_of_nonneg_right (by nlinarith) (by norm_num)
  simp only [physicalSiteWidth, centeredSpatialWidths, ← Finset.sum_mul]
  have hs := mul_le_mul_of_nonneg_right hroot hv
  nlinarith

theorem exists_centered_reference_box_domination {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I] {B σ S : ℝ}
    (hB : 0 ≤ B) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hS : 0 ≤ S)
    (root : K → ℤ) (hroot : (∑ k, |(root k : ℝ)|) ≤ B)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (hmodulusS : ∀ i, (modulus i : ℝ) ≤ S)
    (T : Finset (ColumnResiduePattern (Option K) I modulus)) (hT : T.Nonempty)
    (N : I → ℕ) (hN : ∀ i, 4 ≤ N i)
    (hsize : ∀ i, 64*(probabilityProfileLipschitz : ℝ)*(modulus i : ℝ)*(1+B) ≤ σ*(N i : ℝ)) :
    let W := centeredSpatialWidths (K := K) B σ N
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z,
      ∀ φ : (I → ℝ) → ℝ, (∀ x ∈ integerBox N, 0 ≤ φ (fun i => (x i : ℝ))) →
        (∑' z, (selectedResidueSmoothPMF modulus T W
          (centeredSpatialWidths_pos hB hσ N (fun i => by have := hN i; omega)) hZ z).toReal *
          φ ((fun i => (integerBoxCenter N i : ℝ)) + physicalAffineSite root z)) ≤
        (16*S)^Fintype.card I * (𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ))) := by
  have hW := centeredSpatialWidths_pos (K := K) hB hσ N (fun i => by have := hN i; omega)
  obtain ⟨hZ, he⟩ := exists_selected_reference_box_domination root modulus hmodulus T hT
    (centeredSpatialWidths B σ N) hW (centeredSpatialWidths_scale hB hσ1 modulus hmodulus N hsize)
    N hN (centeredSpatialWidths_fit hB hσ.le hσ1 root hroot N) hS (ρ := 1/8) (by norm_num)
    hmodulusS (fun i => by dsimp only [centeredSpatialWidths]; linarith)
  refine ⟨hZ, ?_⟩
  intro φ hφ
  simpa only [show 2*S/(1/8 : ℝ) = 16*S by ring] using he φ hφ

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def spatialSamplingBudget (P : ℝ) : ℝ := 4*P+128

theorem le_spatialSamplingBudget {P : ℝ} (hP : 0 ≤ P) : P ≤ spatialSamplingBudget P := by
  unfold spatialSamplingBudget
  linarith

noncomputable def spatialWidthFraction (P τ : ℝ) : ℝ := τ/(8*(1+Real.exp (2*P)))

theorem spatialWidthFraction_pos (P : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    0 < spatialWidthFraction P τ := by
  unfold spatialWidthFraction
  positivity

theorem spatialWidthFraction_inv_le {P τ : ℝ} (hP : 0 ≤ P) (hτ : 0 < τ)
    (hτP : τ⁻¹ ≤ Real.exp P) : 1/spatialWidthFraction P τ ≤ Real.exp (spatialSamplingBudget P) := by
  have h1 : 1 ≤ Real.exp (2*P) := Real.one_le_exp_iff.mpr (by positivity)
  have h16 : (16 : ℝ) ≤ Real.exp 128 := by linarith [Real.add_one_le_exp (128 : ℝ)]
  calc
    _ = (8*(1+Real.exp (2*P)))*τ⁻¹ := by unfold spatialWidthFraction; field_simp
    _ ≤ (16*Real.exp (2*P))*Real.exp P :=
      mul_le_mul (by nlinarith) hτP (inv_nonneg.mpr hτ.le) (by positivity)
    _ = 16*Real.exp (3*P) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ Real.exp 128 * Real.exp (3*P) := mul_le_mul_of_nonneg_right h16 (by positivity)
    _ = Real.exp (128+3*P) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by unfold spatialSamplingBudget; linarith)

theorem spatialWidthFraction_mul_le_width {K X : Type*} (P : ℝ) {τ : ℝ}
    (hτ1 : τ ≤ 1) (N : X → ℕ) (z : Option K × X) :
    spatialWidthFraction P τ * (N z.2 : ℝ) ≤
      centeredSpatialWidths (Real.exp (2*P)) τ N z := by
  have hfrac : spatialWidthFraction P τ ≤ 1/8 := by
    unfold spatialWidthFraction
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8*(1+Real.exp (2*P)))).mpr
    nlinarith [Real.exp_pos (2*P)]
  rcases z with ⟨k,i⟩
  cases k with
  | none =>
    change spatialWidthFraction P τ * (N i : ℝ) ≤ (N i : ℝ)/8
    exact (mul_le_mul_of_nonneg_right hfrac (Nat.cast_nonneg _)).trans_eq (by ring)
  | some k =>
    dsimp only [spatialWidthFraction, centeredSpatialWidths]
    apply le_of_eq
    ring

theorem root_sum_le_spatial_budget {K : Type*} [Fintype K] {P : ℝ}
    (hK : (Fintype.card K : ℝ) ≤ P) (root : K → ℤ)
    (hroot : ∀ k, |(root k : ℝ)| ≤ Real.exp P) :
    (∑ k, |(root k : ℝ)|) ≤ Real.exp (2*P) := by
  have hPe : P ≤ Real.exp P := by linarith [Real.add_one_le_exp P]
  calc
    _ ≤ ∑ _k : K, Real.exp P := Finset.sum_le_sum (fun k _ => hroot k)
    _ = (Fintype.card K : ℝ)*Real.exp P := by simp
    _ ≤ P*Real.exp P := mul_le_mul_of_nonneg_right hK (by positivity)
    _ ≤ Real.exp P * Real.exp P := mul_le_mul_of_nonneg_right hPe (by positivity)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem spatial_scale_of_exp_size {P τ H q : ℝ} (hP : 0 ≤ P) (hτ : 0 < τ)
    (hτP : τ⁻¹ ≤ Real.exp P) (hq0 : 0 ≤ q) (hq : q ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hH : Real.exp (5*P+128) ≤ H) :
    64*(probabilityProfileLipschitz : ℝ)*q*(1+Real.exp (2*P)) ≤ τ*H := by
  have h1 : 1+Real.exp (2*P) ≤ 2*Real.exp (2*P) := by
    have := Real.one_le_exp_iff.mpr (show 0 ≤ 2*P by positivity)
    linarith
  have h128 : (128 : ℝ) ≤ Real.exp 128 := by linarith [Real.add_one_le_exp (128 : ℝ)]
  have hexp : Real.exp P*Real.exp P*Real.exp (2*P)*Real.exp P = Real.exp (5*P) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [mul_comm τ H]
  apply (div_le_iff₀ hτ).mp
  calc
    _ = 64*(probabilityProfileLipschitz : ℝ)*q*(1+Real.exp (2*P))*τ⁻¹ := div_eq_mul_inv _ _
    _ ≤ 64*Real.exp P*Real.exp P*(2*Real.exp (2*P))*Real.exp P := by
      gcongr
    _ = 128*Real.exp (5*P) := by rw [show
        64*Real.exp P*Real.exp P*(2*Real.exp (2*P))*Real.exp P =
          128*(Real.exp P*Real.exp P*Real.exp (2*P)*Real.exp P) by ring, hexp]
    _ ≤ Real.exp 128*Real.exp (5*P) := mul_le_mul_of_nonneg_right h128 (by positivity)
    _ = Real.exp (5*P+128) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ H := hH

theorem spatial_threshold_dominates {P : ℝ} (hP : 0 ≤ P) {a A : ℕ}
    (hA : 256 ≤ A) (ha : 2*a ≤ A) :
    Real.exp ((spatialSamplingBudget P+a)^a) ≤ Real.exp ((P+A)^A) := by
  have hAr : (256 : ℝ) ≤ A := by exact_mod_cast hA
  have har : (2 : ℝ)*(a : ℝ) ≤ A := by exact_mod_cast ha
  have hbase : spatialSamplingBudget P+a ≤ (P+A)^2 := by
    unfold spatialSamplingBudget
    nlinarith [sq_nonneg (P+(A : ℝ)-2)]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ((P+(A : ℝ))^2)^a := pow_le_pow_left₀ (by unfold spatialSamplingBudget; positivity) hbase a
    _ = (P+(A : ℝ))^(2*a) := (pow_mul _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ (by linarith) ha

theorem spatial_threshold_large {P : ℝ} (hP : 0 ≤ P) {A : ℕ} (hA : 256 ≤ A) :
    Real.exp (5*P+128) ≤ Real.exp ((P+A)^A) := by
  have hAr : (256 : ℝ) ≤ A := by exact_mod_cast hA
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ (P+(A : ℝ))^2 := by nlinarith [sq_nonneg (P+(A : ℝ)-3)]
    _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)

theorem four_le_of_spatial_threshold {P : ℝ} (hP : 0 ≤ P) {A : ℕ}
    (hA : 256 ≤ A) (N : ℕ) (hN : Real.exp ((P+A)^A) ≤ (N : ℝ)) : 4 ≤ N := by
  have he := (spatial_threshold_large hP hA).trans hN
  have hn : (4 : ℝ) ≤ N := by linarith [Real.add_one_le_exp (5*P+128)]
  exact_mod_cast hn

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def trimmedSpatialWidths {K I : Type*} (B τ : ℝ) (N : I → ℕ) : Option K × I → ℝ :=
  fun z => τ * centeredSpatialWidths B 1 N z

theorem trimmedSpatialWidths_pos {K I : Type*} {B τ : ℝ} (hB : 0 ≤ B) (hτ : 0 < τ)
    (N : I → ℕ) (hN : ∀ i, 0 < N i) (z : Option K × I) :
    0 < trimmedSpatialWidths B τ N z :=
  mul_pos hτ (centeredSpatialWidths_pos hB (by norm_num) N hN z)

theorem spatialWidthFraction_le_trimmed_width {K I : Type*} (P : ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    (N : I → ℕ) (z : Option K × I) :
    spatialWidthFraction P τ * (N z.2 : ℝ) ≤ trimmedSpatialWidths (Real.exp (2*P)) τ N z := by
  have h := mul_le_mul_of_nonneg_left
    (spatialWidthFraction_mul_le_width (K := K) P (by norm_num : (1 : ℝ) ≤ 1) N z) hτ
  have he : spatialWidthFraction P τ = τ * spatialWidthFraction P 1 := by
    unfold spatialWidthFraction
    ring
  rw [he, mul_assoc]
  exact h

namespace BooleanCubeKernel

theorem trimmedSpatialWidths_fit {K I : Type*} [Fintype K] {B τ : ℝ}
    (hB : 0 ≤ B) (hτ : 0 ≤ τ) (root : K → ℤ)
    (hroot : (∑ k, |(root k : ℝ)|) ≤ B) (N : I → ℕ) (i : I) :
    physicalSiteWidth root (trimmedSpatialWidths B τ N) i ≤ τ * (N i : ℝ) / 4 := by
  have h := mul_le_mul_of_nonneg_left
    (centeredSpatialWidths_fit hB (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1)
      root hroot N i) hτ
  have he : physicalSiteWidth root (trimmedSpatialWidths B τ N) i =
      τ * physicalSiteWidth root (centeredSpatialWidths B 1 N) i := by
    simp only [physicalSiteWidth, trimmedSpatialWidths, mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  nlinarith

end BooleanCubeKernel

noncomputable def spatialTrimMargin {I : Type*} (τ : ℝ) (N : I → ℕ) : I → ℕ :=
  fun i => ⌈τ * (N i : ℝ) / 4⌉₊

theorem spatialTrimMargin_fits {K I : Type*} [Fintype K] {B τ : ℝ}
    (hB : 0 ≤ B) (hτ : 0 ≤ τ) (root : K → ℤ)
    (hroot : (∑ k, |(root k : ℝ)|) ≤ B) (N : I → ℕ) (i : I) :
    BooleanCubeKernel.physicalSiteWidth root (trimmedSpatialWidths B τ N) i ≤
      (spatialTrimMargin τ N i : ℝ) :=
  (BooleanCubeKernel.trimmedSpatialWidths_fit hB hτ root hroot N i).trans (Nat.le_ceil _)

theorem spatialTrimMargin_bound {I : Type*} {τ : ℝ} (N : I → ℕ)
    (hsize : ∀ i, 4 ≤ τ * (N i : ℝ)) (i : I) :
    (spatialTrimMargin τ N i : ℝ) ≤ τ * (N i : ℝ) / 2 := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ τ * (N i : ℝ) / 4 by linarith [hsize i])
  dsimp only [spatialTrimMargin]
  linarith [hsize i]

theorem spatialTrimMargin_proper {I : Type*} {τ : ℝ} (hτ : τ ≤ 1/2)
    (N : I → ℕ) (hN : ∀ i, 0 < N i) (hsize : ∀ i, 4 ≤ τ * (N i : ℝ)) (i : I) :
    2 * spatialTrimMargin τ N i < N i := by
  have hn : (0 : ℝ) < N i := by exact_mod_cast hN i
  have h := spatialTrimMargin_bound N hsize i
  have hi : (2 : ℝ) * (spatialTrimMargin τ N i : ℝ) < N i := by nlinarith
  exact_mod_cast hi

theorem spatialTrimMargin_error_bound {I : Type*} [Fintype I] {τ : ℝ}
    (N : I → ℕ) (hN : ∀ i, 0 < N i) (hsize : ∀ i, 4 ≤ τ * (N i : ℝ)) :
    2 * (∑ i, 2 * (spatialTrimMargin τ N i : ℝ) / N i) ≤ 2 * (Fintype.card I : ℝ) * τ := by
  have hi (i : I) : 2 * (spatialTrimMargin τ N i : ℝ) / N i ≤ τ := by
    apply (div_le_iff₀ (show (0 : ℝ) < N i by exact_mod_cast hN i)).mpr
    linarith [spatialTrimMargin_bound N hsize i]
  calc
    _ ≤ 2 * ∑ _i : I, τ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hi i)) (by norm_num)
    _ = _ := by simp [mul_assoc]

theorem spatialTrimMargin_size_of_exp_size {P τ H : ℝ} (hP : 0 ≤ P) (hτ : 0 < τ)
    (hτP : τ⁻¹ ≤ Real.exp P) (hH : Real.exp (5*P+128) ≤ H) : 4 ≤ τ*H := by
  have h4 : (4 : ℝ) ≤ Real.exp 128 := by linarith [Real.add_one_le_exp (128 : ℝ)]
  have h : 4/τ ≤ H := calc
    _ = 4*τ⁻¹ := div_eq_mul_inv _ _
    _ ≤ 4*Real.exp P := mul_le_mul_of_nonneg_left hτP (by norm_num)
    _ ≤ Real.exp 128 * Real.exp P := mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = Real.exp (128+P) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (5*P+128) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ H := hH
  simpa only [mul_comm H τ] using (div_le_iff₀ hτ).mp h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem trimmedSpatial_normalized_parameter_slope
    {K I : Type*} [Fintype K] [Fintype I]
    (P : K → ℕ) (N : I → ℕ) (hN : ∀ i, 0 < N i)
    {B τ : ℝ} (hB : 0 ≤ B) (_hτ : 0 ≤ τ)
    (z : rectangularWeightIndices 0 (trimmedSpatialWidths (K := K) B τ N) 1)
    (k : K) (i : I) :
    |(z.val (some k, i) : ℝ) / (N i : ℝ)| * (P k : ℝ) ≤
      τ * (P k : ℝ) / (8 * (1 + B)) := by
  have hn : (0 : ℝ) < N i := by exact_mod_cast hN i
  have hb : 0 < 8 * (1 + B) := by positivity
  have hz := rectangularWeightIndices_zero_bound
    (trimmedSpatialWidths (K := K) B τ N) z.property (some k, i)
  change |(z.val (some k, i) : ℝ)| ≤ τ * (1 * (N i : ℝ) / (8 * (1 + B))) at hz
  rw [one_mul] at hz
  calc
    _ = (|(z.val (some k, i) : ℝ)| / (N i : ℝ)) * (P k : ℝ) := by
      rw [abs_div, abs_of_nonneg hn.le]
    _ ≤ (τ * ((N i : ℝ) / (8 * (1 + B))) / (N i : ℝ)) * (P k : ℝ) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hz hn.le) (Nat.cast_nonneg _)
    _ = _ := by field_simp

theorem trimmedSpatial_normalized_parameter_slope_sum
    {K I : Type*} [Fintype K] [Fintype I]
    (P : K → ℕ) (N : I → ℕ) (hN : ∀ i, 0 < N i)
    {B τ : ℝ} (hB : 0 ≤ B) (hτ : 0 ≤ τ)
    (hP : (∑ k, (P k : ℝ)) ≤ B)
    (z : rectangularWeightIndices 0 (trimmedSpatialWidths (K := K) B τ N) 1)
    (i : I) :
    (∑ k, |(z.val (some k, i) : ℝ) / (N i : ℝ)| * (P k : ℝ)) ≤ τ / 8 := by
  have hb : 0 < 8 * (1 + B) := by positivity
  calc
    _ ≤ ∑ k, τ * (P k : ℝ) / (8 * (1 + B)) :=
      Finset.sum_le_sum (fun k _ => trimmedSpatial_normalized_parameter_slope P N hN hB hτ z k i)
    _ = τ * (∑ k, (P k : ℝ)) / (8 * (1 + B)) := by
      rw [← Finset.sum_div, Finset.mul_sum]
    _ ≤ τ * B / (8 * (1 + B)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hP hτ) hb.le
    _ ≤ τ / 8 := by
      apply (div_le_iff₀ hb).mpr
      nlinarith

end Erdos3

end

section

namespace Erdos3

theorem trimmedSpatialWidths_scale {K I : Type*} {B τ : ℝ} (hB : 0 ≤ B)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i) (N : I → ℕ)
    (hsize : ∀ i, 64*(probabilityProfileLipschitz : ℝ)*(modulus i : ℝ)*(1+B) ≤ τ*(N i : ℝ))
    (z : Option K × I) :
    8*(probabilityProfileLipschitz : ℝ) ≤
      residueProfileWidth modulus (trimmedSpatialWidths B τ N) z := by
  rcases z with ⟨k,i⟩
  have hm : (0 : ℝ) < modulus i := by exact_mod_cast hmodulus i
  change 8*(probabilityProfileLipschitz : ℝ) ≤ trimmedSpatialWidths B τ N (k,i)/(modulus i : ℝ)
  apply (le_div_iff₀ hm).mpr
  cases k with
  | none =>
    change _ ≤ τ*((N i : ℝ)/8)
    have hl : 64*(probabilityProfileLipschitz : ℝ)*(modulus i : ℝ) ≤
        64*(probabilityProfileLipschitz : ℝ)*(modulus i : ℝ)*(1+B) := by
      apply le_mul_of_one_le_right (by positivity)
      linarith
    nlinarith [hsize i]
  | some k =>
    change _ ≤ τ*(1*(N i : ℝ)/(8*(1+B)))
    rw [one_mul, ← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : (0 : ℝ)<8*(1+B))).mpr
    nlinarith [hsize i]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

noncomputable def unconditionedSpatialTrimFraction (d : ℕ) (σ : ℝ) : ℝ :=
  σ / (32 * (d + 1))

noncomputable def unconditionedSpatialWidthCutoff (B τ L : ℝ) : ℝ :=
  max (4 / τ) (8 * (1 + B) * max (8 * (probabilityProfileLipschitz : ℝ)) L / τ)

theorem unconditionedSpatialTrimFraction_bounds (d : ℕ) {σ : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    0 < unconditionedSpatialTrimFraction d σ ∧
      unconditionedSpatialTrimFraction d σ ≤ 1/2 ∧
      2 * (d : ℝ) * unconditionedSpatialTrimFraction d σ ≤ σ / 8 := by
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hden : 0 < 32 * ((d : ℝ) + 1) := by positivity
  unfold unconditionedSpatialTrimFraction
  refine ⟨div_pos hσ hden, ?_, ?_⟩
  · apply (div_le_iff₀ hden).mpr
    nlinarith
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith

theorem unconditionedSpatialWidthCutoff_bounds {K X : Type*} [Fintype X]
    {B τ L σ : ℝ} (hB : 0 ≤ B) (hτ : 0 < τ) (hτhalf : τ ≤ 1/2)
    (hbudget : 2 * (Fintype.card X : ℝ) * τ ≤ σ / 8)
    (N : X → ℕ) (hN : ∀ i, unconditionedSpatialWidthCutoff B τ L ≤ (N i : ℝ)) :
    (∀ i, 0 < N i) ∧
    (∀ i, 4 ≤ τ * (N i : ℝ)) ∧
    (∀ z : Option K × X, 0 < trimmedSpatialWidths B τ N z) ∧
    (∀ z : Option K × X, 8 * (probabilityProfileLipschitz : ℝ) ≤
      residueProfileWidth (fun _ : X => 1) (trimmedSpatialWidths B τ N) z) ∧
    (∀ z : Option K × X, L ≤ trimmedSpatialWidths B τ N z) ∧
    (∀ i, 2 * spatialTrimMargin τ N i < N i) ∧
    2 * (∑ i, 2 * (spatialTrimMargin τ N i : ℝ) / N i) ≤ σ / 8 := by
  have hsize (i : X) : 4 ≤ τ * (N i : ℝ) := by
    have hh := (le_max_left _ _).trans (hN i)
    have hh' := (div_le_iff₀ hτ).mp hh
    linarith
  have hpos (i : X) : 0 < N i := by
    have hh : 0 < (N i : ℝ) := by nlinarith [hsize i]
    exact_mod_cast hh
  let M : ℝ := max (8 * (probabilityProfileLipschitz : ℝ)) L
  have hM : 0 ≤ M := (by positivity : (0 : ℝ) ≤ 8 * (probabilityProfileLipschitz : ℝ)).trans
    (le_max_left _ _)
  have hwide (i : X) : 8 * (1 + B) * M ≤ τ * (N i : ℝ) := by
    have hh := (le_max_right _ _).trans (hN i)
    have hh' := (div_le_iff₀ hτ).mp hh
    linarith
  have hwidth (z : Option K × X) : M ≤ trimmedSpatialWidths B τ N z := by
    rcases z with ⟨k, i⟩
    cases k with
    | none =>
      change M ≤ τ * ((N i : ℝ) / 8)
      have hh : 8 * M ≤ 8 * (1 + B) * M := by nlinarith
      nlinarith [hwide i]
    | some k =>
      change M ≤ τ * (1 * (N i : ℝ) / (8 * (1 + B)))
      rw [one_mul, ← mul_div_assoc]
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (1 + B))).mpr
      nlinarith [hwide i]
  refine ⟨hpos, hsize, trimmedSpatialWidths_pos hB hτ N hpos, ?_, ?_,
    spatialTrimMargin_proper hτhalf N hpos hsize,
    (spatialTrimMargin_error_bound N hpos hsize).trans hbudget⟩
  · intro z
    change 8 * (probabilityProfileLipschitz : ℝ) ≤ trimmedSpatialWidths B τ N z / (1 : ℕ)
    simpa only [Nat.cast_one, div_one] using (le_max_left _ _).trans (hwidth z)
  · intro z
    exact (le_max_right _ _).trans (hwidth z)

theorem unconditionedSpatialWidthBudget {K X : Type*} [Fintype X]
    {B L σ : ℝ} (hB : 0 ≤ B) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (N : X → ℕ)
    (hN : ∀ i, unconditionedSpatialWidthCutoff B
      (unconditionedSpatialTrimFraction (Fintype.card X) σ) L ≤ (N i : ℝ)) :
    let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
    (∀ i, 0 < N i) ∧
    (∀ i, 4 ≤ τ * (N i : ℝ)) ∧
    (∀ z : Option K × X, 0 < trimmedSpatialWidths B τ N z) ∧
    (∀ z : Option K × X, 8 * (probabilityProfileLipschitz : ℝ) ≤
      residueProfileWidth (fun _ : X => 1) (trimmedSpatialWidths B τ N) z) ∧
    (∀ z : Option K × X, L ≤ trimmedSpatialWidths B τ N z) ∧
    (∀ i, 2 * spatialTrimMargin τ N i < N i) ∧
    2 * (∑ i, 2 * (spatialTrimMargin τ N i : ℝ) / N i) ≤ σ / 8 := by
  obtain ⟨hτ, hτhalf, hbudget⟩ := unconditionedSpatialTrimFraction_bounds (Fintype.card X) hσ hσ1
  exact unconditionedSpatialWidthCutoff_bounds hB hτ hτhalf hbudget N hN

end Erdos3

end

end OAI
