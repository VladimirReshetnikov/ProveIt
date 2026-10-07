import OAI.Combinatorics.Progressions.Dynamics.PhysicalBoundaryBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def integerBoxMeshPoint (lo hi : I → ℤ) (z : ∀ i, Finset.Ico (lo i) (hi i)) :
    translatedIntegerBox lo (fun i => (hi i - lo i).toNat) := by
  refine ⟨fun i => (z i : ℤ), (mem_translatedIntegerBox _ _ _).mpr ?_⟩
  intro i
  have h := Finset.mem_Ico.mp (z i).property
  constructor
  · exact h.1
  · omega

noncomputable def integerBoxMesh (lo hi : I → ℤ)
    (P : ∀ i, FiniteProgressionPartition (hi i - lo i).toNat)
    (z : ∀ i, Finset.Ico (lo i) (hi i)) : ∀ i, (P i).Label :=
  physicalBoxCell lo (fun i => (hi i - lo i).toNat) P (integerBoxMeshPoint lo hi z)

theorem integerBoxMesh_distance (lo hi : I → ℤ)
    (P : ∀ i, FiniteProgressionPartition (hi i - lo i).toNat)
    (hstep : ∀ i c, (P i).step c = 1)
    (z w : ∀ i, Finset.Ico (lo i) (hi i))
    (hsame : integerBoxMesh lo hi P w = integerBoxMesh lo hi P z) (i : I) :
    |(z i : ℤ) - (w i : ℤ)| ≤ ((P i).length (integerBoxMesh lo hi P z i) : ℤ) := by
  have hz := (physicalBoxCell_eq_iff lo (fun i => (hi i - lo i).toNat) P hstep
    (integerBoxMeshPoint lo hi z) (integerBoxMesh lo hi P z)).mp rfl i
  have hw := (physicalBoxCell_eq_iff lo (fun i => (hi i - lo i).toNat) P hstep
    (integerBoxMeshPoint lo hi w) (integerBoxMesh lo hi P z)).mp hsame i
  change intervalCellLower (lo i) (P i) (integerBoxMesh lo hi P z i) ≤ (z i : ℤ) ∧
    (z i : ℤ) < intervalCellUpper (lo i) (P i) (integerBoxMesh lo hi P z i) at hz
  change intervalCellLower (lo i) (P i) (integerBoxMesh lo hi P z i) ≤ (w i : ℤ) ∧
    (w i : ℤ) < intervalCellUpper (lo i) (P i) (integerBoxMesh lo hi P z i) at hw
  dsimp only [intervalCellUpper, intervalCellLower] at hz hw
  exact abs_le.mpr ⟨by omega, by omega⟩

theorem normalized_integerBoxMesh_distance (lo hi : I → ℤ) (H : I → ℝ) (delta : ℝ)
    (hlarge : ∀ i, 4 ≤ delta * H i)
    (hwhole : ∀ i, delta * H i ≤ 2 * ((hi i - lo i).toNat : ℝ))
    (z w : ∀ i, Finset.Ico (lo i) (hi i))
    (hsame : integerBoxMesh lo hi (normalizedBoxPartitions (fun i => (hi i - lo i).toNat) H delta hlarge hwhole) w =
      integerBoxMesh lo hi (normalizedBoxPartitions (fun i => (hi i - lo i).toNat) H delta hlarge hwhole) z)
    (i : I) : |((z i : ℤ) : ℝ) - ((w i : ℤ) : ℝ)| ≤ delta * H i := by
  let P := normalizedBoxPartitions (fun i => (hi i - lo i).toNat) H delta hlarge hwhole
  have h := integerBoxMesh_distance lo hi P (normalizedBoxPartitions_step _ _ _ _ _) z w hsame i
  have hreal : |((z i : ℤ) : ℝ) - ((w i : ℤ) : ℝ)| ≤
      ((P i).length (integerBoxMesh lo hi P z i) : ℝ) := by exact_mod_cast h
  exact hreal.trans (normalizedBoxPartitions_lengths _ _ _ _ _ i (integerBoxMesh lo hi P z i)).2

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def integerBoxMeshPointEquiv (lo hi : I → ℤ) :
    (∀ i, Finset.Ico (lo i) (hi i)) ≃ translatedIntegerBox lo (fun i => (hi i - lo i).toNat) where
  toFun := integerBoxMeshPoint lo hi
  invFun x i := ⟨x.val i, by
    have h := (mem_translatedIntegerBox _ _ _).mp x.property i
    exact Finset.mem_Ico.mpr ⟨h.1, by omega⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def integerBoxMeshCellEquiv (lo hi : I → ℤ)
    (P : ∀ i, FiniteProgressionPartition (hi i - lo i).toNat)
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (c : ∀ i, (P i).Label) :
    {z : (∀ i, Finset.Ico (lo i) (hi i)) // integerBoxMesh lo hi P z = c} ≃
      IntegerResidueBox (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => intervalCellLower (lo i) (P i) (c i) + (P i).length (c i))
        (fun _ => 1) (fun _ => 0) := by
  let e : {z : (∀ i, Finset.Ico (lo i) (hi i)) // integerBoxMesh lo hi P z = c} ≃
      {x : translatedIntegerBox lo (fun i => (hi i - lo i).toNat) //
        physicalBoxCell lo (fun i => (hi i - lo i).toNat) P x = c} :=
    (integerBoxMeshPointEquiv lo hi).subtypeEquiv (fun _ => Iff.rfl)
  exact e.trans (physicalBoxCellEquiv lo (fun i => (hi i - lo i).toNat) P hstep hpos c)

theorem integerBoxMeshCellEquiv_val (lo hi : I → ℤ)
    (P : ∀ i, FiniteProgressionPartition (hi i - lo i).toNat)
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (c : ∀ i, (P i).Label)
    (z : {z : (∀ i, Finset.Ico (lo i) (hi i)) // integerBoxMesh lo hi P z = c}) (i : I) :
    (integerBoxMeshCellEquiv lo hi P hstep hpos c z i).val = (z.val i).val := rfl

theorem integerBoxMesh_cell_mean (lo hi : I → ℤ) [Nonempty (∀ i, Finset.Ico (lo i) (hi i))]
    (P : ∀ i, FiniteProgressionPartition (hi i - lo i).toNat)
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (c : ∀ i, (P i).Label) (f : (I → ℤ) → ℝ) :
    finiteCellMean (FiniteProbabilityWeights.uniform (∀ i, Finset.Ico (lo i) (hi i)))
      (integerBoxMesh lo hi P) (fun z => f (fun i => (z i).val)) c =
      (finiteCellWeights (FiniteProbabilityWeights.uniform (∀ i, Finset.Ico (lo i) (hi i)))
        (integerBoxMesh lo hi P)).weight c *
      (𝔼 z : IntegerResidueBox (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => intervalCellLower (lo i) (P i) (c i) + (P i).length (c i))
        (fun _ => 1) (fun _ => 0), f (fun i => (z i).val)) := by
  rw [finiteCellMean_uniform_weighted]
  congr 1
  exact Fintype.expect_equiv (integerBoxMeshCellEquiv lo hi P hstep hpos c)
    (fun z => f (fun i => (z.val i).val)) (fun z => f (fun i => (z i).val)) (fun _ => rfl)

theorem integerBoxMesh_mean_partition (lo hi : I → ℤ)
    [Nonempty (∀ i, Finset.Ico (lo i) (hi i))]
    (P : ∀ i, FiniteProgressionPartition (hi i - lo i).toNat)
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (f : (I → ℤ) → ℝ) :
    (𝔼 z : (∀ i, Finset.Ico (lo i) (hi i)), f (fun i => (z i).val)) =
      ∑ c, (finiteCellWeights (FiniteProbabilityWeights.uniform (∀ i, Finset.Ico (lo i) (hi i)))
        (integerBoxMesh lo hi P)).weight c *
      (𝔼 z : IntegerResidueBox (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => intervalCellLower (lo i) (P i) (c i) + (P i).length (c i))
        (fun _ => 1) (fun _ => 0), f (fun i => (z i).val)) := by
  rw [← FiniteProbabilityWeights.uniform_mean]
  rw [← finiteCellMean_sum _ (integerBoxMesh lo hi P)]
  exact Finset.sum_congr rfl (fun c _ => integerBoxMesh_cell_mean lo hi P hstep hpos c f)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerWindow_cell_endpoints {a b : ℤ} (hab : a < b)
    (P : FiniteProgressionPartition (b - a).toNat)
    (hstep : ∀ c, P.step c = 1) (c : P.Label) (hpos : 0 < P.length c) :
    a ≤ intervalCellLower a P c ∧
      intervalCellLower a P c + P.length c ≤ b ∧
      intervalCellLower a P c < intervalCellLower a P c + P.length c := by
  have hend := P.end_le_of_step_one hstep c hpos
  have hcount : ((b - a).toNat : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
  have hend' : (P.start c : ℤ) + P.length c ≤ (b - a).toNat := by exact_mod_cast hend
  have hstart : (0 : ℤ) ≤ P.start c := Int.natCast_nonneg _
  have hlength : (0 : ℤ) < P.length c := by exact_mod_cast hpos
  dsimp only [intervalCellLower]
  omega

theorem integerWindow_cell_endpoint_abs {a b : ℤ} {B : ℝ} (hab : a < b)
    (ha : |(a : ℝ)| ≤ B) (hb : |(b : ℝ)| ≤ B)
    (P : FiniteProgressionPartition (b - a).toNat)
    (hstep : ∀ c, P.step c = 1) (c : P.Label) (hpos : 0 < P.length c) :
    |(intervalCellLower a P c : ℝ)| ≤ B ∧
      |((intervalCellLower a P c + P.length c : ℤ) : ℝ)| ≤ B := by
  obtain ⟨hleft, hright, hlt⟩ := integerWindow_cell_endpoints hab P hstep c hpos
  have hleft' : (a : ℝ) ≤ intervalCellLower a P c := by exact_mod_cast hleft
  have hright' : ((intervalCellLower a P c + P.length c : ℤ) : ℝ) ≤ b := by exact_mod_cast hright
  have hle : (intervalCellLower a P c : ℝ) ≤ ((intervalCellLower a P c + P.length c : ℤ) : ℝ) := by exact_mod_cast hlt.le
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩

theorem integerWindow_cell_half_scale {I : Type*} [Fintype I] [DecidableEq I]
    (lo hi : I → ℤ) (P : ∀ i, FiniteProgressionPartition (hi i - lo i).toNat)
    (S : I → ℝ) (c : ∀ i, (P i).Label)
    (hlength : ∀ i, ((P i).length (c i) : ℝ) ≤ S i / 2) :
    ∀ z ∈ Fintype.piFinset (fun i => Finset.Ico (intervalCellLower (lo i) (P i) (c i))
      (intervalCellLower (lo i) (P i) (c i) + (P i).length (c i))), ∀ i,
      |(z i : ℝ) - (intervalCellLower (lo i) (P i) (c i) : ℝ)| ≤ S i / 2 := by
  intro z hz i
  have hz' := Finset.mem_Ico.mp ((Fintype.mem_piFinset.mp hz) i)
  have hleft : (intervalCellLower (lo i) (P i) (c i) : ℝ) ≤ z i := by exact_mod_cast hz'.1
  have hright : (z i : ℝ) < intervalCellLower (lo i) (P i) (c i) + ((P i).length (c i) : ℝ) := by exact_mod_cast hz'.2
  rw [abs_of_nonneg (sub_nonneg.mpr hleft)]
  linarith [hlength i]

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem affineIntegerInterval_endpoint_abs (D : ℕ) (anchor a b : ℤ) (hab : a < b)
    {F : ℝ} (hD : (D : ℝ) ≤ F)
    (hpoint : ∀ t ∈ Finset.Ico a b, |((anchor + (D : ℤ) * t : ℤ) : ℝ)| ≤ F) :
    |((anchor + (D : ℤ) * a : ℤ) : ℝ)| ≤ F ∧
      |((anchor + (D : ℤ) * b : ℤ) : ℝ)| ≤ 2 * F := by
  refine ⟨hpoint a (Finset.mem_Ico.mpr ⟨le_rfl, hab⟩), ?_⟩
  have hlast := hpoint (b - 1) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
  have heq : ((anchor + (D : ℤ) * b : ℤ) : ℝ) =
      ((anchor + (D : ℤ) * (b - 1) : ℤ) : ℝ) + D := by push_cast; ring
  rw [heq]
  have htriangle := abs_add_le (((anchor + (D : ℤ) * (b - 1) : ℤ) : ℝ)) (D : ℝ)
  rw [abs_of_nonneg (show (0 : ℝ) ≤ (D : ℝ) from Nat.cast_nonneg D)] at htriangle
  linarith

theorem affineIntegerInterval_width_le (D : ℕ) (hD : 0 < D) (anchor a b : ℤ) (hab : a < b)
    {F : ℝ} (ha : |((anchor + (D : ℤ) * a : ℤ) : ℝ)| ≤ F)
    (hb : |((anchor + (D : ℤ) * b : ℤ) : ℝ)| ≤ F) :
    ((b - a : ℤ) : ℝ) ≤ 2 * F := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hwidth : (0 : ℝ) ≤ ((b - a : ℤ) : ℝ) := by exact_mod_cast (sub_nonneg.mpr hab.le)
  have ha' := (abs_le.mp ha).1
  have hb' := (abs_le.mp hb).2
  push_cast at ha' hb' hwidth ⊢
  nlinarith

theorem exists_integerBox_width_bound {J : Type*} [Fintype J]
    (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j) {R : ℝ} (hR : 0 ≤ R)
    (hwidth : ∀ j, ((hi j - lo j : ℤ) : ℝ) ≤ R) :
    ∃ M : ℕ, (∀ j, hi j - lo j ≤ (M : ℤ)) ∧ (M : ℝ) ≤ R := by
  let M := Finset.univ.sup (fun j => (hi j - lo j).toNat)
  have hcast j : (((hi j - lo j).toNat : ℕ) : ℝ) = ((hi j - lo j : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr (hlen j).le)
  refine ⟨M, ?_, ?_⟩
  · intro j
    have hle : (hi j - lo j).toNat ≤ M := Finset.le_sup (f := fun j => (hi j - lo j).toNat) (Finset.mem_univ j)
    have hc := Int.toNat_of_nonneg (sub_nonneg.mpr (hlen j).le)
    omega
  · have hle : M ≤ ⌊R⌋₊ := Finset.sup_le (fun j _ => (Nat.le_floor_iff hR).mpr (by rw [hcast]; exact hwidth j))
    exact (Nat.cast_le.mpr hle).trans (Nat.floor_le hR)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerBoxUniformWeights_eq_uniform {I : Type*} [Fintype I] [DecidableEq I]
    (lo hi : I → ℤ) (hlen : ∀ i, lo i < hi i) [Nonempty (∀ i, Finset.Ico (lo i) (hi i))] :
    integerBoxUniformWeights lo hi hlen = FiniteProbabilityWeights.uniform (∀ i, Finset.Ico (lo i) (hi i)) := by
  apply FiniteProbabilityWeights.eq_of_weight_eq
  intro x
  change (∏ i, (Fintype.card (Finset.Ico (lo i) (hi i)) : ℝ)⁻¹) =
    (Fintype.card (∀ i, Finset.Ico (lo i) (hi i)) : ℝ)⁻¹
  rw [Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]

theorem integerBoxMesh_pair_cell_mean {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (lo hi : I → ℤ) [Nonempty (∀ i, Finset.Ico (lo i) (hi i))]
    (P : ∀ i, FiniteProgressionPartition (hi i - lo i).toNat)
    (hPstep : ∀ i c, (P i).step c = 1) (hPpos : ∀ i c, 0 < (P i).length c)
    (tlo thi : J → ℤ) [Nonempty (∀ j, Finset.Ico (tlo j) (thi j))]
    (T : ∀ j, FiniteProgressionPartition (thi j - tlo j).toNat)
    (hTstep : ∀ j c, (T j).step c = 1) (hTpos : ∀ j c, 0 < (T j).length c)
    (c : ∀ i, (P i).Label) (d : ∀ j, (T j).Label) (f : (I → ℤ) → (J → ℤ) → ℝ) :
    finiteCellMean ((FiniteProbabilityWeights.uniform (∀ j, Finset.Ico (tlo j) (thi j))).prod
        (FiniteProbabilityWeights.uniform (∀ i, Finset.Ico (lo i) (hi i))))
      (fun tx => (integerBoxMesh lo hi P tx.2, integerBoxMesh tlo thi T tx.1))
      (fun tx => f (fun i => (tx.2 i).val) (fun j => (tx.1 j).val)) (c,d) =
      (finiteCellWeights (FiniteProbabilityWeights.uniform (∀ i, Finset.Ico (lo i) (hi i)))
        (integerBoxMesh lo hi P)).weight c *
      (finiteCellWeights (FiniteProbabilityWeights.uniform (∀ j, Finset.Ico (tlo j) (thi j)))
        (integerBoxMesh tlo thi T)).weight d *
      (𝔼 z : IntegerResidueBox (fun i => intervalCellLower (lo i) (P i) (c i))
          (fun i => intervalCellLower (lo i) (P i) (c i) + (P i).length (c i)) (fun _ => 1) (fun _ => 0),
        𝔼 t : IntegerResidueBox (fun j => intervalCellLower (tlo j) (T j) (d j))
          (fun j => intervalCellLower (tlo j) (T j) (d j) + (T j).length (d j)) (fun _ => 1) (fun _ => 0),
          f (fun i => (z i).val) (fun j => (t j).val)) := by
  rw [finiteCellMean_product_uniform (integerBoxMesh lo hi P) (integerBoxMesh tlo thi T)
    (fun z t => f (fun i => (z i).val) (fun j => (t j).val)) c d]
  congr 1
  apply Fintype.expect_equiv (integerBoxMeshCellEquiv lo hi P hPstep hPpos c) _ _
  intro z
  exact Fintype.expect_equiv (integerBoxMeshCellEquiv tlo thi T hTstep hTpos d) _ _ (fun _ => rfl)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerUnitResidue_expect_eq {I : Type*} [Fintype I] [DecidableEq I]
    (lo hi : I → ℤ) (f : (I → ℤ) → ℝ) :
    (𝔼 z : IntegerResidueBox lo hi (fun _ => 1) (fun _ => 0), f (fun i => (z i).val)) =
      𝔼 z : (∀ i, Finset.Ico (lo i) (hi i)), f (fun i => (z i).val) := by
  let e : IntegerResidueBox lo hi (fun _ => 1) (fun _ => 0) ≃
      (∀ i, Finset.Ico (lo i) (hi i)) := {
    toFun := fun x i => ⟨(x i).val, (Finset.mem_filter.mp (x i).property).1⟩
    invFun := fun x i => ⟨(x i).val, Finset.mem_filter.mpr ⟨(x i).property, Int.modEq_one⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact Fintype.expect_equiv e _ _ (fun _ => rfl)

theorem integerBox_partition_eventProbability_le {I : Type*} [Fintype I] [DecidableEq I]
    (lo hi : I → ℤ) (hlen : ∀ i, lo i < hi i)
    (P : ∀ i, FiniteProgressionPartition (hi i - lo i).toNat)
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (E : (I → ℤ) → Prop) (bound : ℝ)
    (hcell : ∀ c : ∀ i, (P i).Label,
      (integerBoxUniformWeights (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => intervalCellLower (lo i) (P i) (c i) + (P i).length (c i))
        (fun i => lt_add_of_pos_right _ (by exact_mod_cast hpos i (c i)))).eventProbability
        (fun z => E (fun i => (z i).val)) ≤ bound) :
    (integerBoxUniformWeights lo hi hlen).eventProbability
      (fun z => E (fun i => (z i).val)) ≤ bound := by
  let : ∀ i, Nonempty (Finset.Ico (lo i) (hi i)) :=
    fun i => ⟨⟨lo i, Finset.mem_Ico.mpr ⟨le_rfl, hlen i⟩⟩⟩
  let weights := finiteCellWeights (FiniteProbabilityWeights.uniform (∀ i, Finset.Ico (lo i) (hi i)))
    (integerBoxMesh lo hi P)
  have hcell' (c : ∀ i, (P i).Label) :
      (𝔼 z : IntegerResidueBox (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => intervalCellLower (lo i) (P i) (c i) + (P i).length (c i))
        (fun _ => 1) (fun _ => 0), if E (fun i => (z i).val) then (1 : ℝ) else 0) ≤ bound := by
    have he := integerUnitResidue_expect_eq
      (fun i => intervalCellLower (lo i) (P i) (c i))
      (fun i => intervalCellLower (lo i) (P i) (c i) + (P i).length (c i))
      (fun z => if E z then (1 : ℝ) else 0)
    apply he.trans_le
    simpa only [FiniteProbabilityWeights.eventProbability, integerBoxUniformWeights_mean] using hcell c
  rw [FiniteProbabilityWeights.eventProbability, integerBoxUniformWeights_mean,
    integerBoxMesh_mean_partition lo hi P hstep hpos (fun z => if E z then (1 : ℝ) else 0)]
  calc
    _ ≤ ∑ c, weights.weight c * bound := Finset.sum_le_sum
      (fun c _ => mul_le_mul_of_nonneg_left (hcell' c) (weights.nonneg c))
    _ = bound := by rw [← Finset.sum_mul, weights.total, one_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerBoxMesh_cell_realize {I : Type*} [Fintype I] [DecidableEq I]
    (lo hi : I → ℤ) (P : ∀ i, FiniteProgressionPartition (hi i - lo i).toNat)
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (c : ∀ i, (P i).Label) (z : I → ℤ)
    (hz : z ∈ translatedIntegerBox (fun i => intervalCellLower (lo i) (P i) (c i))
      (fun i => (P i).length (c i))) :
    ∃ x : (∀ i, Finset.Ico (lo i) (hi i)), integerBoxMesh lo hi P x = c ∧
      (fun i => (x i).val) = z := by
  let y := physicalBoxUnitResidueEquiv
    (fun i => intervalCellLower (lo i) (P i) (c i)) (fun i => (P i).length (c i)) ⟨z,hz⟩
  let e := integerBoxMeshCellEquiv lo hi P hstep hpos c
  let x := e.symm y
  refine ⟨x.val, x.property, ?_⟩
  funext i
  have he := congrArg (fun u => (u i).val) (e.apply_symm_apply y)
  change (x.val i).val = z i at he
  exact he

theorem retained_integer_mesh_boxes_classify
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (sourceLo sourceHi : Option J × I → ℤ)
    (S : ∀ i, FiniteProgressionPartition (sourceHi i - sourceLo i).toNat)
    (hSstep : ∀ i c, (S i).step c = 1) (hSpos : ∀ i c, 0 < (S i).length c)
    (paramLo paramHi : J → ℤ)
    (T : ∀ j, FiniteProgressionPartition (paramHi j - paramLo j).toNat)
    (hTstep : ∀ j c, (T j).step c = 1) (hTpos : ∀ j c, 0 < (T j).length c)
    (D : ℕ) (a : J → ℤ)
    (x : (∀ j, Finset.Ico (paramLo j) (paramHi j)) ×
      (∀ i, Finset.Ico (sourceLo i) (sourceHi i)))
    (hx : ¬ physicalMeshCrossing lo N P
      (fun tz => (integerBoxMesh sourceLo sourceHi S tz.2, integerBoxMesh paramLo paramHi T tz.1))
      (fun tz => smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)) x) :
    ∀ z ∈ translatedIntegerBox
        (fun i => intervalCellLower (sourceLo i) (S i) (integerBoxMesh sourceLo sourceHi S x.2 i))
        (fun i => (S i).length (integerBoxMesh sourceLo sourceHi S x.2 i)),
      ∀ t ∈ translatedIntegerBox
        (fun j => intervalCellLower (paramLo j) (T j) (integerBoxMesh paramLo paramHi T x.1 j))
        (fun j => (T j).length (integerBoxMesh paramLo paramHi T x.1 j)),
        physicalBoxClassify lo N P (smoothAffineSample (fun j => a j + (D : ℤ) * t j) z) =
          physicalBoxClassify lo N P
            (smoothAffineSample (fun j => a j + (D : ℤ) * (x.1 j).val) (fun i => (x.2 i).val)) := by
  intro z hz t ht
  obtain ⟨zs, hzs, hzv⟩ := integerBoxMesh_cell_realize sourceLo sourceHi S hSstep hSpos _ z hz
  obtain ⟨ts, hts, htv⟩ := integerBoxMesh_cell_realize paramLo paramHi T hTstep hTpos _ t ht
  have he := retained_mesh_cell_constant lo N P
    (fun tz => (integerBoxMesh sourceLo sourceHi S tz.2, integerBoxMesh paramLo paramHi T tz.1))
    (fun tz => smoothAffineSample (fun j => a j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val))
    x hx (ts,zs) (Prod.ext hzs hts)
  have htj (j : J) : (ts j).val = t j := congrFun htv j
  simpa only [hzv, htj] using he

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem affine_parameter_mesh_distance {J : Type*} [Fintype J] [DecidableEq J]
    (lo hi anchor : J → ℤ) (D : ℕ) (hD : 0 < D) (L delta : ℝ)
    (hlarge : ∀ _j : J, 4 ≤ delta * (L / D))
    (hwhole : ∀ j, delta * (L / D) ≤ 2 * ((hi j - lo j).toNat : ℝ))
    (t u : ∀ j, Finset.Ico (lo j) (hi j))
    (hsame : integerBoxMesh lo hi (normalizedBoxPartitions (fun j => (hi j - lo j).toNat)
        (fun _ => L / D) delta hlarge hwhole) u =
      integerBoxMesh lo hi (normalizedBoxPartitions (fun j => (hi j - lo j).toNat)
        (fun _ => L / D) delta hlarge hwhole) t) (j : J) :
    |((anchor j + (D : ℤ) * (t j : ℤ) : ℤ) : ℝ) -
      ((anchor j + (D : ℤ) * (u j : ℤ) : ℤ) : ℝ)| ≤ delta * L := by
  have hd := normalized_integerBoxMesh_distance lo hi (fun _ => L / D) delta hlarge hwhole t u hsame j
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have he : ((anchor j + (D : ℤ) * (t j : ℤ) : ℤ) : ℝ) -
      ((anchor j + (D : ℤ) * (u j : ℤ) : ℤ) : ℝ) =
      (D : ℝ) * (((t j : ℤ) : ℝ) - ((u j : ℤ) : ℝ)) := by push_cast; ring
  rw [he, abs_mul, abs_of_nonneg hDr.le]
  calc
    _ ≤ (D : ℝ) * (delta * (L / D)) := mul_le_mul_of_nonneg_left hd hDr.le
    _ = _ := by field_simp

theorem concrete_affine_mesh_boundary_probability {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ z, sourceLo z < sourceHi z)
    (parLo parHi anchor : J → ℤ) (hpar : ∀ j, parLo j < parHi j) (D : ℕ) (hD : 0 < D)
    (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ) {L C B A c rho delta margin : ℝ}
    (hL : 0 < L) (hH : ∀ i, 0 < H i) (hC : 0 ≤ C) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hc : 0 < c) (hrho : 0 < rho) (hmargin : 0 < margin)
    (hsiteLarge : ∀ i, 4 ≤ rho * H i) (hsiteWhole : ∀ i, rho * H i ≤ 2 * (N i : ℝ))
    (hsiteRatio : ∀ i, (N i : ℝ) ≤ A * H i)
    (hbaseWidth : ∀ i, c * H i ≤ ((sourceHi (none, i) - sourceLo (none, i) : ℤ) : ℝ))
    (hround : ∀ i, 1 ≤ margin * H i)
    (hparamLo : ∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C)
    (hparamHi : ∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C)
    (hsourceLo : ∀ j i, |(sourceLo (some j, i) : ℝ)| ≤ B * H i / L)
    (hsourceHi : ∀ j i, |(sourceHi (some j, i) : ℝ)| ≤ B * H i / L)
    (hsourceLarge : ∀ z : Option J × I, 4 ≤ delta * smoothPairCoefficientScale (H z.2) L z.1)
    (hsourceWhole : ∀ z : Option J × I, delta * smoothPairCoefficientScale (H z.2) L z.1 ≤
      2 * ((sourceHi z - sourceLo z).toNat : ℝ))
    (hparamLarge : ∀ _j : J, 4 ≤ delta * (L / D))
    (hparamWhole : ∀ j, delta * (L / D) ≤ 2 * ((parHi j - parLo j).toNat : ℝ))
    (hbudget : delta * (1 + (Fintype.card J : ℝ) * (C + B)) ≤ margin) :
    let P := normalizedBoxPartitions N H rho hsiteLarge hsiteWhole
    let S := fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1
    let sourceMesh := integerBoxMesh sourceLo sourceHi
      (normalizedBoxPartitions (fun z => (sourceHi z - sourceLo z).toNat) S delta hsourceLarge hsourceWhole)
    let parameterMesh := integerBoxMesh parLo parHi
      (normalizedBoxPartitions (fun j => (parHi j - parLo j).toNat) (fun _ => L / D) delta hparamLarge hparamWhole)
    let parameter := fun t : ∀ j, Finset.Ico (parLo j) (parHi j) => fun j => anchor j + (D : ℤ) * (t j : ℤ)
    ((integerBoxUniformWeights parLo parHi hpar).prod (integerBoxUniformWeights sourceLo sourceHi hsource)).eventProbability
      (physicalMeshCrossing lo N P (fun tz => (sourceMesh tz.2, parameterMesh tz.1))
        (fun tz => smoothAffineSample (parameter tz.1) (fun z => (tz.2 z : ℤ)))) ≤
      40 * (Fintype.card I : ℝ) * A * margin / (rho * c) := by
  intro P S sourceMesh parameterMesh parameter
  have ht (t : ∀ j, Finset.Ico (parLo j) (parHi j)) (j : J) : |(parameter t j : ℝ)| ≤ C * L := by
    have h := affineInterval_normalized_cap D (anchor j) (parLo j) (parHi j) (t j : ℤ)
      hL (t j).property (hparamLo j) (hparamHi j)
    exact (div_le_iff₀ hL).mp (by simpa only [abs_div, abs_of_pos hL] using h)
  have hv (z : ∀ j, Finset.Ico (sourceLo j) (sourceHi j)) (j : J) (i : I) :
      |((z (some j, i) : ℤ) : ℝ)| ≤ B * H i / L := by
    have hz := Finset.mem_Ico.mp (z (some j, i)).property
    have hlo : (sourceLo (some j, i) : ℝ) ≤ (z (some j, i) : ℤ) := by exact_mod_cast hz.1
    have hhi : ((z (some j, i) : ℤ) : ℝ) ≤ sourceHi (some j, i) := by exact_mod_cast hz.2.le
    exact abs_le.mpr ⟨(abs_le.mp (hsourceLo j i)).1.trans hlo, hhi.trans (abs_le.mp (hsourceHi j i)).2⟩
  have hb (z w : ∀ j, Finset.Ico (sourceLo j) (sourceHi j)) (h : sourceMesh w = sourceMesh z) (i : I) :
      |((z (none, i) : ℤ) : ℝ) - ((w (none, i) : ℤ) : ℝ)| ≤ delta * H i :=
    normalized_integerBoxMesh_distance sourceLo sourceHi S delta hsourceLarge hsourceWhole z w h (none, i)
  have hvd (z w : ∀ j, Finset.Ico (sourceLo j) (sourceHi j)) (h : sourceMesh w = sourceMesh z) (j : J) (i : I) :
      |((z (some j, i) : ℤ) : ℝ) - ((w (some j, i) : ℤ) : ℝ)| ≤ delta * H i / L := by
    have hh := normalized_integerBoxMesh_distance sourceLo sourceHi S delta hsourceLarge hsourceWhole z w h (some j, i)
    simpa only [S, smoothPairCoefficientScale, mul_div_assoc] using hh
  have hp (t u : ∀ j, Finset.Ico (parLo j) (parHi j)) (h : parameterMesh u = parameterMesh t) (j : J) :
      |(parameter t j : ℝ) - parameter u j| ≤ delta * L :=
    affine_parameter_mesh_distance parLo parHi anchor D hD L delta hparamLarge hparamWhole t u h j
  have hr (i : I) : delta * H i + (Fintype.card J : ℝ) *
      ((C * L) * (delta * H i / L) + (B * H i / L) * (delta * L)) ≤ (⌈margin * H i⌉₊ : ℝ) := by
    calc
      _ = (delta * (1 + (Fintype.card J : ℝ) * (C + B))) * H i := by field_simp
      _ ≤ margin * H i := mul_le_mul_of_nonneg_right hbudget (hH i).le
      _ ≤ _ := Nat.le_ceil _
  have hbad := affine_mesh_crossing_probability (integerBoxUniformWeights parLo parHi hpar) parameter
    sourceLo sourceHi hsource sourceMesh parameterMesh lo N P
    (normalizedBoxPartitions_step _ _ _ _ _) (normalizedBoxPartitions_positive _ _ _ _ _)
    (fun i => ⌈margin * H i⌉₊) (fun i => delta * H i) (fun i => delta * H i / L)
    (fun i => B * H i / L) (C * L) (delta * L) (mul_nonneg hC hL.le) (fun i => div_nonneg (mul_nonneg hB (hH i).le) hL.le)
    ht hv hb hvd hp hr
  exact hbad.trans (normalized_physical_boundary_budget_le N H
    (fun i => ((sourceHi (none, i) - sourceLo (none, i) : ℤ) : ℝ)) rho hrho hH
    hsiteLarge hsiteWhole hA hc hmargin hsiteRatio hround hbaseWidth)

end Erdos3

end

end OAI
