/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Geometry.PMFSupportedMean
import OAI.Combinatorics.Progressions.Lattices.AffineMeshRetention

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

def affinePairLocations {I : Type*} (v : I → Fin 2 → ℤ) : (I → ℤ) × (I → ℤ) :=
  (fun i => v i 0, fun i => v i 1)

def affinePairRowsOfLocations {I : Type*} (xy : (I → ℤ) × (I → ℤ)) : I → Fin 2 → ℤ :=
  fun i => ![xy.1 i, xy.2 i]

theorem affinePairLocations_rows {I : Type*} (xy : (I → ℤ) × (I → ℤ)) :
    affinePairLocations (affinePairRowsOfLocations xy) = xy := rfl

theorem affinePairRows_locations {I : Type*} (v : I → Fin 2 → ℤ) :
    affinePairRowsOfLocations (affinePairLocations v) = v := by
  funext i j
  fin_cases j <;> rfl

theorem affinePairLocations_injective {I : Type*} :
    Function.Injective (affinePairLocations (I := I)) := by
  intro x y h
  have he := congrArg affinePairRowsOfLocations h
  simpa only [affinePairRows_locations] using he

theorem smoothAffinePairRows_locations {J I : Type*} [Fintype J]
    (t u : J → ℤ) (z : Option J × I → ℤ) :
    affinePairLocations (smoothAffinePairRows t u z) = (smoothAffineSample t z, smoothAffineSample u z) := by
  apply Prod.ext
  · funext i
    change smoothAffinePairRows t u z i 0 = _
    rw [smoothAffinePairRows_apply]
    rfl
  · funext i
    change smoothAffinePairRows t u z i 1 = _
    rw [smoothAffinePairRows_apply]
    rfl

theorem affinePair_joint_probability {J I : Type*} [Fintype J]
    (p : PMF (Option J × I → ℤ)) (t u : J → ℤ) (x y : I → ℤ) :
    p.map (fun z => (smoothAffineSample t z, smoothAffineSample u z)) (x, y) =
      p.map (smoothAffinePairRows t u) (affinePairRowsOfLocations (x, y)) := by
  have he : (p.map (smoothAffinePairRows t u)).map affinePairLocations =
      p.map (fun z => (smoothAffineSample t z, smoothAffineSample u z)) := by
    rw [PMF.map_comp]
    congr 1
    funext z
    exact smoothAffinePairRows_locations t u z
  rw [← he]
  have h := pmf_map_injective_at (p.map (smoothAffinePairRows t u)) affinePairLocations
    affinePairLocations_injective (affinePairRowsOfLocations (x, y))
  simpa only [affinePairLocations_rows] using h

theorem smoothSource_pair_correlation {J I : Type*} [Fintype J] [Fintype I]
    (a S : Option J × I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (t u : J → ℤ) (T U : Finset (I → ℤ)) (e d : (I → ℤ) → ℝ)
    (he : ∀ x ∉ T, e x = 0) (hd : ∀ y ∉ U, d y = 0) :
    (smoothSourceFiniteWeights a S hS hZ).mean
        (fun z => e (smoothAffineSample t z.val) * d (smoothAffineSample u z.val)) =
      ∑ x ∈ T, ∑ y ∈ U,
        ((shiftedSmoothProductPMF a S hS hZ).map (smoothAffinePairRows t u)
          (affinePairRowsOfLocations (x, y))).toReal * (e x * d y) := by
  classical
  rw [smoothSourceFiniteWeights_mean a S hS hZ
    (fun z => e (smoothAffineSample t z) * d (smoothAffineSample u z))]
  rw [pmf_pair_supported_real_mean (shiftedSmoothProductPMF a S hS hZ)
    (rectangularWeightIndices a S 1) (shiftedSmoothProductPMF_toReal_zero_off a S hS hZ)
    (smoothAffineSample t) (smoothAffineSample u) T U e d he hd]
  simp_rw [affinePair_joint_probability]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def integerVectorResidue {I : Type*} (m : ℕ) (x : I → ℤ) : I → ZMod m :=
  fun i => (x i : ZMod m)

theorem integerVectorResidue_eq_iff {I : Type*} (m : ℕ) (x y : I → ℤ) :
    integerVectorResidue m x = integerVectorResidue m y ↔ ∀ i, (m : ℤ) ∣ y i - x i := by
  simp only [funext_iff, integerVectorResidue, ZMod.intCast_eq_intCast_iff_dvd_sub]

theorem integerVectorResidue_surjective {I : Type*} (m : ℕ) :
    Function.Surjective (integerVectorResidue (I := I) m) := by
  intro r
  choose x hx using fun i => ZMod.intCast_surjective (r i)
  exact ⟨x, funext hx⟩

theorem integerVectorResidue_card (I : Type*) [Fintype I] [DecidableEq I] (m : ℕ) [NeZero m] :
    Fintype.card (I → ZMod m) = m ^ Fintype.card I := by simp

def affinePairModulus {J : Type*} [Fintype J] (t u : J → ℤ) : ℕ :=
  (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs

theorem affinePairModulus_pos {J : Type*} [Fintype J] (t u : J → ℤ) (k : J)
    (hne : u k - t k ≠ 0) : 0 < affinePairModulus t u := by
  apply Int.natAbs_pos.mpr
  apply BohrLattice.Primitive.content_ne_zero
  intro h
  exact hne (congrFun h k)

theorem affinePairModulus_residue_iff {J I : Type*} [Fintype J]
    (t u : J → ℤ) (x y : I → ℤ) :
    integerVectorResidue (affinePairModulus t u) x = integerVectorResidue (affinePairModulus t u) y ↔
      ∀ i, BohrLattice.Primitive.content (fun j => u j - t j) ∣ y i - x i := by
  rw [integerVectorResidue_eq_iff]
  simp only [affinePairModulus, Int.natAbs_dvd]

theorem affinePairPMF_zero_off_residue {J I : Type*} [Fintype J]
    (p : PMF (Option J × I → ℤ)) (t u : J → ℤ) (x y : I → ℤ)
    (hxy : integerVectorResidue (affinePairModulus t u) x ≠
      integerVectorResidue (affinePairModulus t u) y) :
    p.map (smoothAffinePairRows t u) (affinePairRowsOfLocations (x, y)) = 0 := by
  apply affinePairPMF_zero_off_congruence
  intro h
  apply hxy
  apply (affinePairModulus_residue_iff t u x y).mpr
  simpa only [affinePairRowsOfLocations, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerBox_residue_fiberLaw_weight_eq_count
    {I : Type*} [Fintype I] [DecidableEq I]
    (lo hi : I → ℤ) (hlen : ∀ i, lo i < hi i) (q : ℕ) [NeZero q] (v : I → ℤ) :
    (((integerBoxUniformWeights lo hi hlen).fiberLaw
      (fun x => integerVectorResidue q (fun i => (x i).val))).weight
        (integerVectorResidue q v)) =
      (rectangularResidueCount lo hi (fun _ => (q : ℤ)) v : ℝ) /
        integerRectangleVolume lo hi := by
  change (integerBoxUniformWeights lo hi hlen).eventProbability
    (fun x => integerVectorResidue q (fun i => (x i).val) = integerVectorResidue q v) = _
  have heq :
      (fun x : ∀ i, Finset.Ico (lo i) (hi i) =>
        integerVectorResidue q (fun i => (x i).val) = integerVectorResidue q v) =
      (fun x => ∀ i, (x i : ℤ) ≡ v i [ZMOD (q : ℤ)]) := by
    funext x
    exact propext (by simp only [integerVectorResidue_eq_iff, Int.modEq_iff_dvd])
  rw [heq, integerBoxUniformWeights,
    FiniteProbabilityWeights.eventProbability_pi
      (fun i => intervalUniformWeights (lo i) (hi i) (hlen i))
      (fun i x => (x : ℤ) ≡ v i [ZMOD (q : ℤ)])]
  have hprob (i : I) :
      (intervalUniformWeights (lo i) (hi i) (hlen i)).eventProbability
        (fun x => (x : ℤ) ≡ v i [ZMOD (q : ℤ)]) =
      (integerResidueCount (lo i) (hi i) q (v i) : ℝ) /
        ((hi i - lo i : ℤ) : ℝ) := by
    unfold FiniteProbabilityWeights.eventProbability
    rw [intervalUniformWeights_mean,
      @integerInterval_indicator_expect (lo i) (hi i) (hlen i).le
        (fun x : ℤ => x ≡ v i [ZMOD (q : ℤ)])
        (fun _ => Classical.propDecidable _)]
    congr 2
    apply congrArg Finset.card
    ext x
    simp
  simp_rw [hprob]
  simp only [Finset.prod_div_distrib, rectangularResidueCount, Nat.cast_prod,
    integerRectangleVolume]

theorem integerBox_residue_fiberLaw_relative_error
    {I : Type*} [Fintype I] [DecidableEq I]
    (lo hi : I → ℤ) (hlen : ∀ i, lo i < hi i) (q : ℕ) [NeZero q]
    (r : I → ZMod q)
    (hsmall : (∑ i, (q : ℝ) / ((hi i - lo i : ℤ) : ℝ)) ≤ 1 / 2) :
    |(q : ℝ) ^ Fintype.card I *
      (((integerBoxUniformWeights lo hi hlen).fiberLaw
        (fun x => integerVectorResidue q (fun i => (x i).val))).weight r) - 1| ≤
      2 * ∑ i, (q : ℝ) / ((hi i - lo i : ℤ) : ℝ) := by
  obtain ⟨v, rfl⟩ := integerVectorResidue_surjective q r
  rw [integerBox_residue_fiberLaw_weight_eq_count]
  have hV : 0 < integerRectangleVolume lo hi := by
    apply Finset.prod_pos
    intro i _
    exact_mod_cast sub_pos.mpr (hlen i)
  have hbound := rectangularResidueCount_relative_error lo hi (fun _ => (q : ℤ)) v
    hlen (fun _ => by exact_mod_cast NeZero.pos q) (by simpa using hsmall)
  simp only [Int.cast_natCast, Finset.prod_const, Finset.card_univ] at hbound
  calc
    _ = |((q : ℝ) ^ Fintype.card I *
        (rectangularResidueCount lo hi (fun _ => (q : ℤ)) v : ℝ) -
          integerRectangleVolume lo hi) / integerRectangleVolume lo hi| := by
      congr 1
      field_simp
    _ = |(q : ℝ) ^ Fintype.card I *
        (rectangularResidueCount lo hi (fun _ => (q : ℤ)) v : ℝ) -
          integerRectangleVolume lo hi| / integerRectangleVolume lo hi := by
      rw [abs_div, abs_of_pos hV]
    _ ≤ _ := (div_le_iff₀ hV).mpr hbound

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem affineInterval_normalized_cap (D : ℕ) (a lo hi x : ℤ) {L C : ℝ}
    (hL : 0 < L) (hx : x ∈ Finset.Ico lo hi)
    (hlow : |((a + (D : ℤ) * lo : ℤ) : ℝ) / L| ≤ C)
    (hhigh : |((a + (D : ℤ) * hi : ℤ) : ℝ) / L| ≤ C) :
    |((a + (D : ℤ) * x : ℤ) : ℝ) / L| ≤ C := by
  have hx' := Finset.mem_Ico.mp hx
  have hleft : ((a + (D : ℤ) * lo : ℤ) : ℝ) ≤ ((a + (D : ℤ) * x : ℤ) : ℝ) := by
    exact_mod_cast add_le_add (le_refl a) (mul_le_mul_of_nonneg_left hx'.1 (Int.natCast_nonneg D))
  have hright : ((a + (D : ℤ) * x : ℤ) : ℝ) ≤ ((a + (D : ℤ) * hi : ℤ) : ℝ) := by
    exact_mod_cast add_le_add (le_refl a) (mul_le_mul_of_nonneg_left hx'.2.le (Int.natCast_nonneg D))
  exact abs_le.mpr ⟨(abs_le.mp hlow).1.trans (div_le_div_of_nonneg_right hleft hL.le),
    (div_le_div_of_nonneg_right hright hL.le).trans (abs_le.mp hhigh).2⟩

theorem normalized_pair_mesh_bound (x y : ℤ) {L H C δ : ℝ}
    (hL : 0 < L) (hH : 0 < H) (hx : |(x : ℝ) / L| ≤ C) (hy : |(y : ℝ) / L| ≤ C)
    (hmesh : 2 * C * L ^ 2 / H ≤ δ) : ((y - x).natAbs : ℝ) * L / H ≤ δ := by
  have hx' : |(x : ℝ)| ≤ C * L := (div_le_iff₀ hL).mp (by simpa only [abs_div, abs_of_pos hL] using hx)
  have hy' : |(y : ℝ)| ≤ C * L := (div_le_iff₀ hL).mp (by simpa only [abs_div, abs_of_pos hL] using hy)
  have hd : ((y - x).natAbs : ℝ) ≤ 2 * C * L := by
    rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]
    exact (abs_sub _ _).trans (by linarith)
  apply le_trans _ hmesh
  apply (div_le_div_iff_of_pos_right hH).mpr
  nlinarith [mul_le_mul_of_nonneg_right hd hL.le]

theorem retained_affine_pair_geometry {J : Type*} [Fintype J]
    (D Q r : ℕ) (a x y : J → ℤ) {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ)
    (hgap : κ * L ≤ (D : ℝ) * (r + 1 : ℕ))
    (hgood : ¬ affineParameterBadPair D Q r a x y) :
    affinePairModulus (fun j => a j + (D : ℤ) * x j) (fun j => a j + (D : ℤ) * y j) ≤ Q ∧
      ∃ k : J, (a k + (D : ℤ) * y k) - (a k + (D : ℤ) * x k) ≠ 0 ∧
        κ ≤ |(((a k + (D : ℤ) * y k) - (a k + (D : ℤ) * x k) : ℤ) : ℝ) / L| := by
  constructor
  · exact le_of_not_gt (fun h => hgood (Or.inl h))
  · have hnear : ¬ ∀ j, |y j - x j| ≤ (r : ℤ) := fun h => hgood (Or.inr h)
    push Not at hnear
    obtain ⟨k, hk⟩ := hnear
    have hr : ((r + 1 : ℕ) : ℝ) ≤ |((y k - x k : ℤ) : ℝ)| := by
      have h : (r + 1 : ℕ) ≤ |y k - x k| := by omega
      exact_mod_cast h
    have heq : (((a k + (D : ℤ) * y k) - (a k + (D : ℤ) * x k) : ℤ) : ℝ) =
        (D : ℝ) * ((y k - x k : ℤ) : ℝ) := by push_cast; ring
    have hbound : κ ≤ |(((a k + (D : ℤ) * y k) - (a k + (D : ℤ) * x k) : ℤ) : ℝ) / L| := by
      rw [heq, abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg D), abs_of_pos hL]
      apply (le_div_iff₀ hL).mpr
      exact hgap.trans (mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg D))
    refine ⟨k, ?_, hbound⟩
    intro hz
    rw [hz, Int.cast_zero, zero_div, abs_zero] at hbound
    linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integer_box_residue_probability {I : Type*} [Fintype I] [DecidableEq I]
    (lo hi : I → ℤ) (hlen : ∀ i, lo i < hi i) (m : ℕ) (hm : 0 < m) (r : I → ZMod m) :
    (integerBoxUniformWeights lo hi hlen).eventProbability
      (fun x => integerVectorResidue m (fun i => (x i).val) = r) ≤
      ∏ i, (1 / (m : ℝ) + 1 / ((hi i - lo i : ℤ) : ℝ)) := by
  obtain ⟨v, hv⟩ := integerVectorResidue_surjective m r
  have heq : (fun x : ∀ i, Finset.Ico (lo i) (hi i) =>
      integerVectorResidue m (fun i => (x i).val) = r) =
      (fun x => ∀ i, (m : ℤ) ∣ (x i).val - v i) := by
    funext x
    apply propext
    rw [← hv, eq_comm, integerVectorResidue_eq_iff]
  rw [heq]
  exact integer_box_divisor_probability lo hi hlen (m : ℤ) (by exact_mod_cast hm) v

theorem integer_box_residue_probability_of_lengths {I : Type*} [Fintype I] [DecidableEq I]
    (lo hi : I → ℤ) (hlen : ∀ i, lo i < hi i) (m : ℕ) (hm : 0 < m)
    (hwidth : ∀ i, (m : ℝ) ≤ ((hi i - lo i : ℤ) : ℝ)) (r : I → ZMod m) :
    (integerBoxUniformWeights lo hi hlen).eventProbability
      (fun x => integerVectorResidue m (fun i => (x i).val) = r) ≤
      (2 : ℝ) ^ Fintype.card I / (m : ℝ) ^ Fintype.card I := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  apply (integer_box_residue_probability lo hi hlen m hm r).trans
  calc
    _ ≤ ∏ _i : I, 2 / (m : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact add_nonneg (one_div_nonneg.mpr hmR.le)
          (one_div_nonneg.mpr (hmR.le.trans (hwidth i)))
      · intro i _
        have h := one_div_le_one_div_of_le hmR (hwidth i)
        calc
          _ ≤ 1 / (m : ℝ) + 1 / (m : ℝ) := add_le_add le_rfl h
          _ = _ := by ring
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, div_pow]

theorem uniform_interval_box_residue_bound {I : Type*} [Fintype I] [DecidableEq I]
    (lo hi : I → ℤ) (hlen : ∀ i, lo i < hi i)
    [Nonempty (Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i)))]
    (m : ℕ) (hm : 0 < m) (hwidth : ∀ i, (m : ℝ) ≤ ((hi i - lo i : ℤ) : ℝ))
    (r : I → ZMod m) :
    (FiniteProbabilityWeights.uniform (Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i)))).eventProbability
      (fun x => integerVectorResidue m x.val = r) ≤
      (2 : ℝ) ^ Fintype.card I / (m : ℝ) ^ Fintype.card I := by
  classical
  have h := integer_box_residue_probability_of_lengths lo hi hlen m hm hwidth r
  unfold FiniteProbabilityWeights.eventProbability at h ⊢
  rw [FiniteProbabilityWeights.uniform_mean]
  rw [integerBoxUniformWeights_mean] at h
  apply le_of_eq_of_le ?_ h
  apply Fintype.expect_equiv (finiteBoxPointsEquiv (fun i => Finset.Ico (lo i) (hi i))).symm
  intro x
  split_ifs <;> first | rfl | contradiction

end Erdos3

end

end OAI
