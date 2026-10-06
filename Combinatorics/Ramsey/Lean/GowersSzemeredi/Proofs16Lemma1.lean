import GowersSzemeredi.Proofs16Slicing
import GowersSzemeredi.Proofs16MultilinearLift

/-! # Small common-difference products via a multilinear lift and slice -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section16K_eq_multilinear (k : Nat) :
    section16K k = multilinearPartitionConstant (k + 1) := by
  unfold section16K multilinearPartitionConstant
  rfl

theorem section16WidthThreshold_eq_multilinear (k q : Nat) :
    section16WidthThreshold k q = multilinearPartitionThreshold (k + 1) q := by
  simp only [section16WidthThreshold, multilinearPartitionThreshold, section16K_eq_multilinear]

theorem section16RecurrenceExponent_eq_multilinear (k q : Nat) :
    section16RecurrenceExponent k q = multilinearPartitionExponent (k + 1) q := by
  simp only [section16RecurrenceExponent, multilinearPartitionExponent,
    section16K_eq_multilinear, zpow_neg, zpow_natCast]

/-- A diameter estimate for the lifted function bounds its first-coordinate
increment, even when the selected slice lies at the final progression index. -/
theorem lifted_diameter_commonDiff {N k : Nat} [NeZero N]
    (Q : Box N (k + 1)) (mu : Point N k → ZMod N) (s : Real)
    (hdiam : diameterAtMostReal
      (Q.carrier.image (fun z => mu (Fin.tail z) * z 0)) s)
    (hwidth : 2 ≤ Q.width) (y : ZMod N) (hy : y ∈ (Q.axis 0).carrier)
    (x : Point N k) (hx : x ∈ (boxTail Q).carrier) :
    (centeredAbs (mu x * Q.commonDiff) : Real) ≤ s := by
  classical
  have hbase : mu x * y ∈ Q.carrier.image (fun z => mu (Fin.tail z) * z 0) := by
    refine Finset.mem_image.mpr ⟨Fin.cons y x, (mem_boxTail_cons _ _ _).mpr ⟨hy, hx⟩, ?_⟩
    simp
  obtain hnext | hprev := (Q.axis 0).adjacent_mem (hwidth.trans (Q.width_le_axis_length 0)) hy
  · have hnext' : mu x * (y + Q.commonDiff) ∈
        Q.carrier.image (fun z => mu (Fin.tail z) * z 0) := by
      refine Finset.mem_image.mpr ⟨Fin.cons (y + (Q.axis 0).step) x,
        (mem_boxTail_cons _ _ _).mpr ⟨hnext, hx⟩, ?_⟩
      simp [Q.axis_step]
    have h := hdiam.centeredAbs_sub_le hnext' hbase
    convert h using 2
    congr 1
    ring
  · have hprev' : mu x * (y - Q.commonDiff) ∈
        Q.carrier.image (fun z => mu (Fin.tail z) * z 0) := by
      refine Finset.mem_image.mpr ⟨Fin.cons (y - (Q.axis 0).step) x,
        (mem_boxTail_cons _ _ _).mpr ⟨hprev, hx⟩, ?_⟩
      simp [Q.axis_step]
    have h := hdiam.centeredAbs_sub_le hbase hprev'
    convert h using 2
    congr 1
    ring

/-- Proper version of Lemma 16.1, with the same explicit exponent and
rounding-safe threshold as simultaneous multilinear partitioning. -/
theorem proper_lemma_16_1 (N k q m : Nat) [NeZero N] (P : Box N k)
    (hP : P.IsProper) (mu : Fin q → Point N k → ZMod N)
    (hm : section16WidthThreshold k q ≤ m) (hmP : m ≤ P.width)
    (hmu : ∀ i, IsMultilinear (mu i)) :
    ∃ M : Nat, ∃ Q : Fin M → Box N k,
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
      (∀ j, (m : Real) ^ section16RecurrenceExponent k q ≤ (Q j).width) ∧
      ∀ i j x, x ∈ (Q j).carrier →
        (centeredAbs (mu i x * (Q j).commonDiff) : Real) ≤
          2 * (m : Real) ^ (-section16RecurrenceExponent k q) * N := by
  classical
  have hm0 : 0 < m := by
    have h : 0 < section16WidthThreshold k q := by
      unfold section16WidthThreshold polynomialPartitionThreshold weylThreshold
      positivity
    omega
  have hk : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    subst k
    simp [Box.width] at hmP
    omega
  let i0 : Fin k := ⟨0, hk⟩
  let I := P.axis i0
  let R := boxCons P I (P.axis_step i0)
  let nu (i : Fin q) (z : Point N (k + 1)) := mu i (Fin.tail z) * z 0
  have hR : R.IsProper := boxCons_isProper P I _ hP (hP i0)
  have hmR : m ≤ R.width := boxCons_width P I _ hmP (hmP.trans (P.width_le_axis_length i0))
  have hm' : multilinearPartitionThreshold (k + 1) q ≤ m := by
    rwa [section16WidthThreshold_eq_multilinear] at hm
  have hnu : ∀ i, MultilinearOn R.carrier (nu i) :=
    fun i => ⟨nu i, (hmu i).mul_new_coordinate, fun _ _ => rfl⟩
  obtain ⟨M, Q, hpart, hproper, hwidth, hdiam⟩ :=
    proper_multilinear_simultaneous (k + 1) (by omega) q N m R hR nu hm' hmR hnu
  have hy : I.start ∈ I.carrier := by
    refine Finset.mem_image.mpr ⟨⟨0, ?_⟩, Finset.mem_univ _, ?_⟩
    · exact hm0.trans_le (hmP.trans (P.width_le_axis_length i0))
    · simp
  obtain ⟨L, j, hj, hslice⟩ := box_slice_partition P I (P.axis_step i0) Q hpart I.start hy
  refine ⟨L, fun a => boxTail (Q (j a)), hslice,
    fun a => boxTail_isProper _ (hproper _), ?_, ?_⟩
  · intro a
    rw [section16RecurrenceExponent_eq_multilinear]
    exact (hwidth _).trans (by exact_mod_cast boxTail_width (Q (j a)) hk)
  · intro i a x hx
    rw [section16RecurrenceExponent_eq_multilinear]
    have hw : 2 ≤ (Q (j a)).width := by
      exact_mod_cast (multilinearPartition_root_two_le (by omega : 2 ≤ k + 1) hm').trans (hwidth (j a))
    exact lifted_diameter_commonDiff (Q (j a)) (mu i) _ (hdiam i (j a)) hw I.start (hj a) x hx

/-- Exact companion for the catalogue statement. -/
theorem lemma_16_1_holds : lemma_16_1 := by
  intro N k q m _ P mu hP hm hmP hmu
  exact proper_lemma_16_1 N k q m P hP mu hm hmP hmu

end LeanProofs.GowersSzemeredi
