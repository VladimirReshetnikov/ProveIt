import GowersSzemeredi.Proofs05IntegerMultilinearIteration
import GowersSzemeredi.Proofs16IntegerSlicing
import GowersSzemeredi.Proofs16Lemma1

/-! Genuine integer-box lift, simultaneous partition and slicing for
Lemma 16.1, retaining every numerical budget. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Proper version of Lemma 16.1, with the same explicit exponent and
rounding-safe threshold as simultaneous multilinear partitioning. -/
theorem ascending_lemma_16_1 (N k q m : Nat) [NeZero N] (P : Box N k)
    (hP : P.IsAscendingInteger) (mu : Fin q → Point N k → ZMod N)
    (hm : section16WidthThreshold k q ≤ m) (hmP : m ≤ P.width)
    (hmu : ∀ i, IsMultilinear (mu i)) :
    ∃ M : Nat, ∃ Q : Fin M → Box N k,
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsAscendingInteger) ∧
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
  have hR : R.IsAscendingInteger := boxCons_axis_isAscendingInteger P hP i0
  have hmR : m ≤ R.width := boxCons_width P I _ hmP (hmP.trans (P.width_le_axis_length i0))
  have hm' : multilinearPartitionThreshold (k + 1) q ≤ m := by
    rwa [section16WidthThreshold_eq_multilinear] at hm
  have hnu : ∀ i, MultilinearOn R.carrier (nu i) :=
    fun i => ⟨nu i, (hmu i).mul_new_coordinate, fun _ _ => rfl⟩
  obtain ⟨M, Q, hpart, hproper, hwidth, hdiam⟩ :=
    ascending_multilinear_simultaneous (k + 1) (by omega) q N m R hR nu hm' hmR hnu
  have hy : I.start ∈ I.carrier := by
    refine Finset.mem_image.mpr ⟨⟨0, ?_⟩, Finset.mem_univ _, ?_⟩
    · exact hm0.trans_le (hmP.trans (P.width_le_axis_length i0))
    · simp
  obtain ⟨L, j, hj, hslice⟩ := box_slice_partition P I (P.axis_step i0) Q hpart I.start hy
  refine ⟨L, fun a => boxTail (Q (j a)), hslice,
    fun a => boxTail_isAscendingInteger _ (hproper _), ?_, ?_⟩
  · intro a
    rw [section16RecurrenceExponent_eq_multilinear]
    exact (hwidth _).trans (by exact_mod_cast boxTail_width (Q (j a)) hk)
  · intro i a x hx
    rw [section16RecurrenceExponent_eq_multilinear]
    have hw : 2 ≤ (Q (j a)).width := by
      exact_mod_cast (multilinearPartition_root_two_le (by omega : 2 ≤ k + 1) hm').trans (hwidth (j a))
    exact lifted_diameter_commonDiff (Q (j a)) (mu i) _ (hdiam i (j a)) hw I.start (hj a) x hx

/-- Lemma 16.1 for genuine integer boxes, with its original recurrence
threshold, width exponent and common-difference norm bound. -/
theorem genuine_lemma_16_1 (N k q m : Nat) [NeZero N] (P : Box N k)
    (hP : P.HasIntegerRepresentatives) (mu : Fin q → Point N k → ZMod N)
    (hm : section16WidthThreshold k q ≤ m) (hmP : m ≤ P.width)
    (hmu : ∀ i, IsMultilinear (mu i)) :
    ∃ M : Nat, ∃ R : Fin M → Box N k,
      IsBoxPartition R P ∧ (∀ j, (R j).IsAscendingInteger) ∧
      (∀ j, (m : Real) ^ section16RecurrenceExponent k q ≤ (R j).width) ∧
      ∀ i j x, x ∈ (R j).carrier →
        (centeredAbs (mu i x * (R j).commonDiff) : Real) ≤
          2 * (m : Real) ^ (-section16RecurrenceExponent k q) * N := by
  obtain ⟨d, Q, hstep, hd, hQ, hcarrier, hwidth, hcommon⟩ := hP.canonical_axes
  let C := integerAxesBox N Q d hstep
  have hC : C.IsAscendingInteger :=
    ⟨d, Q, hd, rfl, fun i => ⟨(hQ i).1, hstep i, (hQ i).2, rfl⟩⟩
  obtain ⟨M, R, hpart, hR, hRwidth, hRnorm⟩ :=
    ascending_lemma_16_1 N k q m C hC mu hm (by rwa [hwidth]) hmu
  refine ⟨M, R, ?_, hR, hRwidth, hRnorm⟩
  change IsPartition (fun j => (R j).carrier) P.carrier
  rw [← hcarrier]
  exact hpart

/-- Genuine integer-box statement of the source's Lemma 16.1. -/
def lemma_16_1_integer_representatives : Prop :=
  ∀ (N k q m : Nat) [NeZero N] (P : Box N k) (mu : Fin q → Point N k → ZMod N),
    P.HasIntegerRepresentatives → section16WidthThreshold k q ≤ m → m ≤ P.width →
    (∀ i, IsMultilinear (mu i)) →
      ∃ M : Nat, ∃ R : Fin M → Box N k,
        IsBoxPartition R P ∧ (∀ j, (R j).HasIntegerRepresentatives) ∧
        (∀ j, (m : Real) ^ section16RecurrenceExponent k q ≤ (R j).width) ∧
        ∀ i j x, x ∈ (R j).carrier →
          (centeredAbs (mu i x * (R j).commonDiff) : Real) ≤
            2 * (m : Real) ^ (-section16RecurrenceExponent k q) * N

theorem lemma_16_1_integer_representatives_holds : lemma_16_1_integer_representatives := by
  intro N k q m _ P mu hP hm hmP hmu
  obtain ⟨M, R, hpart, hR, hwidth, hnorm⟩ := genuine_lemma_16_1 N k q m P hP mu hm hmP hmu
  exact ⟨M, R, hpart, fun j => (hR j).toGenuine, hwidth, hnorm⟩

end LeanProofs.GowersSzemeredi
