import GowersSzemeredi.Proofs05SimultaneousMultiaffinePartition
import GowersSzemeredi.Proofs16Lemma1

/-! A polynomial family-size recurrence bound for the geometry of Lemma 16.1.

For each dimension k there are K >= 2 and p > 0, independent of q, N and H,
such that H >= K*(q+1) and input width at least H^(p*(q+1)^(2^(k+2)))
yield a common proper box partition of minimum width H, on every cell of
which all q common-difference products have centered norm at most 2*N/H.

The proof lifts each phase by one coordinate, applies the simultaneous
multilinear partition, and slices. It retains the adjacent-point argument
at boundary points. A rescaling absorbs the dimension-dependent diameter
coefficient into p. The large-width bound has polynomial dependence on q
in its exponent, with existential dimension constants. This does not prove
the remaining higher-dimensional structure theorem or the printed final
all-length Szemeredi threshold.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The statement of `exists_simultaneous_commonDiff_partition_bound` at
fixed constants. -/
def CommonDiffPartitionBoundAt (k : Nat) (K : Real) (p : Nat) : Prop :=
      ∀ (N : Nat) [NeZero N] (q : Nat) (P : Box N k), P.IsProper →
        ∀ mu : Fin q → Point N k → ZMod N, (∀ i, IsMultilinear (mu i)) →
        ∀ H : Nat, 0 < H → K * ((q : Real) + 1) ≤ H →
          H ^ (p * (q + 1) ^ (2 * (2 ^ (k + 1)))) ≤ P.width →
          ∃ M : Nat, ∃ Q : Fin M → Box N k,
            IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
            (∀ j, (H : Real) ≤ (Q j).width) ∧
            ∀ i j x, x ∈ (Q j).carrier →
              (centeredAbs (mu i x * (Q j).commonDiff) : Real) ≤
                ((2 : Real) ^ (k + 1) / H) * N

/-- `exists_simultaneous_commonDiff_partition_bound` from the multilinear
partition in dimension `k + 1`, with the same constants. -/
theorem commonDiffPartitionBoundAt_of (k : Nat) {K : Real} {p : Nat} (hK : 2 ≤ K) (hp : 0 < p)
    (hpartition : MultilinearPartitionBoundAt (k + 1) K p) : CommonDiffPartitionBoundAt k K p := by
  classical
  unfold CommonDiffPartitionBoundAt
  intro N _ q P hP mu hmu H hH hscale hsize
  have hPW : 0 < P.width := (pow_pos hH _).trans_le hsize
  have hk : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    subst k
    simp [Box.width] at hPW
  have hH2 : (2 : Real) ≤ H := by
    have hc : (1 : Real) ≤ (q : Real) + 1 := by norm_num
    exact hK.trans ((le_mul_of_one_le_right (by linarith : 0 ≤ K) hc).trans hscale)
  let i0 : Fin k := ⟨0, hk⟩
  let I := P.axis i0
  let R := boxCons P I (P.axis_step i0)
  let nu (i : Fin q) (z : Point N (k + 1)) := mu i (Fin.tail z) * z 0
  have hR : R.IsProper := boxCons_isProper P I _ hP (hP i0)
  have hsizeR : H ^ (p * (q + 1) ^ (2 * (2 ^ (k + 1)))) ≤ R.width :=
    boxCons_width P I _ hsize (hsize.trans (P.width_le_axis_length i0))
  have hnu : ∀ i, MultilinearOn R.carrier (nu i) :=
    fun i => ⟨nu i, (hmu i).mul_new_coordinate, fun _ _ => rfl⟩
  obtain ⟨M, Q, hpart, hproper, hwidth, hdiam⟩ := hpartition N q R hR nu hnu H hH hscale hsizeR
  have hy : I.start ∈ I.carrier := by
    refine Finset.mem_image.mpr ⟨⟨0, hPW.trans_le (P.width_le_axis_length i0)⟩, Finset.mem_univ _, ?_⟩
    simp
  obtain ⟨L, j, hj, hslice⟩ := box_slice_partition P I (P.axis_step i0) Q hpart I.start hy
  refine ⟨L, fun a => boxTail (Q (j a)), hslice,
    fun a => boxTail_isProper _ (hproper _), ?_, ?_⟩
  · intro a
    exact (hwidth _).trans (by exact_mod_cast boxTail_width (Q (j a)) hk)
  · intro i a x hx
    have hw : 2 ≤ (Q (j a)).width := by exact_mod_cast hH2.trans (hwidth (j a))
    exact lifted_diameter_commonDiff (Q (j a)) (mu i) _ (hdiam i (j a)) hw I.start (hj a) x hx

/-- A simultaneous version of the recurrence used in Lemma 16.1.
For fixed dimension, the input-width exponent is polynomial in family size. -/
theorem exists_simultaneous_commonDiff_partition_bound (k : Nat) :
    ∃ (K : Real) (p : Nat), 2 ≤ K ∧ 0 < p ∧
      ∀ (N : Nat) [NeZero N] (q : Nat) (P : Box N k), P.IsProper →
        ∀ mu : Fin q → Point N k → ZMod N, (∀ i, IsMultilinear (mu i)) →
        ∀ H : Nat, 0 < H → K * ((q : Real) + 1) ≤ H →
          H ^ (p * (q + 1) ^ (2 * (2 ^ (k + 1)))) ≤ P.width →
          ∃ M : Nat, ∃ Q : Fin M → Box N k,
            IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
            (∀ j, (H : Real) ≤ (Q j).width) ∧
            ∀ i j x, x ∈ (Q j).carrier →
              (centeredAbs (mu i x * (Q j).commonDiff) : Real) ≤
                ((2 : Real) ^ (k + 1) / H) * N := by
  obtain ⟨K, p, hK, hp, hpartition⟩ := exists_simultaneous_multilinear_partition_bound (k + 1) (by omega)
  exact ⟨K, p, hK, hp, commonDiffPartitionBoundAt_of k hK hp hpartition⟩

/-- The statement of `exists_simultaneous_commonDiff_partition_two_bound` at
fixed constants. -/
def CommonDiffPartitionTwoBoundAt (k : Nat) (K : Real) (p : Nat) : Prop :=
      ∀ (N : Nat) [NeZero N] (q : Nat) (P : Box N k), P.IsProper →
        ∀ mu : Fin q → Point N k → ZMod N, (∀ i, IsMultilinear (mu i)) →
        ∀ H : Nat, 0 < H → K * ((q : Real) + 1) ≤ H →
          H ^ (p * (q + 1) ^ (2 * (2 ^ (k + 1)))) ≤ P.width →
          ∃ M : Nat, ∃ Q : Fin M → Box N k,
            IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
            (∀ j, (H : Real) ≤ (Q j).width) ∧
            ∀ i j x, x ∈ (Q j).carrier →
              (centeredAbs (mu i x * (Q j).commonDiff) : Real) ≤ (2 / H : Real) * N

/-- The factor-two form, with exponent constant `(k + 1) * p`. -/
theorem commonDiffPartitionTwoBoundAt_of (k : Nat) {K : Real} {p : Nat} (hK : 2 ≤ K) (hp : 0 < p)
    (hpartition : CommonDiffPartitionBoundAt k K p) :
    CommonDiffPartitionTwoBoundAt k K ((k + 1) * p) := by
  unfold CommonDiffPartitionTwoBoundAt
  intro N _ q P hP mu hmu H hH hscale hsize
  have hH2 : 2 ≤ H := by
    have hc : (1 : Real) ≤ (q : Real) + 1 := by norm_num
    have hh := hK.trans ((le_mul_of_one_le_right (by linarith : 0 ≤ K) hc).trans hscale)
    exact_mod_cast hh
  let T := 2 ^ k * H
  have hT : 0 < T := Nat.mul_pos (by positivity) hH
  have hHT : H ≤ T := Nat.le_mul_of_pos_left H (by positivity)
  have hscaleT : K * ((q : Real) + 1) ≤ T := hscale.trans (by exact_mod_cast hHT)
  have hTpow : T ≤ H ^ (k + 1) := by
    calc
      _ ≤ H ^ k * H := Nat.mul_le_mul_right H (Nat.pow_le_pow_left hH2 k)
      _ = _ := (pow_succ H k).symm
  have hsizeT : T ^ (p * (q + 1) ^ (2 * (2 ^ (k + 1)))) ≤ P.width := by
    apply le_trans _ hsize
    apply le_trans (Nat.pow_le_pow_left hTpow _)
    rw [← pow_mul]
    exact le_of_eq (congrArg (fun n => H ^ n) (by ring))
  obtain ⟨M, Q, hpart, hproper, hwidth, hsmall⟩ := hpartition N q P hP mu hmu T hT hscaleT hsizeT
  refine ⟨M, Q, hpart, hproper, fun j => (show (H : Real) ≤ T by exact_mod_cast hHT).trans (hwidth j), ?_⟩
  intro i j x hx
  have h := hsmall i j x hx
  have hHR : (0 : Real) < H := by exact_mod_cast hH
  convert h using 1
  dsimp [T]
  push_cast
  rw [pow_succ]
  field_simp

/-- Absorb the dimension-dependent diameter coefficient into the exponent
constant, retaining the factor 2 in the common-difference error. -/
theorem exists_simultaneous_commonDiff_partition_two_bound (k : Nat) :
    ∃ (K : Real) (p : Nat), 2 ≤ K ∧ 0 < p ∧
      ∀ (N : Nat) [NeZero N] (q : Nat) (P : Box N k), P.IsProper →
        ∀ mu : Fin q → Point N k → ZMod N, (∀ i, IsMultilinear (mu i)) →
        ∀ H : Nat, 0 < H → K * ((q : Real) + 1) ≤ H →
          H ^ (p * (q + 1) ^ (2 * (2 ^ (k + 1)))) ≤ P.width →
          ∃ M : Nat, ∃ Q : Fin M → Box N k,
            IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
            (∀ j, (H : Real) ≤ (Q j).width) ∧
            ∀ i j x, x ∈ (Q j).carrier →
              (centeredAbs (mu i x * (Q j).commonDiff) : Real) ≤ (2 / H : Real) * N := by
  obtain ⟨K, p, hK, hp, hpartition⟩ := exists_simultaneous_commonDiff_partition_bound k
  exact ⟨K, (k + 1) * p, hK, Nat.mul_pos (by omega) hp,
    commonDiffPartitionTwoBoundAt_of k hK hp hpartition⟩

end LeanProofs.GowersSzemeredi
