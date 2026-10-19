import GowersSzemeredi.Proofs13PolyRecurrence
import GowersSzemeredi.Proofs16BaseCaseLongBoxTransport

/-! The phase partition of progressions from the dimension-one common-difference
partition (Notes L.7c, P11a).

`CommonDiffPartitionBoundAt k K p` (`Proofs16SimultaneousRecurrence`) partitions
a proper `k`-dimensional box so that `q` multilinear maps times the common
difference are small on every cell. `CommonDiffPartitionOne K p` is its
statement at `k = 1`, copied verbatim so that the two are definitionally equal.
This lets the light modules use it without importing the Schmidt chain.

`progressionPhasePartition_of_commonDiffOne` turns it into the
`ProgressionPhasePartition K p` used by the polynomial Lemma 13.5:
* a progression `P` is the one-dimensional box with axis `P`;
* the affine phases `h ↦ a_i h + b_i` are multilinear in dimension one;
* the cells' axes partition `P`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- `CommonDiffPartitionBoundAt 1 K p`, verbatim. -/
def CommonDiffPartitionOne (K : Real) (p : Nat) : Prop :=
      ∀ (N : Nat) [NeZero N] (q : Nat) (P : Box N 1), P.IsProper →
        ∀ mu : Fin q → Point N 1 → ZMod N, (∀ i, IsMultilinear (mu i)) →
        ∀ H : Nat, 0 < H → K * ((q : Real) + 1) ≤ H →
          H ^ (p * (q + 1) ^ (2 * (2 ^ (1 + 1)))) ≤ P.width →
          ∃ M : Nat, ∃ Q : Fin M → Box N 1,
            IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
            (∀ j, (H : Real) ≤ (Q j).width) ∧
            ∀ i j x, x ∈ (Q j).carrier →
              (centeredAbs (mu i x * (Q j).commonDiff) : Real) ≤
                ((2 : Real) ^ (1 + 1) / H) * N

/-- The width of a one-dimensional box is the length of its axis. -/
theorem Box.width_one {N : Nat} (B : Box N 1) : B.width = (B.axis 0).length := by
  classical
  unfold Box.width
  rw [dif_neg one_ne_zero]
  have himage : (Finset.univ.image fun j : Fin 1 => (B.axis j).length) = {(B.axis 0).length} := by
    rw [Finset.univ_unique, Finset.image_singleton]
    rfl
  simp only [himage, Finset.min'_singleton]

/-- Membership in a one-dimensional box is membership of the coordinate. -/
theorem Box.mem_carrier_one {N : Nat} [NeZero N] (B : Box N 1) (x : Point N 1) :
    x ∈ B.carrier ↔ x 0 ∈ (B.axis 0).carrier := by
  classical
  unfold Box.carrier
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, Fin.forall_fin_one]

/-- The box with a single axis `P`. -/
def ModAP.toBoxOne {N : Nat} (P : ModAP N) : Box N 1 where
  axis _ := P
  commonDiff := P.step
  axis_step _ := rfl

/-- **The phase partition of progressions** from the dimension-one
common-difference partition. -/
theorem progressionPhasePartition_of_commonDiffOne {K : Real} {p : Nat}
    (h : CommonDiffPartitionOne K p) : ProgressionPhasePartition K p := by
  classical
  intro N _ q P hP a b H hH hKH hsize
  obtain ⟨M, Q, hpart, hproper, hwidth, hsmall⟩ := h N q P.toBoxOne (fun _ => hP)
    (fun i x => a i * x 0 + b i) (fun i => BaseCase.isMultilinear_affine_one (a i) (b i)) H hH
    hKH (by rw [Box.width_one]; exact_mod_cast hsize)
  have hptQ (j : Fin M) (y : ZMod N) :
      (fun _ => y) ∈ (Q j).carrier ↔ y ∈ ((Q j).axis 0).carrier :=
    Box.mem_carrier_one (Q j) _
  refine ⟨M, fun j => (Q j).axis 0, ⟨fun y => ?_, fun i j hij => ?_⟩, fun j => hproper j 0,
    fun j => by simpa only [Box.width_one, Nat.cast_le] using hwidth j, fun i j y hy => ?_⟩
  · exact (Box.mem_carrier_one P.toBoxOne fun _ => y).symm.trans
      ((hpart.1 _).trans (exists_congr fun j => hptQ j y))
  · exact Finset.disjoint_left.mpr fun y hyi hyj =>
      Finset.disjoint_left.mp (hpart.2 i j hij) ((hptQ i y).mpr hyi) ((hptQ j y).mpr hyj)
  · rw [(Q j).axis_step 0, show (4 : Real) = 2 ^ (1 + 1) by norm_num]
    exact hsmall i j _ ((hptQ j y).mpr hy)

end LeanProofs.GowersSzemeredi
