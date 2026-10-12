import GowersSzemeredi.Proofs16ShortParents
import GowersSzemeredi.Proofs16IntegerProductTiling

/-! Bounded and short parent partitions retain ascending integer axes.
The original constant-factor width loss and every axis bound are preserved. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem NatAP.bounded_partition (P : NatAP) (hP : P.IsProper)
    (r : Nat) (hr : 0 < r) (hsize : r ≤ P.length) :
    ∃ M : Nat, ∃ Q : Fin M → NatAP,
      0 < M ∧ IsNatAPPartition Q P.carrier ∧
      (∀ j, (Q j).IsProper ∧ r ≤ (Q j).length ∧ (Q j).length < 2 * r) ∧
      (∀ j, (Q j).step = P.step) := by
  obtain ⟨M, A, hM, hpart, hprops, hstep⟩ := bounded_interval_partition P.length r hr hsize
  refine ⟨M, fun j => section5NatTransport P (A j), hM,
    section5NatTransport_partition P A hP hpart, ?_, ?_⟩
  · intro j
    exact ⟨section5NatTransport_isProper P (A j) hP (hprops j).1, (hprops j).2⟩
  · intro j
    change (A j).step * P.step = P.step
    rw [hstep j, one_mul]

theorem Box.ascending_bounded_partition {N k : Nat} [NeZero N] (P : Box N k)
    (hP : P.IsAscendingInteger) (hk : 0 < k) (r : Nat) (hr : 0 < r)
    (hsize : r ≤ P.width) :
    ∃ M : Nat, ∃ Q : Fin M → Box N k,
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsAscendingInteger ∧ r ≤ (Q j).width) ∧
      (∀ j i, r ≤ ((Q j).axis i).length ∧ ((Q j).axis i).length < 2 * r) ∧
      (∀ j, (Q j).commonDiff = P.commonDiff) := by
  classical
  obtain ⟨d, A, hd, hcommon, hA⟩ := hP
  have hAlen (i : Fin k) : (A i).length = (P.axis i).length :=
    congrArg ModAP.length (hA i).2.2.2
  choose m R hm hpart hprops hstep using fun i =>
    (A i).bounded_partition (hA i).1 r hr (by rw [hAlen i]; exact hsize.trans (P.width_le_axis_length i))
  have hRN (i : Fin k) (j : Fin (m i)) : (R i j).carrier ⊆ Finset.range N :=
    (IsPartition.cell_subset (hpart i) j).trans (hA i).2.2.1
  have hRd (i : Fin k) (j : Fin (m i)) : (R i j).step = d :=
    (hstep i j).trans (hA i).2.1
  let T (i : Fin k) (j : Fin (m i)) := (R i j).toModAP N
  have hTstep (i : Fin k) (j : Fin (m i)) : (T i j).step = P.commonDiff :=
    (congrArg (fun a : Nat => (a : ZMod N)) (hRd i j)).trans hcommon
  have hTpart (i : Fin k) : IsPartition (fun j => (T i j).carrier) (P.axis i).carrier := by
    rw [← (hA i).2.2.2]
    exact (hpart i).toModAP (hA i).2.2.1
  let Q := fun j : Fin (Fintype.card (∀ i, Fin (m i))) =>
    boxProductCell m T P.commonDiff hTstep ((Fintype.equivFin _).symm j)
  have hQ (j : Fin (Fintype.card (∀ i, Fin (m i)))) : (Q j).IsAscendingInteger := by
    refine ⟨d, fun i => R i (((Fintype.equivFin _).symm j) i), hd, hcommon, fun i => ?_⟩
    exact ⟨(hprops i _).1, hRd i _, hRN i _, rfl⟩
  refine ⟨_, Q, boxProductCell_partition P m T _ hTstep hTpart, ?_, ?_, fun _ => rfl⟩
  · intro j
    exact ⟨hQ j, Box.le_width_of_le_axis _ hk (fun i => (hprops i _).2.1)⟩
  · intro j i
    exact (hprops i _).2

theorem Box.ascending_short_parent_partition {N k m : Nat} [NeZero N]
    (P : Box N k) (I : ModAP N) (hP : P.IsAscendingInteger) (hI : I.IsProper)
    (hk : 0 < k) (hm : 4 ≤ m) (hmP : m ≤ P.width) (hmI : m ≤ I.length) :
    ∃ M : Nat, ∃ Q : Fin M → Box N k,
      IsBoxPartition Q P ∧
      (∀ j, (Q j).IsAscendingInteger ∧ (m : Real) / 8 ≤ (Q j).width) ∧
      (∀ j i, 0 < ((Q j).axis i).length ∧
        2 * ((Q j).axis i).length ≤ N ∧ ((Q j).axis i).length ≤ I.length) ∧
      (∀ j, (Q j).commonDiff = P.commonDiff) := by
  obtain ⟨hr, hlower, hupper⟩ := quarter_scale_width hm
  obtain ⟨M, Q, hpart, hQ, haxes, hstep⟩ :=
    P.ascending_bounded_partition hP hk (m / 4) hr ((Nat.div_le_self _ _).trans hmP)
  have hIN : I.length ≤ N := by
    rw [← hI]
    simpa only [ZMod.card] using Finset.card_le_univ I.carrier
  refine ⟨M, Q, hpart, ?_, ?_, hstep⟩
  · intro j
    refine ⟨(hQ j).1, ?_⟩
    have h : m ≤ 8 * (Q j).width := hlower.trans (Nat.mul_le_mul_left 8 (hQ j).2)
    have h' : (m : Real) ≤ 8 * ((Q j).width : Real) := by exact_mod_cast h
    linarith only [h']
  · intro j i
    have h := haxes j i
    omega

end LeanProofs.GowersSzemeredi
