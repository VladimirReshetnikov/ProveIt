import GowersSzemeredi.Proofs16AscendingIntegerBoxes

/-! Prescribed-step refinements of genuine integer boxes. Natural index
partitions preserve nonwrapping geometry and the full width budget. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def integerAxesBox (N : Nat) {k : Nat} (Q : Fin k → NatAP) (d : Nat)
    (hstep : ∀ i, (Q i).step = d) : Box N k :=
  ⟨fun i => (Q i).toModAP N, d, fun i => congrArg (fun n : Nat => (n : ZMod N)) (hstep i)⟩

theorem Box.width_eq_of_axis_lengths_eq {N k : Nat} (P R : Box N k)
    (h : ∀ i, (P.axis i).length = (R.axis i).length) : P.width = R.width := by
  classical
  unfold Box.width
  split_ifs
  · rfl
  · have heq : (Finset.univ.image fun i => (P.axis i).length) =
        Finset.univ.image (fun i => (R.axis i).length) :=
      Finset.image_congr (fun i _ => h i)
    simp only [heq]

theorem Box.carrier_eq_of_axis_carriers_eq {N k : Nat} [NeZero N] (P R : Box N k)
    (h : ∀ i, (P.axis i).carrier = (R.axis i).carrier) : P.carrier = R.carrier := by
  classical
  ext x
  simp only [Box.carrier, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> intro hx i
  · rw [← h i]; exact hx i
  · rw [h i]; exact hx i

/-- Replace a set-theoretic integer box by its ascending natural-axis
parameterization. Carriers and widths are identical; the common orientation
can change sign. -/
theorem Box.HasIntegerRepresentatives.canonical_axes {N k : Nat} [NeZero N]
    {P : Box N k} (hP : P.HasIntegerRepresentatives) :
    ∃ d : Nat, ∃ Q : Fin k → NatAP, ∃ hstep : ∀ i, (Q i).step = d,
      0 < d ∧ (∀ i, (Q i).IsProper ∧ (Q i).carrier ⊆ Finset.range N) ∧
      (integerAxesBox N Q d hstep).carrier = P.carrier ∧
      (integerAxesBox N Q d hstep).width = P.width ∧
      ((d : ZMod N) = P.commonDiff ∨ (d : ZMod N) = -P.commonDiff) := by
  obtain ⟨d, hd, hcast, Q, hQ⟩ := hP
  let hstep := fun i => (hQ i).2.1
  refine ⟨d, Q, hstep, hd, fun i => ⟨(hQ i).1, (hQ i).2.2.2.1⟩, ?_, ?_, hcast⟩
  · apply Box.carrier_eq_of_axis_carriers_eq
    intro i
    exact ((Q i).toModAP_carrier N).trans (hQ i).2.2.2.2
  · apply Box.width_eq_of_axis_lengths_eq
    intro i
    exact (hQ i).2.2.1

theorem NatAP.toModAP_section5Transport (N : Nat) (P R : NatAP) :
    (section5NatTransport P R).toModAP N = section5Transport (P.toModAP N) R := by
  simp only [section5NatTransport, section5NatIndexPoint, NatAP.toModAP,
    section5Transport, section5IndexPoint, Nat.cast_add, Nat.cast_mul]

/-- A canonical genuine integer box admits a genuine refinement with the
same target lengths and prescribed positive integer step as the original
modular construction. No primality hypothesis is used. -/
theorem integerAxesBox_ascending_residue_partition {N k : Nat} [NeZero N]
    (Q : Fin k → NatAP) (d : Nat) (hd : 0 < d) (hstep : ∀ i, (Q i).step = d)
    (hQ : ∀ i, (Q i).IsProper) (hparent : ∀ i, (Q i).carrier ⊆ Finset.range N)
    (hk : 0 < k) (p v : Nat) (hp : 0 < p) (hv : 1 ≤ v)
    (hsize : p * v ^ 2 ≤ (integerAxesBox N Q d hstep).width) :
    ∃ M : Nat, ∃ R : Fin M → Box N k,
      IsBoxPartition R (integerAxesBox N Q d hstep) ∧
      (∀ j, (R j).IsAscendingInteger) ∧
      (∀ j, v - 1 ≤ (R j).width) ∧
      (∀ j i, 0 < ((R j).axis i).length ∧
        (((R j).axis i).length = v - 1 ∨ ((R j).axis i).length = v)) ∧
      ∀ j, (R j).commonDiff = ((p * d : Nat) : ZMod N) := by
  classical
  let P := integerAxesBox N Q d hstep
  have hPproper : P.IsProper := fun i =>
    ((Q i).toModAP_hasIntegerRepresentatives (hQ i) (hparent i)).isProper
  have hbudget (i : Fin k) : p * v ^ 2 ≤ (Q i).length :=
    hsize.trans (P.width_le_axis_length i)
  choose m T hm hTpart hTproper hTstep using
    fun i => section5_residue_target_partition (Q i).length p v hp hv (hbudget i)
  let U (i : Fin k) (j : Fin (m i)) := section5NatTransport (Q i) (T i j)
  let A (i : Fin k) (j : Fin (m i)) := (U i j).toModAP N
  have hAeq (i : Fin k) (j : Fin (m i)) :
      A i j = section5Transport (P.axis i) (T i j) :=
    NatAP.toModAP_section5Transport N (Q i) (T i j)
  have hApart (i : Fin k) : IsPartition (fun j => (A i j).carrier) (P.axis i).carrier := by
    simpa only [hAeq] using section5Transport_partition (P.axis i) (T i) (hPproper i) (hTpart i)
  have hUstep (i : Fin k) (j : Fin (m i)) : (U i j).step = p * d := by
    simp only [U, section5NatTransport, hTstep, hstep]
  have hAstep (i : Fin k) (j : Fin (m i)) : (A i j).step = ((p * d : Nat) : ZMod N) :=
    congrArg (fun n : Nat => (n : ZMod N)) (hUstep i j)
  let R : Fin (Fintype.card (∀ i, Fin (m i))) → Box N k := fun j =>
    boxProductCell m A ((p * d : Nat) : ZMod N) hAstep ((Fintype.equivFin _).symm j)
  refine ⟨_, R, boxProductCell_partition P m A _ hAstep hApart, ?_, ?_, ?_, fun _ => rfl⟩
  · intro j
    let z := (Fintype.equivFin (∀ i, Fin (m i))).symm j
    refine ⟨p * d, (fun i => U i (z i)), Nat.mul_pos hp hd, rfl, fun i => ?_⟩
    refine ⟨section5NatTransport_isProper (Q i) (T i (z i)) (hQ i) (hTproper i (z i)).1,
      hUstep i (z i), ?_, rfl⟩
    · exact (section5NatTransport_subset (Q i) (T i (z i))
        ((hTpart i).cell_subset (z i))).trans (hparent i)
  · intro j
    apply Box.le_width_of_le_axis _ hk
    intro i
    have hlen := (hTproper i (((Fintype.equivFin _).symm j) i)).2.2
    change v - 1 ≤ (T i (((Fintype.equivFin _).symm j) i)).length
    omega
  · intro j i
    exact (hTproper i _).2

/-- Compatibility statement with set-theoretic integer representatives. -/
theorem integerAxesBox_residue_partition {N k : Nat} [NeZero N]
    (Q : Fin k → NatAP) (d : Nat) (hd : 0 < d) (hstep : ∀ i, (Q i).step = d)
    (hQ : ∀ i, (Q i).IsProper) (hparent : ∀ i, (Q i).carrier ⊆ Finset.range N)
    (hk : 0 < k) (p v : Nat) (hp : 0 < p) (hv : 1 ≤ v)
    (hsize : p * v ^ 2 ≤ (integerAxesBox N Q d hstep).width) :
    ∃ M : Nat, ∃ R : Fin M → Box N k,
      IsBoxPartition R (integerAxesBox N Q d hstep) ∧
      (∀ j, (R j).HasIntegerRepresentatives) ∧
      (∀ j, v - 1 ≤ (R j).width) ∧
      (∀ j i, 0 < ((R j).axis i).length ∧
        (((R j).axis i).length = v - 1 ∨ ((R j).axis i).length = v)) ∧
      ∀ j, (R j).commonDiff = ((p * d : Nat) : ZMod N) := by
  obtain ⟨M, R, hpart, hR, hwidth, hlengths, hcommon⟩ :=
    integerAxesBox_ascending_residue_partition Q d hd hstep hQ hparent hk p v hp hv hsize
  exact ⟨M, R, hpart, fun j => (hR j).toGenuine, hwidth, hlengths, hcommon⟩

/-- An ascending stored parameterization retains its exact positive
prescribed modular step in every ascending output cell. -/
theorem Box.ascending_residue_partition {N k : Nat} [NeZero N]
    (P : Box N k) (hP : P.IsAscendingInteger) (hk : 0 < k)
    (p v : Nat) (hp : 0 < p) (hv : 1 ≤ v) (hsize : p * v ^ 2 ≤ P.width) :
    ∃ M : Nat, ∃ R : Fin M → Box N k,
      IsBoxPartition R P ∧ (∀ j, (R j).IsAscendingInteger) ∧
      (∀ j, v - 1 ≤ (R j).width) ∧
      (∀ j i, 0 < ((R j).axis i).length ∧
        (((R j).axis i).length = v - 1 ∨ ((R j).axis i).length = v)) ∧
      ∀ j, (R j).commonDiff = (p : ZMod N) * P.commonDiff := by
  obtain ⟨d, Q, hd, hcommon, hQ⟩ := hP
  let hstep := fun i => (hQ i).2.1
  have hPeq : integerAxesBox N Q d hstep = P := by
    apply Box.eq_of_axis_eq_commonDiff_eq
    · exact funext (fun i => (hQ i).2.2.2)
    · exact hcommon
  obtain ⟨M, R, hpart, hR, hwidth, hlengths, hdiff⟩ :=
    integerAxesBox_ascending_residue_partition Q d hd hstep (fun i => (hQ i).1)
      (fun i => (hQ i).2.2.1) hk p v hp hv (by rwa [hPeq])
  refine ⟨M, R, by simpa only [hPeq] using hpart, hR, hwidth, hlengths, ?_⟩
  intro j
  rw [hdiff j, Nat.cast_mul, hcommon]

/-- Every genuine integer box admits a genuine prescribed-multiple
refinement, without losing the uniform width guarantee. The common
orientation is shared across every output axis and cell. -/
theorem Box.integer_residue_partition {N k : Nat} [NeZero N]
    (P : Box N k) (hP : P.HasIntegerRepresentatives) (hk : 0 < k)
    (p v : Nat) (hp : 0 < p) (hv : 1 ≤ v) (hsize : p * v ^ 2 ≤ P.width) :
    ∃ M : Nat, ∃ R : Fin M → Box N k,
      IsBoxPartition R P ∧ (∀ j, (R j).HasIntegerRepresentatives) ∧
      (∀ j, v - 1 ≤ (R j).width) ∧
      (∀ j i, 0 < ((R j).axis i).length ∧
        (((R j).axis i).length = v - 1 ∨ ((R j).axis i).length = v)) ∧
      ∀ j, (R j).commonDiff = (p : ZMod N) * P.commonDiff ∨
        (R j).commonDiff = -((p : ZMod N) * P.commonDiff) := by
  obtain ⟨d, Q, hstep, hd, hQ, hcarrier, hwidth, hcast⟩ := hP.canonical_axes
  obtain ⟨M, R, hpart, hR, hRwidth, hRlengths, hRstep⟩ :=
    integerAxesBox_residue_partition Q d hd hstep (fun i => (hQ i).1) (fun i => (hQ i).2)
      hk p v hp hv (by rwa [hwidth])
  refine ⟨M, R, ?_, hR, hRwidth, hRlengths, ?_⟩
  · change IsPartition (fun j => (R j).carrier) P.carrier
    rw [← hcarrier]
    exact hpart
  · intro j
    rw [hRstep j, Nat.cast_mul]
    rcases hcast with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h, mul_neg])

end LeanProofs.GowersSzemeredi
