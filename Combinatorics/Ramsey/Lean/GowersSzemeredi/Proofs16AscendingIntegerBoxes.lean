import GowersSzemeredi.Proofs16IntegerBoxes

/-! Ascending natural-axis certificates for stored box parameterizations.
Unlike set-theoretic integer representability, these certificates can be
composed directly under the affine index transport used in height induction. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def Box.IsAscendingInteger {N k : Nat} (P : Box N k) : Prop :=
  ∃ d : Nat, ∃ Q : Fin k → NatAP,
    0 < d ∧ (d : ZMod N) = P.commonDiff ∧
    ∀ i, (Q i).IsProper ∧ (Q i).step = d ∧
      (Q i).carrier ⊆ Finset.range N ∧ (Q i).toModAP N = P.axis i

theorem Box.eq_of_axis_eq_commonDiff_eq {N k : Nat} (P R : Box N k)
    (haxis : P.axis = R.axis) (hcommon : P.commonDiff = R.commonDiff) : P = R := by
  cases P
  cases R
  cases haxis
  cases hcommon
  rfl

theorem Box.IsAscendingInteger.toGenuine {N k : Nat} [NeZero N]
    {P : Box N k} (hP : P.IsAscendingInteger) : P.HasIntegerRepresentatives := by
  obtain ⟨d, Q, hd, hcommon, hQ⟩ := hP
  refine ⟨d, hd, Or.inl hcommon, Q, fun i => ?_⟩
  refine ⟨(hQ i).1, (hQ i).2.1, congrArg ModAP.length (hQ i).2.2.2,
    (hQ i).2.2.1, ?_⟩
  rw [← (hQ i).2.2.2, NatAP.toModAP_carrier]

theorem Box.IsAscendingInteger.isProper {N k : Nat} [NeZero N]
    {P : Box N k} (hP : P.IsAscendingInteger) : P.IsProper := hP.toGenuine.isProper

/-- Every proper box's coordinate index model is ascending, even if the
original modular box itself wraps. -/
theorem boxIndexModel_isAscendingInteger {N k : Nat} [NeZero N]
    (P : Box N k) (hP : P.IsProper) : (boxIndexModel P).IsAscendingInteger := by
  classical
  let Q : Fin k → NatAP := fun i => ⟨0, 1, (P.axis i).length⟩
  refine ⟨1, Q, by omega, by simp only [boxIndexModel, Nat.cast_one], fun i => ?_⟩
  have hlen : (P.axis i).length ≤ N := by
    rw [← hP i]
    simpa only [ZMod.card] using (P.axis i).carrier.card_le_univ
  refine ⟨⟨by simp [Q], ?_⟩, rfl, ?_, ?_⟩
  · unfold NatAP.carrier
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b hab
      apply Fin.ext
      simpa [Q] using hab
  · intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    simpa [Q] using Finset.mem_range.mpr (j.isLt.trans_le hlen)
  · simp only [Q, NatAP.toModAP, boxIndexModel, modInterval, Nat.cast_zero, Nat.cast_one]

/-- Ascending certificates compose along a nonempty box in the parent's
index model. No width or cardinality loss and no primality assumption. -/
theorem boxAffineTransport_isAscendingInteger {N k : Nat} [NeZero N]
    (P R : Box N k) (hP : P.IsAscendingInteger) (hR : R.IsAscendingInteger)
    (hne : R.carrier.Nonempty) (hsub : R.carrier ⊆ (boxIndexModel P).carrier) :
    (boxAffineTransport P R).IsAscendingInteger := by
  classical
  obtain ⟨d, Q, hd, hcommonP, hQ⟩ := hP
  obtain ⟨e, T, he, hcommonR, hT⟩ := hR
  have hPproper : P.IsProper :=
    (show P.IsAscendingInteger from ⟨d, Q, hd, hcommonP, hQ⟩).isProper
  have hindices (i : Fin k) : (T i).carrier ⊆ Finset.range (Q i).length := by
    have haxis := R.axis_carrier_subset_of_carrier_subset (boxIndexModel P) hne hsub i
    have hlenN : (P.axis i).length ≤ N := by
      rw [← hPproper i]
      simpa only [ZMod.card] using (P.axis i).carrier.card_le_univ
    intro x hx
    have hxN : x < N := Finset.mem_range.mp ((hT i).2.2.1 hx)
    have hxR : (x : ZMod N) ∈ (R.axis i).carrier := by
      rw [← (hT i).2.2.2, NatAP.toModAP_carrier]
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have hxlen := val_lt_of_mem_modInterval_zero hlenN (haxis hxR)
    rw [ZMod.val_natCast_of_lt hxN] at hxlen
    have hlen : (Q i).length = (P.axis i).length := congrArg ModAP.length (hQ i).2.2.2
    exact Finset.mem_range.mpr (by omega)
  let U : Fin k → NatAP := fun i => section5NatTransport (Q i) (T i)
  refine ⟨e * d, U, Nat.mul_pos he hd, ?_, fun i => ?_⟩
  · simp only [Nat.cast_mul, hcommonP, hcommonR, boxAffineTransport]
    exact mul_comm _ _
  · refine ⟨section5NatTransport_isProper (Q i) (T i) (hQ i).1 (hT i).1,
      by simp only [U, section5NatTransport, (hQ i).2.1, (hT i).2.1],
      (section5NatTransport_subset (Q i) (T i) (hindices i)).trans (hQ i).2.2.1, ?_⟩
    change (section5NatTransport (Q i) (T i)).toModAP N =
      modAPAffine (P.axis i) (R.axis i)
    rw [NatAP.toModAP_natTransport, (hQ i).2.2.2, (hT i).2.2.2]

end LeanProofs.GowersSzemeredi
