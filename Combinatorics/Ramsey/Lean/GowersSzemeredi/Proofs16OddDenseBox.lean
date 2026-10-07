import GowersSzemeredi.Proofs16EqualSideBoxCover
import GowersSzemeredi.Proofs13OddFourierSquare
import GowersSzemeredi.Proofs16BaseCaseLongBoxTransport

/-! Short odd equal-side boxes retaining a quantified portion of a dense
subset in arbitrary dimension. The common nonzero step is preserved. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Positive width at least two forces a proper box's common step to be nonzero. -/
theorem Box.commonDiff_ne_zero_of_two_le_width {N k : Nat}
    (P : Box N k) (hP : P.IsProper) (hk : 0 < k) (hw : 2 ≤ P.width) :
    P.commonDiff != 0 := by
  let i : Fin k := ⟨0, hk⟩
  have h := BaseCase.proper_modAP_step_ne_zero_of_two_le (P.axis i) (hP i)
    (hw.trans (P.width_le_axis_length i))
  exact bne_iff_ne.mpr (by rwa [P.axis_step] at h)

/-- A dense proper box of width at least N^e contains, in the padded-cover
sense, a dense odd equal-side box with side between N^e/2 and sqrt(N).
The dense witness is a subset of the original set. -/
theorem Box.dense_odd_short_box {N k : Nat} [Fact N.Prime]
    (P : Box N k) (hP : P.IsProper) (hk : 0 < k) (B : Finset (Point N k))
    {delta e : Real} (hδ : 0 ≤ delta) (hehalf : e ≤ 1 / 2)
    (hwidth : (N : Real) ^ e ≤ P.width) (hlarge : 4 ≤ (N : Real) ^ e)
    (hB : B ⊆ P.carrier) (hmass : delta * P.carrier.card ≤ B.card) :
    ∃ m : Nat, ∃ Q : Box N k, ∃ C : Finset (Point N k),
      Odd m ∧ 0 < m ∧ (N : Real) ^ e / 2 ≤ m ∧ (m : Real) ≤ Real.sqrt N ∧
      Q.commonDiff = P.commonDiff ∧ Q.commonDiff != 0 ∧ Q.IsProper ∧
      Q.width = m ∧ (∀ i, (Q.axis i).length = m) ∧
      C ⊆ B ∧ C ⊆ Q.carrier ∧ delta / (2 : Real) ^ k * (m : Real) ^ k ≤ C.card := by
  obtain ⟨m, hmodd, hmpos, hmlower, hmupper⟩ := exists_odd_nat_between_half hlarge
  have hmP : m ≤ P.width := by exact_mod_cast hmupper.trans hwidth
  have hw : 2 ≤ P.width := by
    have h : (4 : Real) ≤ P.width := hlarge.trans hwidth
    have h' : 4 ≤ P.width := by exact_mod_cast h
    omega
  have hstep := P.commonDiff_ne_zero_of_two_le_width hP hk hw
  obtain ⟨Q, C, hs, hp, haxes, hCB, hCQ, hCmass⟩ :=
    P.dense_equal_side_box hP hstep hmpos hmP B hδ hB hmass
  have hN : (1 : Real) ≤ N := by exact_mod_cast NeZero.pos N
  have hmsqrt : (m : Real) ≤ Real.sqrt N := by
    calc
      _ ≤ (N : Real) ^ e := hmupper
      _ ≤ (N : Real) ^ (1 / 2 : Real) := Real.rpow_le_rpow_of_exponent_le hN hehalf
      _ = _ := (Real.sqrt_eq_rpow _).symm
  have hQwidth : Q.width = m := by
    apply le_antisymm
    · simpa only [haxes] using Q.width_le_axis_length ⟨0, hk⟩
    · exact Q.le_width_of_le_axis hk (fun i => (haxes i).ge)
  exact ⟨m, Q, C, hmodd, hmpos, hmlower, hmsqrt, hs, by rwa [hs], hp, hQwidth,
    haxes, hCB, hCQ, hCmass⟩

end LeanProofs.GowersSzemeredi
