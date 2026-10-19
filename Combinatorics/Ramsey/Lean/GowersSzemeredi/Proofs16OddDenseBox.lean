import GowersSzemeredi.Proofs05BoxPartition
import GowersSzemeredi.Proofs16EqualSideBoxCover
import GowersSzemeredi.Proofs13OddSquareBounds
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
  have hstep := P.commonDiff_ne_zero_of_two_le_width hP hk
    (by exact_mod_cast (by linarith : (2 : Real) ≤ P.width))
  obtain ⟨Q, C, hs, hp, haxes, hCB, hCQ, hCmass⟩ := P.dense_equal_side_box hP hstep hmpos
    (by exact_mod_cast hmupper.trans hwidth) B hδ hB hmass
  refine ⟨m, Q, C, hmodd, hmpos, hmlower, hmupper.trans ?_, hs, by rwa [hs], hp,
    le_antisymm (by simpa only [haxes] using Q.width_le_axis_length ⟨0, hk⟩)
      (Q.le_width_of_le_axis hk fun i => (haxes i).ge), haxes, hCB, hCQ, hCmass⟩
  exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast NeZero.pos N) hehalf).trans_eq
    (Real.sqrt_eq_rpow _).symm

end LeanProofs.GowersSzemeredi
