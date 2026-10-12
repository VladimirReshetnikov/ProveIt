import GowersSzemeredi.Proofs16BaseCaseLongBoxTransport
import GowersSzemeredi.Proofs16IntegerLocalCover
import GowersSzemeredi.Proofs18NaturalIntervalIncrement

/-! Ordinary integer index cells transport to ascending natural-axis cells.
This includes empty index cells, whose stored start is normalized separately. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

theorem indexCellBox_isAscendingInteger {N : Nat} [NeZero N]
    (P : Box N 1) (hP : P.IsAscendingInteger) (S : IntAP)
    (hS : S.IsProper) (hsub : S.carrier ⊆ (boxOneIndexAP P).carrier) :
    (indexCellBox P S).IsAscendingInteger := by
  classical
  obtain ⟨d, A, hd, hcommon, hA⟩ := hP
  have hstep : (A 0).step = d := (hA 0).2.1
  have hstartcast : ((A 0).start : ZMod N) = (P.axis 0).start :=
    congrArg ModAP.start (hA 0).2.2.2
  have hstepcast : ((A 0).step : ZMod N) = (P.axis 0).step :=
    congrArg ModAP.step (hA 0).2.2.2
  have hdiff : ((S.step * d : Nat) : ZMod N) = (indexCellBox P S).commonDiff := by
    simp only [Nat.cast_mul, hcommon, indexCellBox]
  by_cases hzero : S.length = 0
  · let U : NatAP := ⟨((indexCellBox P S).axis 0).start.val, S.step * d, 0⟩
    refine ⟨S.step * d, fun _ => U, Nat.mul_pos hS.1 hd, hdiff, fun i => ?_⟩
    refine ⟨U.isProper_of_step_pos (Nat.mul_pos hS.1 hd), rfl, ?_, ?_⟩
    · simp only [U, NatAP.carrier, Finset.univ_eq_empty, Finset.image_empty]
      exact Finset.empty_subset _
    · simp only [U, NatAP.toModAP, indexCellBox, ZMod.natCast_zmod_val,
        Nat.cast_mul, hcommon, P.axis_step 0, hzero]
  have hSpos : 0 < S.length := Nat.pos_of_ne_zero hzero
  have hSstart : 0 ≤ S.start := by
    have hx : S.start ∈ S.carrier := by
      refine Finset.mem_image.mpr ⟨⟨0, hSpos⟩, Finset.mem_univ _, ?_⟩
      simp
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hsub hx)
    simpa only [boxOneIndexAP, zero_add, mul_one, ← hi] using (Int.natCast_nonneg i.val)
  let T : NatAP := ⟨S.start.toNat, S.step, S.length⟩
  have hstartInt : ((S.start.toNat : Nat) : Int) = S.start := Int.toNat_of_nonneg hSstart
  have hstartMod : (S.start.toNat : ZMod N) = (S.start : ZMod N) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : Int => (z : ZMod N)) hstartInt
  have hlen : (A 0).length = P.width :=
    (congrArg ModAP.length (hA 0).2.2.2).trans (boxOne_width P).symm
  have hTsub : T.carrier ⊆ Finset.range (A 0).length := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    have hz : S.start + ((j.val * S.step : Nat) : Int) ∈ S.carrier :=
      Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hsub hz)
    have hi' : (i.val : Int) = ((S.start.toNat + j.val * S.step : Nat) : Int) := by
      simpa only [boxOneIndexAP, zero_add, mul_one, Nat.cast_add, hstartInt] using hi
    have hnat : i.val = S.start.toNat + j.val * S.step := Int.ofNat_inj.mp hi'
    apply Finset.mem_range.mpr
    change S.start.toNat + j.val * S.step < (A 0).length
    rw [← hnat, hlen]
    exact i.isLt
  let U := section5NatTransport (A 0) T
  have hU : U.IsProper := section5NatTransport_isProper (A 0) T (hA 0).1
    (T.isProper_of_step_pos hS.1)
  have hUN : U.carrier ⊆ Finset.range N :=
    (section5NatTransport_subset (A 0) T hTsub).trans (hA 0).2.2.1
  refine ⟨S.step * d, fun _ => U, Nat.mul_pos hS.1 hd, hdiff, fun i => ?_⟩
  refine ⟨hU, ?_, hUN, ?_⟩
  · change S.step * (A 0).step = S.step * d
    rw [hstep]
  · simp only [U, T, section5NatTransport, section5NatIndexPoint, NatAP.toModAP,
      indexCellBox, Nat.cast_add, Nat.cast_mul, hstartcast, hstepcast, hstartMod]

end LeanProofs.GowersSzemeredi
