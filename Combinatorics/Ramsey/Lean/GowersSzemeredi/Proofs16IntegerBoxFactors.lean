import GowersSzemeredi.Proofs16IntegerRetiledRecurrence
import GowersSzemeredi.Proofs16SingletonPartition

/-! Canonical factors and singleton cells retain integer certificates. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem boxInit_isAscendingInteger {N k : Nat} (P : Box N (k + 1))
    (hP : P.IsAscendingInteger) : (boxInit P).IsAscendingInteger := by
  obtain ⟨d, A, hd, hcommon, hA⟩ := hP
  exact ⟨d, fun i => A i.castSucc, hd, hcommon, fun i => hA i.castSucc⟩

theorem pointSingletonBox_isAscendingInteger {N k : Nat} [NeZero N] (x : Point N k) :
    (pointSingletonBox x).IsAscendingInteger := by
  classical
  let A (i : Fin k) : NatAP := ⟨(x i).val, 1, 1⟩
  refine ⟨1, A, Nat.one_pos, by simp only [Nat.cast_one, pointSingletonBox],
    fun i => ⟨⟨Nat.one_pos, ?_⟩, rfl, ?_, ?_⟩⟩
  · unfold NatAP.carrier
    rw [Finset.card_image_of_injective _ (fun a b _ => Subsingleton.elim a b)]
    exact Fintype.card_fin 1
  · intro y hy
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hy
    have ha : a.val = 0 := by have h := a.isLt; change a.val < 1 at h; omega
    simpa only [A, ha, zero_mul, add_zero] using Finset.mem_range.mpr (ZMod.val_lt (x i))
  · simp only [A, NatAP.toModAP, pointSingletonBox, ZMod.natCast_zmod_val, Nat.cast_one]

theorem boxInit_carrier_eq_of_box_carrier_eq {N k : Nat} [NeZero N]
    (P R : Box N (k + 1)) (h : P.carrier = R.carrier)
    (hneP : P.carrier.Nonempty) (hneR : R.carrier.Nonempty) :
    (boxInit P).carrier = (boxInit R).carrier := by
  apply Box.carrier_eq_of_axis_carriers_eq
  intro i
  exact Finset.Subset.antisymm
    (P.axis_carrier_subset_of_carrier_subset R hneP h.le i.castSucc)
    (R.axis_carrier_subset_of_carrier_subset P hneR h.ge i.castSucc)

end LeanProofs.GowersSzemeredi
