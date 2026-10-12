import GowersSzemeredi.Proofs16IntegerContainedSteps

/-! Product tiling with genuine integer-axis certificates. Containment
in an ordinary parallel parent supplies the actual positive step ratio.
No prime modulus, unit step or short-parent hypothesis is required. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem IsPartition.image_injOn {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    {M : Nat} {A : Fin M → Finset X} {S : Finset X}
    (hpart : IsPartition A S) (f : X → Y) (hinj : Set.InjOn f (S : Set X)) :
    IsPartition (fun j => (A j).image f) (S.image f) := by
  classical
  constructor
  · intro y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨j, hj⟩ := (hpart.1 x).mp hx
      exact ⟨j, Finset.mem_image.mpr ⟨x, hj, rfl⟩⟩
    · rintro ⟨j, hj⟩
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_image.mpr ⟨x, (hpart.1 x).mpr ⟨j, hx⟩, rfl⟩
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro y hi hj
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp hj
    have hxz : x = z := hinj ((hpart.1 x).mpr ⟨i, hx⟩)
      ((hpart.1 z).mpr ⟨j, hz⟩) heq.symm
    subst z
    exact Finset.disjoint_left.mp (hpart.2 i j hij) hx hz

theorem IsNatAPPartition.toModAP {N M : Nat} [NeZero N]
    {A : Fin M → NatAP} {I : NatAP} (hpart : IsNatAPPartition A I.carrier)
    (hIN : I.carrier ⊆ Finset.range N) :
    IsPartition (fun j => ((A j).toModAP N).carrier) (I.toModAP N).carrier := by
  classical
  have hinj : Set.InjOn (fun x : Nat => (x : ZMod N)) (I.carrier : Set Nat) := by
    intro x hx y hy hxy
    have hval := congrArg ZMod.val hxy
    simpa only [ZMod.val_natCast_of_lt (Finset.mem_range.mp (hIN hx)),
      ZMod.val_natCast_of_lt (Finset.mem_range.mp (hIN hy))] using hval
  simpa only [NatAP.toModAP_carrier] using hpart.image_injOn (fun x : Nat => (x : ZMod N)) hinj

theorem ascending_box_product_tiling_of_contained_integer_axis {N k v : Nat} [NeZero N]
    (R : Box N k) (hR : R.IsAscendingInteger) (B I : NatAP) (i : Fin k)
    (hB : B.IsProper) (hI : I.IsProper)
    (hBN : B.carrier ⊆ Finset.range N) (hIN : I.carrier ⊆ Finset.range N)
    (hparallel : B.step = I.step)
    (hsub : (R.axis i).carrier ⊆ (B.toModAP N).carrier)
    (hL : B.length ≤ I.length) (hv : 1 ≤ v) (hfit : v ^ 2 ≤ R.width - 1) :
    ∃ M : Nat, ∃ S : Fin M → Box N (k + 1), ∃ J : Fin M → ModAP N,
      IsPartition (fun j => (S j).carrier)
        (Finset.univ.filter (fun x : Point N (k + 1) =>
          section16Init x ∈ R.carrier ∧ section16Last x ∈ (I.toModAP N).carrier)) ∧
      (∀ j, (S j).IsAscendingInteger ∧ v - 1 ≤ (S j).width) ∧
      (∀ j, IsLastCoordinateBoxProduct (S j) R (J j)) ∧
      (∀ j, (J j).HasIntegerRepresentatives ∧ 0 < (J j).length ∧
        ((J j).length = v - 1 ∨ (J j).length = v)) := by
  classical
  obtain ⟨d, A, hd, hcommon, hA⟩ := hR
  have hAlen : (A i).length = (R.axis i).length := by
    rw [← (hA i).2.2.2]
    rfl
  have hAsub : (A i).carrier ⊆ B.carrier :=
    (A i).carrier_subset_of_mod_carrier_subset B (hA i).2.2.1 hBN
      (by rw [(hA i).2.2.2]; exact hsub)
  have hfitA : v ^ 2 ≤ (A i).length - 1 := by
    rw [hAlen]
    exact hfit.trans (Nat.sub_le_sub_right (R.width_le_axis_length i) 1)
  obtain ⟨M, Q, hpart, hprops, hstep⟩ :=
    (A i).partition_at_contained_step B I (hA i).1 hB hI hAsub hparallel hL hv hfitA
  have hQN (j : Fin M) : (Q j).carrier ⊆ Finset.range N :=
    (IsPartition.cell_subset hpart j).trans hIN
  have hQd (j : Fin M) : (Q j).step = d := (hstep j).trans (hA i).2.1
  have hQcast (j : Fin M) : ((Q j).toModAP N).step = R.commonDiff :=
    (congrArg (fun a : Nat => (a : ZMod N)) (hQd j)).trans hcommon
  let S (j : Fin M) := boxAppend R ((Q j).toModAP N) (hQcast j)
  have hS (j : Fin M) : (S j).IsAscendingInteger := by
    refine ⟨d, Fin.snoc A (Q j), hd, hcommon, ?_⟩
    intro a
    refine Fin.lastCases ?_ (fun b => ?_) a
    · simpa only [Fin.snoc_last, S, boxAppend] using
        (show (Q j).IsProper ∧ (Q j).step = d ∧ (Q j).carrier ⊆ Finset.range N ∧
          (Q j).toModAP N = (Q j).toModAP N from ⟨(hprops j).1, hQd j, hQN j, rfl⟩)
    · simpa only [Fin.snoc_castSucc, S, boxAppend] using hA b
  refine ⟨M, S, fun j => (Q j).toModAP N,
    boxAppend_partition R (I.toModAP N) (fun j => (Q j).toModAP N) hQcast
      (hpart.toModAP hIN), ?_, ?_, ?_⟩
  · intro j
    refine ⟨hS j, boxAppend_width_ge R ((Q j).toModAP N) (hQcast j) ?_ ?_⟩
    · have hv2 : v ≤ v ^ 2 := Nat.le_self_pow (by omega) v
      omega
    · rcases (hprops j).2.2 with h | h <;> change v - 1 ≤ (Q j).length <;> omega
  · intro j
    exact boxAppend_product R ((Q j).toModAP N) (hQcast j)
  · intro j
    exact ⟨(Q j).toModAP_hasIntegerRepresentatives (hprops j).1 (hQN j), (hprops j).2⟩

end LeanProofs.GowersSzemeredi
