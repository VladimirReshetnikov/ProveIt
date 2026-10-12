import GowersSzemeredi.Proofs16IntegerExplicitRecurrence
import GowersSzemeredi.Proofs16IntegerProductTiling

/-! Retile the final axis after a genuine common-difference recurrence.
Integer certificates and the same frequency-times-step estimate survive.
The final product need not initially have a common-step box presentation. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem ascending_retiled_product_of_recurrence {N k q v : Nat} [NeZero N]
    (P : Box N k) (B I : NatAP) (i : Fin k)
    (hB : B.IsProper) (hI : I.IsProper)
    (hBN : B.carrier ⊆ Finset.range N) (hIN : I.carrier ⊆ Finset.range N)
    (hparallel : B.step = I.step)
    (hsub : (P.axis i).carrier ⊆ (B.toModAP N).carrier) (hL : B.length ≤ I.length)
    (mu : Fin q → Point N k → ZMod N) (scale error : Real)
    (hrec : ∃ M : Nat, ∃ R : Fin M → Box N k,
      IsBoxPartition R P ∧ (∀ j, (R j).IsAscendingInteger) ∧
      (∀ j, scale ≤ (R j).width) ∧
      ∀ a j x, x ∈ (R j).carrier →
        (centeredAbs (mu a x * (R j).commonDiff) : Real) ≤ error * N)
    (hv : 2 ≤ v) (hvscale : (v : Real) ^ 2 + 1 ≤ scale) :
    ∃ M : Nat, ∃ S : Fin M → Box N (k + 1), ∃ T : Fin M → Box N k,
      ∃ J : Fin M → ModAP N,
      IsPartition (fun j => (S j).carrier) (lastProductSet P.carrier (I.toModAP N).carrier) ∧
      (∀ j, (S j).IsAscendingInteger ∧ v - 1 ≤ (S j).width) ∧
      (∀ j, (T j).IsAscendingInteger) ∧
      (∀ j, IsLastCoordinateBoxProduct (S j) (T j) (J j)) ∧
      (∀ j, (T j).carrier ⊆ P.carrier) ∧
      (∀ j, (J j).HasIntegerRepresentatives ∧ 0 < (J j).length ∧ (J j).length ≤ v) ∧
      ∀ a j x, x ∈ (T j).carrier →
        (centeredAbs (mu a x * (J j).step) : Real) ≤ error * N := by
  classical
  obtain ⟨M, R, hpart, hR, hwidth, hsmall⟩ := hrec
  have hfit (j : Fin M) : v ^ 2 ≤ (R j).width - 1 := by
    have h := hvscale.trans (hwidth j)
    have h' : v ^ 2 + 1 ≤ (R j).width := by exact_mod_cast h
    omega
  have hnonempty (j : Fin M) : (R j).carrier.Nonempty := by
    apply Box.carrier_nonempty_of_axis_pos
    intro a
    have h := (R j).width_le_axis_length a
    have h' := hfit j
    have hv2 : 1 ≤ v ^ 2 := one_le_pow₀ (by omega)
    omega
  have hsub' (j : Fin M) : ((R j).axis i).carrier ⊆ (B.toModAP N).carrier :=
    ((R j).axis_carrier_subset_of_carrier_subset P (hnonempty j)
      (IsPartition.cell_subset hpart j) i).trans hsub
  choose L S J hSpart hSprop hSproduct hJlength using fun j =>
    ascending_box_product_tiling_of_contained_integer_axis (R j) (hR j) B I i
      hB hI hBN hIN hparallel (hsub' j) hL (by omega : 1 ≤ v) (hfit j)
  let e := section5NatFlattenEquiv L
  refine ⟨∑ j, L j, boxFlatten L S, (fun j => R (e.symm j).1),
    (fun j => J (e.symm j).1 (e.symm j).2),
    finsetPartition_flatten L (fun j => lastProductSet (R j).carrier (I.toModAP N).carrier)
      (lastProductSet P.carrier (I.toModAP N).carrier) (fun j a => (S j a).carrier)
      (lastProductSet_partition _ _ _ hpart) hSpart,
    (fun j => hSprop _ _), (fun j => hR _), (fun j => hSproduct _ _),
    (fun j => IsPartition.cell_subset hpart _), ?_, ?_⟩
  · intro j
    have h := hJlength (e.symm j).1 (e.symm j).2
    refine ⟨h.1, h.2.1, ?_⟩
    change (J (e.symm j).1 (e.symm j).2).length ≤ v
    rcases h.2.2 with h | h <;> omega
  · intro a j x hx
    have hp := hSproduct (e.symm j).1 (e.symm j).2
    rw [hp.2.2, hp.2.1]
    exact hsmall a _ x hx

theorem ascending_retiled_linearity_family_of_recurrence_scale {N k q : Nat}
    [NeZero N] {ι : Type} (P : Box N k) (B I : NatAP) (i : Fin k)
    (hB : B.IsProper) (hI : I.IsProper)
    (hBN : B.carrier ⊆ Finset.range N) (hIN : I.carrier ⊆ Finset.range N)
    (hparallel : B.step = I.step)
    (hsub : (P.axis i).carrier ⊆ (B.toModAP N).carrier) (hL : B.length ≤ I.length)
    (mu : Fin q → Point N k → ZMod N) (s zeta : Real) (hs : 0 < s)
    (hz : 0 < zeta) (hzHalf : zeta ≤ 1 / 2)
    (hrec : ∃ M : Nat, ∃ R : Fin M → Box N k,
      IsBoxPartition R P ∧ (∀ j, (R j).IsAscendingInteger) ∧
      (∀ j, s ≤ (R j).width) ∧
      ∀ a j x, x ∈ (R j).carrier →
        (centeredAbs (mu a x * (R j).commonDiff) : Real) ≤ (2 / s) * N)
    (K : ι → Point N k → Finset (ZMod N)) (G : ι → Finset (Point N k))
    (A : ι → Point N k → Finset (ZMod N)) (f : ι → Point N k → ZMod N → ZMod N)
    (hcover : ∀ c, ∀ x ∈ P.carrier, x ∈ G c → ∀ r ∈ K c x, ∃ a, r = mu a x)
    (hlinear : ∀ c, ∀ x ∈ G c, ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
      J.step ∈ bohr (K c x) (zeta / v) → LinearOn (J.carrier ∩ A c x) (f c x))
    (hlarge : 1 < (zeta / 2) * Real.sqrt s) :
    ∃ M : Nat, ∃ S : Fin M → Box N (k + 1), ∃ T : Fin M → Box N k,
      ∃ J : Fin M → ModAP N,
      IsPartition (fun j => (S j).carrier) (lastProductSet P.carrier (I.toModAP N).carrier) ∧
      (∀ j, (S j).IsAscendingInteger ∧ (zeta / 2) * Real.sqrt s ≤ (S j).width) ∧
      (∀ j, (T j).IsAscendingInteger) ∧
      (∀ j, IsLastCoordinateBoxProduct (S j) (T j) (J j)) ∧
      (∀ j, (J j).HasIntegerRepresentatives) ∧
      ∀ c j x, x ∈ (T j).carrier → x ∈ G c → LinearOn ((J j).carrier ∩ A c x) (f c x) := by
  obtain ⟨v, hv, hvwidth, hvscale, hvbudget⟩ :=
    section16_short_scale_margin s zeta hs hz hzHalf hlarge
  obtain ⟨M, S, T, J, hpart, hS, hT, hproduct, hTsub, hJ, hsmall⟩ :=
    ascending_retiled_product_of_recurrence P B I i hB hI hBN hIN hparallel hsub hL
      mu s (2 / s) hrec hv hvscale
  refine ⟨M, S, T, J, hpart, ?_, hT, hproduct, fun j => (hJ j).1, ?_⟩
  · intro j
    exact ⟨(hS j).1, hvwidth.trans (by exact_mod_cast (hS j).2)⟩
  · intro c j x hx hxG
    exact hlinear c x hxG v (by omega) (J j) (hJ j).2.2
      (product_recurrence_bohr_mem mu (K c) x (J j).step _ zeta v
        (hcover c x (hTsub j hx) hxG) (fun a => hsmall a j x hx) hvbudget)

theorem IntegerSection16RecurrenceProfileWith.retiled_family {k : Nat}
    {Thr : Nat → Nat} {Exp : Nat → Real}
    (hrec : IntegerSection16RecurrenceProfileWith k Thr Exp)
    (hThr : ∀ q, 0 < Thr q) (q : Nat)
    (N m : Nat) [NeZero N] (P : Box N k) (hP : P.HasIntegerRepresentatives)
    (B I : NatAP) (i : Fin k) (hB : B.IsProper) (hI : I.IsProper)
    (hBN : B.carrier ⊆ Finset.range N) (hIN : I.carrier ⊆ Finset.range N)
    (hparallel : B.step = I.step)
    (hsub : (P.axis i).carrier ⊆ (B.toModAP N).carrier) (hL : B.length ≤ I.length)
    (mu : Fin q → Point N k → ZMod N) (hmu : ∀ a, IsMultilinear (mu a))
    (hm : Thr q ≤ m) (hmP : m ≤ P.width)
    (ι : Type) (K : ι → Point N k → Finset (ZMod N)) (G : ι → Finset (Point N k))
    (A : ι → Point N k → Finset (ZMod N)) (f : ι → Point N k → ZMod N → ZMod N)
    (zeta : Real) (hz : 0 < zeta) (hzHalf : zeta ≤ 1 / 2)
    (hcover : ∀ c, ∀ x ∈ P.carrier, x ∈ G c → ∀ r ∈ K c x, ∃ a, r = mu a x)
    (hlinear : ∀ c, ∀ x ∈ G c, ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
      J.step ∈ bohr (K c x) (zeta / v) → LinearOn (J.carrier ∩ A c x) (f c x))
    (hlarge : 1 < (zeta / 2) * Real.sqrt ((m : Real) ^ Exp q)) :
    ∃ M : Nat, ∃ S : Fin M → Box N (k + 1), ∃ T : Fin M → Box N k,
      ∃ J : Fin M → ModAP N,
      IsPartition (fun j => (S j).carrier) (lastProductSet P.carrier (I.toModAP N).carrier) ∧
      (∀ j, (S j).IsAscendingInteger ∧
        (zeta / 2) * Real.sqrt ((m : Real) ^ Exp q) ≤ (S j).width) ∧
      (∀ j, (T j).IsAscendingInteger) ∧
      (∀ j, IsLastCoordinateBoxProduct (S j) (T j) (J j)) ∧
      (∀ j, (J j).HasIntegerRepresentatives) ∧
      ∀ c j x, x ∈ (T j).carrier → x ∈ G c → LinearOn ((J j).carrier ∩ A c x) (f c x) := by
  have hm0 : 0 < m := (hThr q).trans_le hm
  have hmR : (0 : Real) < m := by exact_mod_cast hm0
  apply ascending_retiled_linearity_family_of_recurrence_scale P B I i hB hI hBN hIN
    hparallel hsub hL mu _ zeta (Real.rpow_pos_of_pos hmR _) hz hzHalf _
    K G A f hcover hlinear hlarge
  simpa only [Real.rpow_neg hmR.le, div_eq_mul_inv] using
    hrec N q m P hP mu hmu hm hmP

end LeanProofs.GowersSzemeredi
