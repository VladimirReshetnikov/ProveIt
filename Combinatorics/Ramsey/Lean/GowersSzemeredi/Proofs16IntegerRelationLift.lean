import GowersSzemeredi.Proofs16RelationLift
import GowersSzemeredi.Proofs16IntegerBaseCover
import GowersSzemeredi.Proofs16IntegerFamilyRemainder

/-! Genuine relation covers lift across an unused coordinate.
All cells retain ascending integer axes, with the original graph count,
mass and one-sixteenth exponent controls. Only a nonzero modulus is needed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem IntegerMultiplyLinearWith.relation_unused_coordinate_cover {N k m v : Nat}
    [NeZero N] {Qb Eb : Real → Real} {Λ : Finset (Point N k × ZMod N)}
    (hML : IntegerMultiplyLinearWith Qb Eb Λ)
    (epsilon : Real) (he : 0 < epsilon) (he1 : epsilon ≤ 1)
    (hQ : 0 ≤ Qb epsilon) (hE : 0 ≤ Eb epsilon)
    (T : Box N k) (I : NatAP) (hT : T.IsAscendingInteger) (hI : I.IsProper)
    (hIN : I.carrier ⊆ Finset.range N) (hstep : (I.toModAP N).step = T.commonDiff)
    (hk : 0 < k) (hm : 4 ≤ m) (hmT : m ≤ T.width) (hmI : m ≤ I.length)
    (hv : 1 ≤ v) (hfit : (v : Real) ^ 2 + 1 ≤ ((m : Real) / 8) ^ Eb epsilon) :
    ∃ (q : Nat) (G : Finset (Point N (k + 1))) (L : Nat)
      (S : Fin L → Box N (k + 1)) (mu : Fin L → Fin q → Point N (k + 1) → ZMod N),
      (q : Real) ≤ Qb epsilon ∧
      G ⊆ lastProductSet T.carrier (I.toModAP N).carrier ∧
      (1 - epsilon) * ((lastProductSet T.carrier (I.toModAP N).carrier).card : Real) ≤ G.card ∧
      IsPartition (fun j => (S j).carrier) (lastProductSet T.carrier (I.toModAP N).carrier) ∧
      (∀ j, (S j).IsAscendingInteger ∧ v - 1 ≤ (S j).width) ∧
      (∀ j i, IsMultilinear (mu j i)) ∧
      ∀ j z, z ∈ (S j).carrier → z ∈ G → ∀ y, (section16Init z, y) ∈ Λ →
        ∃ i, y = mu j i z := by
  classical
  have hIcast : (I.toModAP N).IsProper := (I.toModAP_hasIntegerRepresentatives hI hIN).isProper
  obtain ⟨q, H, b, P, n, R, mu, hq, hH, hHm, hPpart, hPasc,
      hPaxes, hPstep, hRpart, hRasc, hRwidth, hmu, hc⟩ :=
    hML.short_parent_cover epsilon he he1 hQ hE T (I.toModAP N) hT hIcast hk hm hmT hmI
  let e := section5NatFlattenEquiv n
  let R' := boxFlatten n R
  have hR'part : IsBoxPartition R' T := boxFlatten_partition T P n R hPpart hRpart
  have hvfit (j : Fin (∑ a, n a)) : v ^ 2 ≤ (R' j).width - 1 := by
    have hh := hfit.trans (hRwidth (e.symm j).1 (e.symm j).2)
    have hh' : v ^ 2 + 1 ≤ (R' j).width := by exact_mod_cast hh
    omega
  have hwidth2 (j : Fin (∑ a, n a)) : 2 ≤ (R' j).width := by
    have h := hvfit j
    have hv2 : 1 ≤ v ^ 2 := one_le_pow₀ hv
    omega
  have hne (j : Fin (∑ a, n a)) : (R' j).carrier.Nonempty :=
    (R' j).carrier_nonempty_of_axis_pos
      (fun a => (by have hw := hwidth2 j; omega : 0 < (R' j).width).trans_le
        ((R' j).width_le_axis_length a))
  let axis : Fin k := ⟨0, hk⟩
  have hsub (j : Fin (∑ a, n a)) :
      ((R' j).axis axis).carrier ⊆ ((P (e.symm j).1).axis axis).carrier :=
    (R' j).axis_carrier_subset_of_carrier_subset (P (e.symm j).1) (hne j)
      (IsPartition.cell_subset (hRpart (e.symm j).1) (e.symm j).2) axis
  choose d A hd hcommon hA using hPasc
  have hPcert (j : Fin b) : (P j).IsAscendingInteger :=
    ⟨d j, A j, hd j, hcommon j, hA j⟩
  let B (j : Fin (∑ a, n a)) := A (e.symm j).1 axis
  have hBN (j : Fin (∑ a, n a)) : (B j).carrier ⊆ Finset.range N :=
    (hA (e.symm j).1 axis).2.2.1
  have hBcast (j : Fin (∑ a, n a)) : (B j).toModAP N = (P (e.symm j).1).axis axis :=
    (hA (e.symm j).1 axis).2.2.2
  have hBlen (j : Fin (∑ a, n a)) : 2 ≤ (B j).length := by
    have hc := Finset.card_le_card (hsub j)
    rw [show ((R' j).axis axis).carrier.card = ((R' j).axis axis).length from
      (hRasc (e.symm j).1 (e.symm j).2).isProper axis,
      show ((P (e.symm j).1).axis axis).carrier.card = ((P (e.symm j).1).axis axis).length from
        (hPcert (e.symm j).1).isProper axis] at hc
    change 2 ≤ ((B j).toModAP N).length
    rw [hBcast j]
    exact (hwidth2 j).trans (((R' j).width_le_axis_length axis).trans hc)
  have hparallel (j : Fin (∑ a, n a)) : (B j).step = I.step := by
    apply (B j).step_eq_of_mod_step_eq I (hBN j) hIN (hBlen j) (by omega)
    rw [hBcast j, (P _).axis_step, hPstep, hstep]
  have hBI (j : Fin (∑ a, n a)) : (B j).length ≤ I.length := by
    change ((B j).toModAP N).length ≤ (I.toModAP N).length
    rw [hBcast j]
    exact (hPaxes (e.symm j).1 axis).2.2
  choose L S J hSpart hSasc hSprod hJ using fun j =>
    ascending_box_product_tiling_of_contained_integer_axis (R' j) (hRasc _ _) (B j) I axis
      (hA (e.symm j).1 axis).1 hI (hBN j) hIN (hparallel j)
      (by rw [hBcast j]; exact hsub j) (hBI j) hv (hvfit j)
  let fidx := section5NatFlattenEquiv L
  let G := lastProductSet H (I.toModAP N).carrier
  have hnu (j : Fin (∑ a, n a)) (i : Fin q) :
      IsMultilinear (fun z : Point N (k + 1) => mu (e.symm j).1 (e.symm j).2 i (section16Init z)) :=
    (hmu (e.symm j).1 (e.symm j).2 i).lift_last
  obtain ⟨hG, hGm⟩ := lastProductSet_good_mass T.carrier H (I.toModAP N).carrier epsilon hH hHm
  refine ⟨q, G, ∑ j, L j, boxFlatten L S,
    (fun j i z => mu (e.symm (fidx.symm j).1).1 (e.symm (fidx.symm j).1).2 i (section16Init z)),
    hq, hG, hGm, ?_, (fun j => hSasc _ _), (fun j i => hnu _ i), ?_⟩
  · exact finsetPartition_flatten L (fun j => lastProductSet (R' j).carrier (I.toModAP N).carrier)
      (lastProductSet T.carrier (I.toModAP N).carrier) (fun j a => (S j a).carrier)
      (lastProductSet_partition _ _ _ hR'part) hSpart
  · intro j z hz hzG y hy
    let a := (fidx.symm j).1
    let c := (fidx.symm j).2
    have hzR : section16Init z ∈ (R' a).carrier := by
      change z ∈ (S a c).carrier at hz
      rw [(hSprod a c).1] at hz
      exact (Finset.mem_filter.mp hz).2.1
    have hzH := (Finset.mem_filter.mp hzG).2.1
    exact hc (e.symm a).1 (e.symm a).2 (section16Init z) hzR hzH y hy

theorem IntegerMultiplyLinearWith.relation_lift_last {N k : Nat} [NeZero N]
    {Qb Eb : Real → Real} {Λ : Finset (Point N k × ZMod N)}
    (hML : IntegerMultiplyLinearWith Qb Eb Λ)
    (M : Nat) (hfib : ∀ x : Point N k, (Λ.filter fun z => z.1 = x).card ≤ M)
    (hQ : ∀ t, 0 < t → t ≤ 1 → 0 ≤ Qb t)
    (hE : ∀ t, 0 < t → t ≤ 1 → 0 < Eb t ∧ Eb t ≤ 1) (hk : 0 < k) :
    IntegerMultiplyLinearWith (fun t => max (Qb t) ((3 ^ (k + 1) * M : Nat) : Real))
      (fun t => Eb t / 16) (lastLiftRelation Λ) := by
  apply IntegerMultiplyLinearWith.of_ascending
  intro theta ht ht1 P hP
  classical
  obtain ⟨ha, ha1⟩ := hE theta ht ht1
  have hA : 0 < Eb theta / 16 := by positivity
  have hmass : (1 - theta) * (P.carrier.card : Real) ≤ P.carrier.card := by
    have hnonneg : (0 : Real) ≤ P.carrier.card := Nat.cast_nonneg _
    nlinarith only [ht, hnonneg]
  by_cases hsmall : (P.width : Real) ^ (Eb theta / 16) ≤ 2
  · obtain ⟨L, R, mu, hpart, hR, hw, hmu, hcov⟩ :=
      section16_integer_coarse_relation_cover (by omega : 0 < k + 1) (lastLiftRelation Λ) M
        (lastLiftRelation_fiber_le hfib) P hP
    refine ⟨L, 3 ^ (k + 1) * M, P.carrier, R, mu, Finset.Subset.rfl, hmass, hpart, hR,
      le_max_right _ _, ?_, hmu, fun j x hx _ y hy => hcov j x hx y hy⟩
    intro j
    have hmin : (P.width : Real) ^ (Eb theta / 16) ≤ ((min 2 P.width : Nat) : Real) := by
      rcases Nat.lt_or_ge P.width 2 with hlt | hge
      · rw [min_eq_right hlt.le]
        interval_cases h : P.width
        · simp [Real.zero_rpow hA.ne']
        · simp
      · rw [min_eq_left hge]
        exact_mod_cast hsmall
    exact hmin.trans (by exact_mod_cast hw j)
  · have hlarge : 2 < (P.width : Real) ^ (Eb theta / 16) := lt_of_not_ge hsmall
    obtain ⟨hm4, hw16, hwidth⟩ := with_lift_width_budget ha ha1 P.width hlarge
    obtain ⟨v, hv, hvfit, hvwidth⟩ := section16_lift_width_rounding hw16
    have hT : (boxInit P).IsAscendingInteger := boxInit_isAscendingInteger P hP
    obtain ⟨d, A, hd, hcommon, haxes⟩ := hP
    let I := A (Fin.last k)
    have hIeq : I.toModAP N = P.axis (Fin.last k) := (haxes _).2.2.2
    have hIstep : (I.toModAP N).step = (boxInit P).commonDiff := by
      rw [hIeq, P.axis_step]
      rfl
    have hmI : P.width ≤ I.length := by
      change P.width ≤ (I.toModAP N).length
      rw [hIeq]
      exact P.width_le_axis_length _
    obtain ⟨q, G, M', Q, mu, hq, hG, hGm, hpart, hR, hmu, hc⟩ :=
      hML.relation_unused_coordinate_cover theta ht ht1 (hQ theta ht ht1) ha.le (boxInit P) I
        hT (haxes _).1 (haxes _).2.2.1 hIstep hk hm4 (boxInit_width P hk) hmI hv hvfit
    have hprod : lastProductSet (boxInit P).carrier (I.toModAP N).carrier = P.carrier := by
      rw [hIeq]
      exact (boxInit_last_product P).1.symm
    rw [hprod] at hG hGm hpart
    refine ⟨M', q, G, Q, mu, hG, hGm, hpart, fun j => (hR j).1,
      hq.trans (le_max_left _ _), fun j => ?_, hmu, ?_⟩
    · exact hwidth.trans (hvwidth.trans (by exact_mod_cast (hR j).2))
    · intro j z hz hzG y hy
      exact hc j z hz hzG y (mem_lastLiftRelation.mp hy)

end LeanProofs.GowersSzemeredi
