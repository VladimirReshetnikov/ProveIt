import GowersSzemeredi.Proofs05BoxPartition

/-! # Transporting proper box refinements from index coordinates -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace LeanProofs.GowersSzemeredi

/-- The zero-based modular interval agrees with the cast natural interval. -/
theorem modInterval_zero_carrier {N L : Nat} :
    (modInterval N 0 L).carrier = (Finset.range L).image (fun t : Nat => (t : ZMod N)) := by
  rw [section5_carrier_eq_image_range]
  change (Finset.range L).image (fun t : Nat => (0 : ZMod N) + (t : ZMod N) * 1) = _
  simp

/-- Initial intervals of length at most N are proper. -/
theorem modInterval_zero_isProper {N L : Nat} [NeZero N] (hL : L ≤ N) :
    (modInterval N 0 L).IsProper := by
  rw [ModAP.IsProper, modInterval_zero_carrier, Finset.card_image_iff.mpr]
  · simp [modInterval]
  · intro x hx y hy hxy
    have hxN : x < N := (Finset.mem_range.mp hx).trans_le hL
    have hyN : y < N := (Finset.mem_range.mp hy).trans_le hL
    have h := congrArg ZMod.val hxy
    simpa only [ZMod.val_natCast_of_lt hxN, ZMod.val_natCast_of_lt hyN] using h

/-- The affine map of a proper progression is injective on its index interval. -/
theorem modAP_affine_injective_on_indices {N : Nat} [NeZero N]
    (P : ModAP N) (hP : P.IsProper) :
    Set.InjOn (fun t : ZMod N => P.start + P.step * t)
      ((modInterval N 0 P.length).carrier : Set (ZMod N)) := by
  intro x hx y hy hxy
  rw [modInterval_zero_carrier] at hx hy
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
  have hst : s = t := section5IndexPoint_injective_on_range P hP hs ht
    (by simpa [section5IndexPoint, mul_comm] using hxy)
  rw [hst]

/-- Apply the affine parametrization of one progression to another. -/
def modAPAffine {N : Nat} (P R : ModAP N) : ModAP N where
  start := P.start + P.step * R.start
  step := P.step * R.step
  length := R.length

theorem modAPAffine_carrier {N : Nat} (P R : ModAP N) :
    (modAPAffine P R).carrier = R.carrier.image (fun t => P.start + P.step * t) := by
  classical
  unfold ModAP.carrier
  rw [Finset.image_image]
  apply Finset.image_congr
  intro i _
  dsimp [modAPAffine]
  ring

theorem modAPAffine_isProper {N : Nat} [NeZero N] (P R : ModAP N)
    (hP : P.IsProper) (hR : R.IsProper)
    (hsub : R.carrier ⊆ (modInterval N 0 P.length).carrier) :
    (modAPAffine P R).IsProper := by
  rw [ModAP.IsProper, modAPAffine_carrier,
    Finset.card_image_iff.mpr ((modAP_affine_injective_on_indices P hP).mono hsub)]
  exact hR

/-- The modular index model has difference one and the same axis lengths. -/
def boxIndexModel {N k : Nat} (P : Box N k) : Box N k where
  axis i := modInterval N 0 (P.axis i).length
  commonDiff := 1
  axis_step _i := rfl

/-- The index model of a proper box is proper. -/
theorem boxIndexModel_isProper {N k : Nat} [NeZero N]
    (P : Box N k) (hP : P.IsProper) : (boxIndexModel P).IsProper := by
  intro i
  apply modInterval_zero_isProper
  rw [← hP i]
  simpa using Finset.card_le_univ (P.axis i).carrier

@[simp] theorem boxIndexModel_width {N k : Nat} (P : Box N k) :
    (boxIndexModel P).width = P.width := by
  simp [Box.width, boxIndexModel, modInterval]

/-- The coordinatewise affine map from index coordinates. -/
def boxAffinePoint {N k : Nat} (P : Box N k) (t : Point N k) : Point N k :=
  fun i => (P.axis i).start + P.commonDiff * t i

/-- Transport a modular box through the affine parametrization. -/
def boxAffineTransport {N k : Nat} (P Q : Box N k) : Box N k where
  axis i := modAPAffine (P.axis i) (Q.axis i)
  commonDiff := P.commonDiff * Q.commonDiff
  axis_step i := by simp [modAPAffine, P.axis_step, Q.axis_step]

@[simp] theorem boxAffineTransport_width {N k : Nat} (P Q : Box N k) :
    (boxAffineTransport P Q).width = Q.width := by
  simp [Box.width, boxAffineTransport, modAPAffine]

/-- Affine transport commutes with the Cartesian product carrier. -/
theorem boxAffineTransport_carrier {N k : Nat} [NeZero N] (P Q : Box N k) :
    (boxAffineTransport P Q).carrier = Q.carrier.image (boxAffinePoint P) := by
  classical
  ext x
  simp only [Box.carrier, Finset.mem_filter, Finset.mem_univ, true_and,
    boxAffineTransport, modAPAffine_carrier, Finset.mem_image]
  constructor
  · intro hx
    choose t ht heq using hx
    refine ⟨t, ht, ?_⟩
    funext i
    simpa [boxAffinePoint, P.axis_step] using heq i
  · rintro ⟨t, ht, rfl⟩ i
    exact ⟨t i, ht i, by simp [boxAffinePoint, P.axis_step]⟩

/-- Transporting the full index model recovers the original carrier. -/
theorem boxAffinePoint_image_indexModel {N k : Nat} [NeZero N] (P : Box N k) :
    (boxIndexModel P).carrier.image (boxAffinePoint P) = P.carrier := by
  rw [← boxAffineTransport_carrier]
  simp [Box.carrier, boxAffineTransport, boxIndexModel, modAPAffine,
    modInterval, ModAP.carrier, P.axis_step]

/-- Coordinatewise injectivity holds throughout a proper index model. -/
theorem boxAffinePoint_injective_on_indexModel {N k : Nat} [NeZero N]
    (P : Box N k) (hP : P.IsProper) :
    Set.InjOn (boxAffinePoint P) ((boxIndexModel P).carrier : Set (Point N k)) := by
  intro x hx y hy hxy
  have hx' : ∀ i, x i ∈ (modInterval N 0 (P.axis i).length).carrier := by
    simpa only [Finset.mem_coe, Box.carrier, boxIndexModel, Finset.mem_filter, Finset.mem_univ, true_and] using hx
  have hy' : ∀ i, y i ∈ (modInterval N 0 (P.axis i).length).carrier := by
    simpa only [Finset.mem_coe, Box.carrier, boxIndexModel, Finset.mem_filter, Finset.mem_univ, true_and] using hy
  funext i
  apply modAP_affine_injective_on_indices (P.axis i) (hP i) (hx' i) (hy' i)
  simpa only [boxAffinePoint, P.axis_step] using congrFun hxy i

/-- Every coordinate of a nonempty box can be realized by a point of the box. -/
theorem Box.axis_carrier_subset_of_carrier_subset {N k : Nat} [NeZero N]
    (Q R : Box N k) (hQ : Q.carrier.Nonempty) (hsub : Q.carrier ⊆ R.carrier)
    (i : Fin k) : (Q.axis i).carrier ⊆ (R.axis i).carrier := by
  classical
  obtain ⟨x, hx⟩ := hQ
  have hx' : ∀ j, x j ∈ (Q.axis j).carrier := by
    simpa only [Box.carrier, Finset.mem_filter, Finset.mem_univ, true_and] using hx
  intro y hy
  let z := Function.update x i y
  have hz : z ∈ Q.carrier := by
    simp only [Box.carrier, Finset.mem_filter, Finset.mem_univ, true_and]
    intro j
    by_cases hji : j = i
    · subst j; simpa [z] using hy
    · simpa [z, hji] using hx' j
  have hz' := hsub hz
  have hzi : z i ∈ (R.axis i).carrier := by
    exact (Finset.mem_filter.mp hz').2 i
  simpa [z] using hzi

/-- Positive axis lengths make the box nonempty. -/
theorem Box.carrier_nonempty_of_axis_pos {N k : Nat} [NeZero N]
    (P : Box N k) (hP : ∀ i, 0 < (P.axis i).length) : P.carrier.Nonempty := by
  classical
  refine ⟨fun i => (P.axis i).start, ?_⟩
  simp only [Box.carrier, Finset.mem_filter, Finset.mem_univ, true_and]
  intro i
  apply Finset.mem_image.mpr
  exact ⟨⟨0, hP i⟩, Finset.mem_univ _, by simp⟩

/-- A nonempty proper child in index coordinates transports to a proper box. -/
theorem boxAffineTransport_isProper {N k : Nat} [NeZero N]
    (P Q : Box N k) (hP : P.IsProper) (hQ : Q.IsProper)
    (hne : Q.carrier.Nonempty) (hsub : Q.carrier ⊆ (boxIndexModel P).carrier) :
    (boxAffineTransport P Q).IsProper := by
  intro i
  exact modAPAffine_isProper (P.axis i) (Q.axis i) (hP i) (hQ i)
    (Q.axis_carrier_subset_of_carrier_subset (boxIndexModel P) hne hsub i)

/-- Proper affine index maps transport entire partitions exactly. -/
theorem boxAffineTransport_partition {N k M : Nat} [NeZero N]
    (P : Box N k) (hP : P.IsProper) (Q : Fin M → Box N k)
    (hQ : IsBoxPartition Q (boxIndexModel P)) :
    IsBoxPartition (fun j => boxAffineTransport P (Q j)) P := by
  constructor
  · intro x
    rw [← boxAffinePoint_image_indexModel P]
    simp only [boxAffineTransport_carrier, Finset.mem_image]
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨j, hj⟩ := (hQ.1 t).mp ht
      exact ⟨j, t, hj, rfl⟩
    · rintro ⟨j, t, ht, rfl⟩
      exact ⟨t, (hQ.1 t).mpr ⟨j, ht⟩, rfl⟩
  · intro i j hij
    change Disjoint (boxAffineTransport P (Q i)).carrier (boxAffineTransport P (Q j)).carrier
    rw [boxAffineTransport_carrier, boxAffineTransport_carrier]
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp hy
    have hst : t = s := boxAffinePoint_injective_on_indexModel P hP
      (IsPartition.cell_subset hQ j ht) (IsPartition.cell_subset hQ i hs) heq
    subst t
    exact Finset.disjoint_left.mp (hQ.2 i j hij) hs ht

/-- Flatten the local refinements of a finite family of boxes. -/
def boxFlatten {N k M : Nat} (L : Fin M → Nat)
    (R : (i : Fin M) → Fin (L i) → Box N k) : Fin (∑ i, L i) → Box N k :=
  fun j => let z := (section5NatFlattenEquiv L).symm j; R z.1 z.2

private theorem box_sigma_partition {X : Type*} [DecidableEq X]
    {M : Nat} (L : Fin M -> Nat) (A : Fin M -> Finset X) (S : Finset X)
    (B : (i : Fin M) -> Fin (L i) -> Finset X)
    (hA : IsPartition A S) (hB : forall i, IsPartition (B i) (A i)) :
    (forall x, x ∈ S <->
      exists z : Sigma fun i : Fin M => Fin (L i), x ∈ B z.1 z.2) /\
      forall z w : Sigma fun i : Fin M => Fin (L i), z != w ->
        Disjoint (B z.1 z.2) (B w.1 w.2) := by
  constructor
  · intro x
    rw [hA.1]
    constructor
    · rintro ⟨i, hi⟩
      obtain ⟨j, hj⟩ := (hB i).1 x |>.mp hi
      exact ⟨⟨i, j⟩, hj⟩
    · rintro ⟨⟨i, j⟩, hij⟩
      exact ⟨i, (hB i).1 x |>.mpr ⟨j, hij⟩⟩
  · intro z w hzw
    have hzw' : z ≠ w := bne_iff_ne.mp hzw
    by_cases hi : z.1 = w.1
    · rcases z with ⟨i, j⟩
      rcases w with ⟨i', j'⟩
      dsimp only at hi ⊢
      subst i'
      have hj : j ≠ j' := by
        intro h
        subst j'
        exact hzw' rfl
      exact (hB i).2 j j' (bne_iff_ne.mpr hj)
    · exact Disjoint.mono (IsPartition.cell_subset (hB z.1) z.2)
        (IsPartition.cell_subset (hB w.1) w.2)
        (hA.2 z.1 w.1 (bne_iff_ne.mpr hi))

/-- Flattened proper-box refinements cover the original box exactly. -/
theorem boxFlatten_partition {N k M : Nat} [NeZero N]
    (P : Box N k) (Q : Fin M → Box N k) (L : Fin M → Nat)
    (R : (i : Fin M) → Fin (L i) → Box N k)
    (hQ : IsBoxPartition Q P) (hR : ∀ i, IsBoxPartition (R i) (Q i)) :
    IsBoxPartition (boxFlatten L R) P := by
  classical
  let e := section5NatFlattenEquiv L
  have hsigma := box_sigma_partition L (fun i => (Q i).carrier) P.carrier
    (fun i j => (R i j).carrier) hQ hR
  constructor
  · intro x
    rw [hsigma.1 x]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨e z, ?_⟩
      change x ∈ (R (e.symm (e z)).1 (e.symm (e z)).2).carrier
      rw [e.symm_apply_apply]
      exact hz
    · rintro ⟨j, hj⟩
      exact ⟨e.symm j, hj⟩
  · intro i j hij
    have hpre : e.symm i ≠ e.symm j := fun h => (bne_iff_ne.mp hij) (e.symm.injective h)
    exact hsigma.2 (e.symm i) (e.symm j) (bne_iff_ne.mpr hpre)

end LeanProofs.GowersSzemeredi
