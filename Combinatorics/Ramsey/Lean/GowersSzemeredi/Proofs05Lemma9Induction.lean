import GowersSzemeredi.Proofs05Lemma9
import GowersSzemeredi.Proofs05Downstream
import Mathlib.Data.Fintype.EquivFin

/-!
# The refinement engine for Lemma 5.9

This module separates the combinatorial induction needed for simultaneous
polynomial partitioning from its quantitative scale schedule.  Its first
layer transports the strong one-polynomial API from an index interval to an
arbitrary proper natural-number progression.  All progressions remain in the
original natural index set; no modular injectivity beyond `r <= N` is hidden
in the construction.

The 19 declarations of this module that the final route does not use are in
`Proofs05Lemma9InductionSide`. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ## Natural-progression transport -/

/-- The point of `P` with natural index `t`. -/
def section5NatIndexPoint (P : NatAP) (t : Nat) : Nat :=
  P.start + t * P.step

/-- Composition of a progression of indices with a natural progression. -/
def section5NatTransport (P R : NatAP) : NatAP where
  start := section5NatIndexPoint P R.start
  step := R.step * P.step
  length := R.length

@[simp] theorem section5NatTransport_length (P R : NatAP) :
    (section5NatTransport P R).length = R.length :=
  rfl

theorem section5Nat_carrier_eq_image_range (P : NatAP) :
    P.carrier = (Finset.range P.length).image (section5NatIndexPoint P) := by
  ext x
  unfold NatAP.carrier section5NatIndexPoint
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

theorem section5NatTransport_carrier (P R : NatAP) :
    (section5NatTransport P R).carrier =
      R.carrier.image (section5NatIndexPoint P) := by
  ext x
  simp only [NatAP.carrier, section5NatTransport, section5NatIndexPoint,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨R.start + (i : Nat) * R.step, ⟨i, rfl⟩, ?_⟩
    ring
  · rintro ⟨t, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    ring

theorem section5NatIndexPoint_injective (P : NatAP) (hstep : 0 < P.step) :
    Function.Injective (section5NatIndexPoint P) := by
  intro x y hxy
  unfold section5NatIndexPoint at hxy
  exact Nat.mul_right_cancel hstep (Nat.add_left_cancel hxy)

theorem section5NatTransport_isProper (P R : NatAP)
    (hP : P.IsProper) (hR : R.IsProper) :
    (section5NatTransport P R).IsProper := by
  constructor
  · exact Nat.mul_pos hR.1 hP.1
  · rw [section5NatTransport_carrier, Finset.card_image_iff.mpr]
    · exact hR.2
    · exact (section5NatIndexPoint_injective P hP.1).injOn

theorem section5NatTransport_subset (P R : NatAP)
    (hR : R.carrier ⊆ Finset.range P.length) :
    (section5NatTransport P R).carrier ⊆ P.carrier := by
  rw [section5NatTransport_carrier, section5Nat_carrier_eq_image_range P]
  exact Finset.image_mono (section5NatIndexPoint P) hR

/-- Transporting an interval partition through a proper natural progression
gives a partition of that progression. -/
theorem section5NatTransport_partition {M : Nat} (P : NatAP)
    (R : Fin M -> NatAP) (hP : P.IsProper)
    (hR : IsNatAPPartition R (Finset.range P.length)) :
    IsNatAPPartition (fun j => section5NatTransport P (R j)) P.carrier := by
  have hinj := section5NatIndexPoint_injective P hP.1
  constructor
  · intro x
    constructor
    · intro hx
      rw [section5Nat_carrier_eq_image_range] at hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, htj⟩ := (hR.1 t).mp ht
      refine ⟨j, ?_⟩
      change section5NatIndexPoint P t ∈ (section5NatTransport P (R j)).carrier
      rw [section5NatTransport_carrier]
      exact Finset.mem_image.mpr ⟨t, htj, rfl⟩
    · rintro ⟨j, hx⟩
      exact section5NatTransport_subset P (R j)
        (IsPartition.cell_subset hR j) hx
  · intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    change x ∈ (section5NatTransport P (R i)).carrier at hxi
    change x ∈ (section5NatTransport P (R j)).carrier at hxj
    rw [section5NatTransport_carrier] at hxi hxj
    obtain ⟨s, hsi, hsx⟩ := Finset.mem_image.mp hxi
    obtain ⟨t, htj, htx⟩ := Finset.mem_image.mp hxj
    have hst : s = t := hinj (hsx.trans htx.symm)
    subst t
    exact Finset.disjoint_left.mp (hR.2 i j hij) hsi htj

theorem section5NatIndexPoint_cast {N : Nat} (P : NatAP) (t : Nat) :
    (section5NatIndexPoint P t : ZMod N) =
      (P.start : ZMod N) + (t : ZMod N) * (P.step : ZMod N) := by
  unfold section5NatIndexPoint
  push_cast
  rfl

/-! ## Monotonicity needed by the iteration -/

theorem diameterAtMostReal_mono {N : Nat} {A B : Finset (ZMod N)}
    {s t : Real} (hAB : A ⊆ B) (hB : diameterAtMostReal B s)
    (hst : s <= t) : diameterAtMostReal A t := by
  obtain ⟨d, hd, hdscale⟩ := hB
  obtain ⟨a, ha⟩ := hd
  exact ⟨d, ⟨a, hAB.trans ha⟩, hdscale.trans hst⟩

/-! ## Dependent flattening for natural progressions -/

/-- The canonical finite reindexing used to flatten dependent refinements. -/
noncomputable def section5NatFlattenEquiv {M : Nat} (L : Fin M -> Nat) :
    (Sigma fun i : Fin M => Fin (L i)) ≃ Fin (∑ i, L i) :=
  Fintype.equivFinOfCardEq (by simp)

/-- Flatten a dependent family of natural progressions. -/
noncomputable def section5NatFlatten {M : Nat} (L : Fin M -> Nat)
    (R : (i : Fin M) -> Fin (L i) -> NatAP) :
    Fin (∑ i, L i) -> NatAP := fun j =>
  let z := (section5NatFlattenEquiv L).symm j
  R z.1 z.2

/-- Flattening dependent local partitions gives a partition of the original
natural progression. -/
theorem section5NatFlatten_partition {M : Nat} (P : Fin M -> NatAP)
    (S : Finset Nat) (L : Fin M -> Nat)
    (R : (i : Fin M) -> Fin (L i) -> NatAP)
    (hP : IsNatAPPartition P S)
    (hR : forall i, IsNatAPPartition (R i) (P i).carrier) :
    IsNatAPPartition (section5NatFlatten L R) S := by
  let e := section5NatFlattenEquiv L
  have hsigma := IsPartition.sigma L (fun i => (P i).carrier) S
    (fun i j => (R i j).carrier) hP hR
  constructor
  · intro x
    rw [hsigma.1 x]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨e z, ?_⟩
      change x ∈
        (R ((section5NatFlattenEquiv L).symm (section5NatFlattenEquiv L z)).1
          ((section5NatFlattenEquiv L).symm (section5NatFlattenEquiv L z)).2).carrier
      rw [(section5NatFlattenEquiv L).symm_apply_apply z]
      exact hz
    · rintro ⟨j, hj⟩
      refine ⟨e.symm j, ?_⟩
      simpa only [section5NatFlatten, e] using hj
  · intro i j hij
    have hij' : i ≠ j := bne_iff_ne.mp hij
    have hpre : e.symm i ≠ e.symm j := fun h => hij' (e.symm.injective h)
    simpa only [section5NatFlatten, e] using
      hsigma.2 (e.symm i) (e.symm j) (bne_iff_ne.mpr hpre)

theorem section5NatFlatten_isProper {M : Nat} (L : Fin M -> Nat)
    (R : (i : Fin M) -> Fin (L i) -> NatAP)
    (hR : forall i j, (R i j).IsProper) :
    forall j, (section5NatFlatten L R j).IsProper := by
  intro j
  let z := (section5NatFlattenEquiv L).symm j
  simpa only [section5NatFlatten, z] using hR z.1 z.2

/-! ## Reduction of the live statement to a quantitative schedule -/

/-- The initial natural progression whose carrier is `range r`. -/
def section5RangeNatAP (r : Nat) : NatAP where
  start := 0
  step := 1
  length := r

@[simp] theorem section5RangeNatAP_length (r : Nat) :
    (section5RangeNatAP r).length = r :=
  rfl

@[simp] theorem section5RangeNatAP_carrier (r : Nat) :
    (section5RangeNatAP r).carrier = Finset.range r := by
  ext x
  simp only [NatAP.carrier, section5RangeNatAP, Finset.mem_image,
    Finset.mem_univ, true_and, Finset.mem_range, zero_add, mul_one]
  constructor
  · rintro ⟨i, rfl⟩
    exact i.isLt
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

end LeanProofs.GowersSzemeredi
