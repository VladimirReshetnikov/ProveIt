import GowersSzemeredi.Section16

/-!
# Counting the induced cube domains in Section 16

This module identifies additive tuples in the fixed-side cube domain `X_h`
with general arrangements having side `h`.  Under this identification the
induced cube map is exactly the arrangement cube-value map.  The resulting
cardinality identities turn the respected-arrangement hypothesis used in
Lemma 16.5 into the `DomainApproxHomOfOrder` hypothesis of Theorem 10.13.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma section16CubeElement_side {N k : Nat} [NeZero N]
    {B : Finset (Point N (k + 1))} {h : Point N k}
    (C : Section16CubeElement B h) : C.1.1.side = h := by
  have hC := C.property
  simp only [section16CubeDomain, Finset.mem_filter, Finset.mem_univ,
    true_and] at hC
  exact hC.1

private lemma section16CubeElement_vertex_mem {N k : Nat} [NeZero N]
    {B : Finset (Point N (k + 1))} {h : Point N k}
    (C : Section16CubeElement B h) (e : Fin k → Bool) :
    appendCoordinate (C.1.1.vertex e) C.1.2 ∈ B := by
  have hC := C.property
  simp only [section16CubeDomain, Finset.mem_filter, Finset.mem_univ,
    true_and] at hC
  exact hC.2 e

@[simp] theorem section16CubeElement_card {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (h : Point N k) :
    Fintype.card (Section16CubeElement B h) =
      (section16CubeDomain B h).card := by
  exact Fintype.card_coe _

private lemma section16CubeFibre_crossSection {N k : Nat} [NeZero N]
    {B : Finset (Point N (k + 1))} {h : Point N k} {s : ZMod N}
    (C : {C : Section16CubeElement B h //
      C ∈ (section16CubeMultifunctionDomain B h).fibre s}) :
    C.1.1.2 = s := by
  have hC := C.property
  simp only [MultifunctionDomain.fibre, Finset.mem_filter, Finset.mem_univ,
    true_and, section16CubeMultifunctionDomain] at hC
  exact hC

private def section16CubeFibreBase {N k : Nat} [NeZero N]
    {B : Finset (Point N (k + 1))} {h : Point N k} {s : ZMod N}
    (C : {C : Section16CubeElement B h //
      C ∈ (section16CubeMultifunctionDomain B h).fibre s}) : Point N k :=
  C.1.1.1.base

private lemma section16CubeFibreBase_injective {N k : Nat} [NeZero N]
    {B : Finset (Point N (k + 1))} {h : Point N k} {s : ZMod N} :
    Function.Injective
      (section16CubeFibreBase (B := B) (h := h) (s := s)) := by
  intro C D hbase
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext
    · exact hbase
    · exact (section16CubeElement_side C.1).trans
        (section16CubeElement_side D.1).symm
  · exact (section16CubeFibre_crossSection C).trans
      (section16CubeFibre_crossSection D).symm

theorem section16CubeMultifunctionDomain_fibre_card_le
    {N k : Nat} [NeZero N] (B : Finset (Point N (k + 1)))
    (h : Point N k) (s : ZMod N) :
    ((section16CubeMultifunctionDomain B h).fibre s).card ≤ N ^ k := by
  classical
  calc
    ((section16CubeMultifunctionDomain B h).fibre s).card =
        Fintype.card {C : Section16CubeElement B h //
          C ∈ (section16CubeMultifunctionDomain B h).fibre s} := by
      exact (Fintype.card_coe _).symm
    _ ≤ Fintype.card (Point N k) :=
      Fintype.card_le_of_injective
        (section16CubeFibreBase (B := B) (h := h) (s := s))
        (section16CubeFibreBase_injective (B := B) (h := h) (s := s))
    _ = N ^ k := by simp [Point, ZMod.card]

private def section16IndexAdditive {N k d : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (h : Point N k)
    (x : Fin (2 * d) → Section16CubeElement B h) : Prop :=
  HasEqualHalfSums fun j ↦
    (section16CubeMultifunctionDomain B h).index (x j)

private def section16ValueAdditive {N k d : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (h : Point N k)
    (phi : Point N (k + 1) → ZMod N)
    (x : Fin (2 * d) → Section16CubeElement B h) : Prop :=
  HasEqualHalfSums fun j ↦ section16InducedCubeMap B h phi (x j)

private def section16ArrangementAtSide {N k d : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (h : Point N k)
    (R : GeneralArrangement N k d) : Prop :=
  R.IsIn B ∧ R.side = h

private def section16TupleArrangement {N k d : Nat} [NeZero N]
    {B : Finset (Point N (k + 1))} (h : Point N k)
    (x : Fin (2 * d) → Section16CubeElement B h) :
    GeneralArrangement N k d :=
  (h, (fun j ↦ (x j).1.1.base), fun j ↦ (x j).1.2)

private lemma section16TupleArrangement_vertex {N k d : Nat} [NeZero N]
    {B : Finset (Point N (k + 1))} (h : Point N k)
    (x : Fin (2 * d) → Section16CubeElement B h)
    (e : Fin k → Bool) (j : Fin (2 * d)) :
    (section16TupleArrangement h x).vertex e j =
      appendCoordinate ((x j).1.1.vertex e) (x j).1.2 := by
  change appendCoordinate
      (AxisCube.vertex ((x j).1.1.base, h) e) (x j).1.2 =
    appendCoordinate ((x j).1.1.vertex e) (x j).1.2
  have haxis : ((x j).1.1.base, h) = (x j).1.1 := by
    apply Prod.ext
    · rfl
    · exact (section16CubeElement_side (x j)).symm
  rw [haxis]

private lemma section16TupleArrangement_cubeValue {N k d : Nat} [NeZero N]
    {B : Finset (Point N (k + 1))} (h : Point N k)
    (phi : Point N (k + 1) → ZMod N)
    (x : Fin (2 * d) → Section16CubeElement B h)
    (j : Fin (2 * d)) :
    (section16TupleArrangement h x).cubeValue phi j =
      section16InducedCubeMap B h phi (x j) := by
  unfold GeneralArrangement.cubeValue section16InducedCubeMap
  apply Finset.sum_congr rfl
  intro e _
  rw [section16TupleArrangement_vertex]

private def section16ArrangementCubeElement {N k d : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (h : Point N k)
    (R : GeneralArrangement N k d)
    (hmem : ∀ e j, R.vertex e j ∈ B) (hside : R.side = h)
    (j : Fin (2 * d)) : Section16CubeElement B h :=
  ⟨((R.base j, h), R.crossSection j), by
    simp only [section16CubeDomain, Finset.mem_filter, Finset.mem_univ,
      true_and]
    refine ⟨rfl, ?_⟩
    intro e
    rw [← hside]
    simpa only [GeneralArrangement.vertex, GeneralArrangement.cube] using
      hmem e j⟩

private def section16AdditiveTupleArrangementEquiv
    {N k d : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (h : Point N k) :
    {x : Fin (2 * d) → Section16CubeElement B h //
      section16IndexAdditive B h x} ≃
    {R : GeneralArrangement N k d // section16ArrangementAtSide B h R} where
  toFun x := by
    refine ⟨section16TupleArrangement h x.1, ?_⟩
    refine ⟨⟨?_, ?_⟩, rfl⟩
    · simpa only [section16IndexAdditive, section16CubeMultifunctionDomain,
        section16TupleArrangement, GeneralArrangement.crossSection,
        HasEqualHalfSums, IsAdditiveTuple] using x.property
    · intro e j
      rw [section16TupleArrangement_vertex]
      exact section16CubeElement_vertex_mem (x.1 j) e
  invFun R := by
    refine ⟨fun j ↦
      section16ArrangementCubeElement B h R.1 R.property.1.2
        R.property.2 j, ?_⟩
    simpa only [section16IndexAdditive, section16CubeMultifunctionDomain,
      section16ArrangementCubeElement, HasEqualHalfSums, IsAdditiveTuple]
      using R.property.1.1
  left_inv x := by
    apply Subtype.ext
    funext j
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · exact (section16CubeElement_side (x.1 j)).symm
    · rfl
  right_inv R := by
    apply Subtype.ext
    rcases R with ⟨⟨side, base, cross⟩, hR⟩
    have hside : side = h := hR.2
    subst side
    rfl

private lemma section16ValueAdditive_iff_respected
    {N k d : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (h : Point N k)
    (phi : Point N (k + 1) → ZMod N)
    (x : {x : Fin (2 * d) → Section16CubeElement B h //
      section16IndexAdditive B h x}) :
    section16ValueAdditive B h phi x.1 ↔
      ((section16AdditiveTupleArrangementEquiv B h x).1).IsRespected phi := by
  change HasEqualHalfSums
      (fun j ↦ section16InducedCubeMap B h phi (x.1 j)) ↔
    IsAdditiveTuple
      (fun j ↦ (section16TupleArrangement h x.1).cubeValue phi j)
  unfold HasEqualHalfSums IsAdditiveTuple
  simp_rw [section16TupleArrangement_cubeValue]

private def section16RespectedTupleArrangementEquiv
    {N k d : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (h : Point N k)
    (phi : Point N (k + 1) → ZMod N) :
    {x : Fin (2 * d) → Section16CubeElement B h //
      section16IndexAdditive B h x ∧ section16ValueAdditive B h phi x} ≃
    {R : GeneralArrangement N k d //
      R.IsIn B ∧ R.side = h ∧ R.IsRespected phi} := by
  let e₁ := (Equiv.subtypeSubtypeEquivSubtypeInter
    (section16IndexAdditive (d := d) B h)
    (section16ValueAdditive (d := d) B h phi)).symm
  let e₂ :
      {x : {x : Fin (2 * d) → Section16CubeElement B h //
        section16IndexAdditive B h x} //
          section16ValueAdditive B h phi x.1} ≃
      {R : {R : GeneralArrangement N k d //
        section16ArrangementAtSide B h R} // R.1.IsRespected phi} :=
    (section16AdditiveTupleArrangementEquiv (d := d) B h).subtypeEquiv
      (section16ValueAdditive_iff_respected (d := d) B h phi)
  let e₃ := Equiv.subtypeSubtypeEquivSubtypeInter
    (section16ArrangementAtSide (d := d) B h)
    (fun R : GeneralArrangement N k d ↦ R.IsRespected phi)
  let e₄ :
      {R : GeneralArrangement N k d //
        section16ArrangementAtSide B h R ∧ R.IsRespected phi} ≃
      {R : GeneralArrangement N k d //
        R.IsIn B ∧ R.side = h ∧ R.IsRespected phi} :=
    Equiv.subtypeEquivRight fun R ↦ by
      constructor
      · rintro ⟨⟨hR, hside⟩, hrespected⟩
        exact ⟨hR, hside, hrespected⟩
      · rintro ⟨hR, hside, hrespected⟩
        exact ⟨⟨hR, hside⟩, hrespected⟩
  exact e₁.trans (e₂.trans (e₃.trans e₄))

private lemma section16_countWhere_eq_card_subtype
    {X : Type*} [Fintype X] (P : X → Prop)
    [Fintype {x : X // P x}] :
    countWhere P = Fintype.card {x : X // P x} := by
  classical
  unfold countWhere
  rw [Finset.filter_congr_decidable]
  exact (Fintype.card_subtype P).symm

theorem section16_domainAdditiveTupleCount_eq_arrangementCountAtSide
    {N k d : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (h : Point N k) :
    domainAdditiveTupleCount (section16CubeMultifunctionDomain B h) d =
      section16ArrangementCountAtSide d B h := by
  classical
  calc
    domainAdditiveTupleCount (section16CubeMultifunctionDomain B h) d =
        Fintype.card {x : Fin (2 * d) → Section16CubeElement B h //
          section16IndexAdditive B h x} := by
      unfold domainAdditiveTupleCount
      exact section16_countWhere_eq_card_subtype
        (fun x : Fin (2 * d) → Section16CubeElement B h ↦
          section16IndexAdditive B h x)
    _ = Fintype.card {R : GeneralArrangement N k d //
          section16ArrangementAtSide B h R} :=
      Fintype.card_congr (section16AdditiveTupleArrangementEquiv B h)
    _ = section16ArrangementCountAtSide d B h := by
      unfold section16ArrangementCountAtSide
      exact (section16_countWhere_eq_card_subtype
        (fun R : GeneralArrangement N k d ↦
          section16ArrangementAtSide B h R)).symm

theorem section16_domainPhiAdditiveTupleCount_eq_respectedArrangementCountAtSide
    {N k d : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (h : Point N k)
    (phi : Point N (k + 1) → ZMod N) :
    domainPhiAdditiveTupleCount (section16CubeMultifunctionDomain B h)
        (section16InducedCubeMap B h phi) d =
      section16RespectedArrangementCountAtSide d B phi h := by
  classical
  calc
    domainPhiAdditiveTupleCount (section16CubeMultifunctionDomain B h)
        (section16InducedCubeMap B h phi) d =
        Fintype.card {x : Fin (2 * d) → Section16CubeElement B h //
          section16IndexAdditive B h x ∧
            section16ValueAdditive B h phi x} := by
      unfold domainPhiAdditiveTupleCount
      exact section16_countWhere_eq_card_subtype
        (fun x : Fin (2 * d) → Section16CubeElement B h ↦
          section16IndexAdditive B h x ∧
            section16ValueAdditive B h phi x)
    _ = Fintype.card {R : GeneralArrangement N k d //
          R.IsIn B ∧ R.side = h ∧ R.IsRespected phi} :=
      Fintype.card_congr (section16RespectedTupleArrangementEquiv B h phi)
    _ = section16RespectedArrangementCountAtSide d B phi h := by
      unfold section16RespectedArrangementCountAtSide
      exact (section16_countWhere_eq_card_subtype
        (fun R : GeneralArrangement N k d ↦
          R.IsIn B ∧ R.side = h ∧ R.IsRespected phi)).symm

theorem section16_domainApproxHomOfOrder_iff_arrangementCounts
    {N k d : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (h : Point N k)
    (phi : Point N (k + 1) → ZMod N) (eta : Real) :
    DomainApproxHomOfOrder (section16CubeMultifunctionDomain B h)
        (section16InducedCubeMap B h phi) eta d ↔
      (1 - eta) * section16ArrangementCountAtSide d B h ≤
        section16RespectedArrangementCountAtSide d B phi h := by
  unfold DomainApproxHomOfOrder
  rw [section16_domainAdditiveTupleCount_eq_arrangementCountAtSide,
    section16_domainPhiAdditiveTupleCount_eq_respectedArrangementCountAtSide]

theorem section16_domainApproxHomOfOrder_of_arrangementCounts
    {N k d : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (h : Point N k)
    (phi : Point N (k + 1) → ZMod N) (eta : Real)
    (hcount :
      (1 - eta) * section16ArrangementCountAtSide d B h ≤
        section16RespectedArrangementCountAtSide d B phi h) :
    DomainApproxHomOfOrder (section16CubeMultifunctionDomain B h)
      (section16InducedCubeMap B h phi) eta d :=
  (section16_domainApproxHomOfOrder_iff_arrangementCounts B h phi eta).2 hcount

end LeanProofs.GowersSzemeredi
