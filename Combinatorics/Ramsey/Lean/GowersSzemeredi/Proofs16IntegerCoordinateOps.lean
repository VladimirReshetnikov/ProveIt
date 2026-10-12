import GowersSzemeredi.Proofs16IntegerRelationLift
import GowersSzemeredi.Proofs16FaceLifts

/-! Coordinate permutations and arbitrary-axis cylinders retain genuine
integer boxes and the original cover controls, over any nonzero modulus. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem Box.IsAscendingInteger.coordinateReindex {N k : Nat} {P : Box N k}
    (h : P.IsAscendingInteger) (e : Fin k ≃ Fin k) : (P.coordinateReindex e).IsAscendingInteger := by
  obtain ⟨d, A, hd, hcommon, hA⟩ := h
  exact ⟨d, fun i => A (e i), hd, hcommon, fun i => hA (e i)⟩

theorem Box.HasIntegerRepresentatives.coordinateReindex {N k : Nat} {P : Box N k}
    (h : P.HasIntegerRepresentatives) (e : Fin k ≃ Fin k) :
    (P.coordinateReindex e).HasIntegerRepresentatives := by
  obtain ⟨d, hd, hcast, A, hA⟩ := h
  exact ⟨d, hd, hcast, fun i => A (e i), fun i => hA (e i)⟩

theorem IntegerMultiplyLinearWith.coordinateReindex {N k : Nat} [NeZero N]
    {Qb Eb : Real → Real} {Gamma : Finset (Point N k × ZMod N)}
    (h : IntegerMultiplyLinearWith Qb Eb Gamma) (e : Fin k ≃ Fin k) :
    IntegerMultiplyLinearWith Qb Eb
      (Gamma.image (fun z => (LeanProofs.GowersSzemeredi.coordinateReindex e z.1, z.2))) := by
  classical
  intro theta ht ht1 P hP
  obtain ⟨M, q, H, Q, mu, hH, hHcard, hpart, hproper, hq, hwidth, hmu, hcover⟩ :=
    h theta ht ht1 (P.coordinateReindex e.symm) (hP.coordinateReindex e.symm)
  refine ⟨M, q, H.image (LeanProofs.GowersSzemeredi.coordinateReindex e),
    fun j => (Q j).coordinateReindex e,
    fun j i x => mu j i (LeanProofs.GowersSzemeredi.coordinateReindex e.symm x),
    ?_, ?_, ?_, fun j => (hproper j).coordinateReindex e, hq, ?_,
    fun j i => (hmu j i).coordinateReindex e.symm, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hh := (Box.coordinateReindex_mem_carrier (P.coordinateReindex e.symm) e y).mpr (hH hy)
    simpa only [Box.coordinateReindex_symm'] using hh
  · rw [Finset.card_image_of_injective _ (LeanProofs.GowersSzemeredi.coordinateReindex e).injective]
    simpa using hHcard
  · simpa using hpart.coordinateReindex e
  · intro j
    simpa using hwidth j
  · intro j x hx hh y hxy
    obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp hxy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    have haQ := (Box.coordinateReindex_mem_carrier (Q j) e a).mp hx
    have haH := (LeanProofs.GowersSzemeredi.coordinateReindex e).injective.mem_finset_image.mp hh
    obtain ⟨i, hi⟩ := hcover j a haQ haH b hab
    exact ⟨i, by simpa using hi⟩

theorem IntegerMultiplyLinearWith.coordinateReindex_graph {N k : Nat} [NeZero N]
    {Qb Eb : Real → Real} {B : Finset (Point N k)} {phi : Point N k → ZMod N}
    (h : IntegerMultiplyLinearWith Qb Eb (partialGraph B phi)) (e : Fin k ≃ Fin k) :
    IntegerMultiplyLinearWith Qb Eb
      (partialGraph (B.image (LeanProofs.GowersSzemeredi.coordinateReindex e))
        (fun x => phi (LeanProofs.GowersSzemeredi.coordinateReindex e.symm x))) := by
  classical
  have hh := IntegerMultiplyLinearWith.coordinateReindex h e
  have heq : (partialGraph B phi).image
      (fun z => (LeanProofs.GowersSzemeredi.coordinateReindex e z.1, z.2)) =
      partialGraph (B.image (LeanProofs.GowersSzemeredi.coordinateReindex e))
        (fun x => phi (LeanProofs.GowersSzemeredi.coordinateReindex e.symm x)) := by
    simp [partialGraph, Finset.image_image, Function.comp_def]
  rw [heq] at hh
  exact hh

theorem IntegerMultiplyLinearWith.cylAt {N k : Nat} [NeZero N]
    {Qb Eb : Real → Real} {Λ : Finset (Point N k × ZMod N)}
    (hML : IntegerMultiplyLinearWith Qb Eb Λ)
    (M : Nat) (hfib : ∀ x : Point N k, (Λ.filter fun z => z.1 = x).card ≤ M)
    (hQ : ∀ t, 0 < t → t ≤ 1 → 0 ≤ Qb t)
    (hE : ∀ t, 0 < t → t ≤ 1 → 0 < Eb t ∧ Eb t ≤ 1) (hk : 0 < k) (j : Fin (k + 1)) :
    IntegerMultiplyLinearWith (fun t => max (Qb t) ((3 ^ (k + 1) * M : Nat) : Real))
      (fun t => Eb t / 16) (cylAt j Λ) := by
  classical
  have h := hML.relation_lift_last M hfib hQ hE hk
  have h2 := IntegerMultiplyLinearWith.coordinateReindex h (liftPerm j).symm
  refine IntegerMultiplyLinearWith.mono h2 ?_
  intro z hz
  have hzΛ := mem_cylAt.mp hz
  refine Finset.mem_image.mpr
    ⟨(LeanProofs.GowersSzemeredi.coordinateReindex (liftPerm j) z.1, z.2), ?_, ?_⟩
  · apply mem_lastLiftRelation.mpr
    rw [init_reindex_liftPerm]
    exact hzΛ
  · exact Prod.ext (reindex_liftPerm_symm j z.1) rfl

end LeanProofs.GowersSzemeredi
