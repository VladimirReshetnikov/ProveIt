import GowersSzemeredi.Proofs13CoefficientPartition
import GowersSzemeredi.Proofs07TinyCells

/-! Weighted bilinear extraction for small real length targets. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The analytic and averaging step of Lemma 13.9 on a given height
progression. Both coefficient maps retain the one-domain exponent. -/
theorem extract_bilinear_cell_small_target {N : Nat} [Fact N.Prime]
    (T : ModAP N) (S J : Finset (ZMod N)) (C : Finset (Pair N))
    (y : ZMod N) (phi : Pair N → ZMod N) (a c : ZMod N → ZMod N) (delta target : Real) (htarget : target ≤ 2) (htargetT : target ≤ T.length)
    (hT : T.IsProper) (hstep : T.step != 0) (hlen : 0 < T.length)
    (hS : S.Nonempty)
    (hJ : J ⊆ T.carrier)
    (hsupport : ∀ z ∈ C, z.1 ∈ S ∧ z.2 - y ∈ J)
    (hmass : delta * S.card * T.length ≤ C.card)
    (hrow : ∀ z ∈ C, phi z = a (z.2 - y) + c (z.2 - y) * z.1)
    (ha : FreimanHom 8 J a) (hc : FreimanHom 8 J c) :
    ∃ U : ModAP N, U.step != 0 ∧ U.IsProper ∧ U.carrier ⊆ T.carrier ∧
      target ≤ U.length ∧ U.length ≤ 3 ∧
      delta * S.card * U.length ≤ (C.filter fun z ↦ z.2 - y ∈ U.carrier).card ∧
      BilinearOn (C.filter fun z ↦ z.2 - y ∈ U.carrier) phi := by
  classical
  obtain ⟨M, P, hP, hcell⟩ := universal_partition_at_most_three
    T J target hT hstep htarget htargetT
  have hTcard : T.carrier.card = T.length := hT
  have hTne : T.carrier.Nonempty := Finset.card_pos.mp (by simpa only [hTcard] using hlen)
  obtain ⟨j, hj⟩ := exists_coordinate_filter_cell C T.carrier (fun z ↦ z.2 - y)
    (fun j ↦ (P j).carrier) hTne hP (fun z hz ↦ hJ (hsupport z hz).2)
    (b := delta * S.card) (by simpa only [hTcard] using hmass)
  obtain ⟨hs, hp, hl, hupper, hlin⟩ := hcell j
  have hPcard : (P j).carrier.card = (P j).length := hp
  refine ⟨P j, hs, hp, hP.cell_subset j, hl, hupper, ?_, ?_⟩
  · simpa only [hPcard] using hj
  · apply bilinearOn_of_affine_row_coefficients _
      ((P j).carrier.filter fun x ↦ x ∈ J) y phi a c ?_ ?_ (hlin a ha) (hlin c hc)
    · intro z hz
      obtain ⟨hzC, hzP⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hzP, (hsupport z hzC).2⟩
    · intro z hz
      exact hrow z (Finset.mem_filter.mp hz).1

end LeanProofs.GowersSzemeredi
