import GowersSzemeredi.Proofs13IndexedCoefficientPartition
import GowersSzemeredi.Proofs07AllScalesStepSpan

/-! Bilinear coefficient extraction preserving integer geometry at all scales. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- At every scale, bilinear extraction retains the actual positive integer
step ratio in the parent progression and its span bound. -/
theorem extract_bilinear_cell_all_scales_with_step_span {N : Nat} [Fact N.Prime]
    (T : ModAP N) (S J : Finset (ZMod N)) (C : Finset (Pair N))
    (y : ZMod N) (phi : Pair N → ZMod N) (a c : ZMod N → ZMod N) (delta : Real)
    (hT : T.IsProper) (hstep : T.step != 0) (hlen : 0 < T.length)
    (hS : S.Nonempty) (hδ : 0 < delta) (hδone : delta ≤ 1)
    (hJ : J ⊆ T.carrier)
    (hsupport : ∀ z ∈ C, z.1 ∈ S ∧ z.2 - y ∈ J)
    (hmass : delta * S.card * T.length ≤ C.card)
    (hrow : ∀ z ∈ C, phi z = a (z.2 - y) + c (z.2 - y) * z.1)
    (ha : FreimanHom 8 J a) (hc : FreimanHom 8 J c) :
    ∃ U : ModAP N, ∃ t : Nat, U.step != 0 ∧ U.IsProper ∧ U.carrier ⊆ T.carrier ∧
      (T.length : Real) ^ cor711Exponent delta 1 ≤ U.length ∧
      delta * S.card * U.length ≤ (C.filter fun z ↦ z.2 - y ∈ U.carrier).card ∧
      BilinearOn (C.filter fun z ↦ z.2 - y ∈ U.carrier) phi ∧
      0 < t ∧ U.step = (t : ZMod N) * T.step ∧ t * (U.length - 1) < T.length := by
  classical
  have hcard := translated_row_card_le C S J y hsupport
  have hcardReal : (C.card : Real) ≤ (S.card : Real) * J.card := by exact_mod_cast hcard
  have hSpos : (0 : Real) < S.card := by exact_mod_cast hS.card_pos
  have hJdense : delta * T.length ≤ J.card := by
    apply le_of_mul_le_mul_left (a := (S.card : Real)) _ hSpos
    nlinarith only [hmass, hcardReal]
  obtain ⟨M, P, hP, hcell, t, ht, hspan⟩ := corollary_7_11_all_scales_universal_with_step_span
    N T J delta hT hstep hlen hδ hδone hJ hJdense
  have hTcard : T.carrier.card = T.length := hT
  have hTne : T.carrier.Nonempty := Finset.card_pos.mp (by simpa only [hTcard] using hlen)
  obtain ⟨j, hj⟩ := exists_coordinate_filter_cell C T.carrier (fun z ↦ z.2 - y)
    (fun j ↦ (P j).carrier) hTne hP (fun z hz ↦ hJ (hsupport z hz).2)
    (b := delta * S.card) (by simpa only [hTcard] using hmass)
  obtain ⟨hs, hp, hl, hlinear⟩ := hcell j
  have hPcard : (P j).carrier.card = (P j).length := hp
  refine ⟨P j, t, hs, hp, hP.cell_subset j, hl, ?_, ?_, ht, (hspan j).1, (hspan j).2⟩
  · simpa only [hPcard] using hj
  · apply bilinearOn_of_affine_row_coefficients _
      ((P j).carrier.filter fun x ↦ x ∈ J) y phi a c ?_ ?_ (hlinear a ha) (hlinear c hc)
    · intro z hz
      obtain ⟨hzC, hzP⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hzP, (hsupport z hzC).2⟩
    · intro z hz
      exact hrow z (Finset.mem_filter.mp hz).1

end LeanProofs.GowersSzemeredi
