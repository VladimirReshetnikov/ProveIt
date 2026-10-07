import GowersSzemeredi.Proofs13AllScalesCoefficientSpan
import GowersSzemeredi.Proofs07ShortParentBudget

/-! Preserve the original column-length target during short-parent
localization and bilinear square extraction. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- At every scale, bilinear extraction retains the actual positive integer
step ratio in the parent progression and its span bound. -/
theorem extract_bilinear_cell_short_parent_with_step_span {N : Nat} [Fact N.Prime]
    (T : ModAP N) (S J : Finset (ZMod N)) (C : Finset (Pair N))
    (y : ZMod N) (phi : Pair N → ZMod N) (a c : ZMod N → ZMod N) (delta : Real)
    (hT : T.IsProper) (hstep : T.step != 0) (hlen : 4 ≤ T.length)
    (L : Nat) (hparent : L ≤ 3 * T.length)
    (hS : S.Nonempty) (hδ : 0 < delta) (hδone : delta ≤ 1)
    (hJ : J ⊆ T.carrier)
    (hsupport : ∀ z ∈ C, z.1 ∈ S ∧ z.2 - y ∈ J)
    (hmass : delta * S.card * T.length ≤ C.card)
    (hrow : ∀ z ∈ C, phi z = a (z.2 - y) + c (z.2 - y) * z.1)
    (ha : FreimanHom 8 J a) (hc : FreimanHom 8 J c) :
    ∃ U : ModAP N, ∃ t : Nat, U.step != 0 ∧ U.IsProper ∧ U.carrier ⊆ T.carrier ∧
      (L : Real) ^ cor711Exponent delta 1 ≤ U.length ∧
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
  obtain ⟨M, P, hP, hcell, t, ht, hspan⟩ := corollary_7_11_short_parent_with_step_span
    N T J delta L hT hstep hlen hδ hδone hparent hJ hJdense
  have hTcard : T.carrier.card = T.length := hT
  have hTne : T.carrier.Nonempty := Finset.card_pos.mp (by rw [hTcard]; omega)
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

/-- Localizing the coefficient domain to a same-step parent no longer than
the column progression makes the integer square-fit bound automatic. -/
theorem bilinear_square_from_short_parent_full_length {N : Nat} [Fact N.Prime]
    (S T : ModAP N) (J : Finset (ZMod N)) (C : Finset (Pair N))
    (y : ZMod N) (phi : Pair N → ZMod N) (a c : ZMod N → ZMod N) (delta : Real)
    (hS : S.IsProper) (hSstep : S.step != 0) (hSpos : 2 ≤ S.length)
    (hT : T.IsProper) (hTpos : 4 ≤ T.length) (hparent : S.length ≤ 3 * T.length)
    (hstep : T.step = S.step) (hshort : T.length ≤ S.length)
    (hδ : 0 < delta) (hδone : delta ≤ 1) (hJ : J ⊆ T.carrier)
    (hsupport : ∀ z ∈ C, z.1 ∈ S.carrier ∧ z.2 - y ∈ J)
    (hmass : delta * S.length * T.length ≤ C.card)
    (hrow : ∀ z ∈ C, phi z = a (z.2 - y) + c (z.2 - y) * z.1)
    (ha : FreimanHom 8 J a) (hc : FreimanHom 8 J c) :
    ∃ V W : ModAP N, ∃ E : Finset (Pair N),
      V.step != 0 ∧ V.step = W.step ∧ V.IsProper ∧ W.IsProper ∧ V.length = W.length ∧
      (S.length : Real) ^ (cor711Exponent delta 1 / 2) - 1 ≤ V.length ∧
      E ⊆ C ∧ E ⊆ V.carrier.product W.carrier ∧
      delta / 4 * V.length * W.length ≤ E.card ∧ BilinearOn E phi := by
  classical
  have hScard : S.carrier.card = S.length := hS
  obtain ⟨U, t, hUs, hU, hUsub, hUl, hmassU, hbilinear, ht, hstepU, hspan⟩ :=
    extract_bilinear_cell_short_parent_with_step_span T S.carrier J C y phi a c delta
      hT (by simpa only [hstep] using hSstep) hTpos S.length hparent
      (Finset.card_pos.mp (by rw [hScard]; omega)) hδ hδone hJ hsupport
      (by simpa only [hScard] using hmass) hrow ha hc
  have he := cor711_single_exponent_bounds hδ hδone
  have hUtwo : 2 ≤ U.length := by
    have hpow : 1 < (S.length : Real) ^ cor711Exponent delta 1 :=
      Real.one_lt_rpow (by exact_mod_cast (show 1 < S.length by omega)) he.1
    have hlen : (1 : Real) < U.length := hpow.trans_le hUl
    have : 1 < U.length := by exact_mod_cast hlen
    omega
  have hsqrt : Nat.sqrt U.length ≤ U.length - 1 := by
    have h := Nat.sqrt_lt_self (by omega : 1 < U.length)
    omega
  have hfit : t * Nat.sqrt U.length ≤ S.length :=
    ((Nat.mul_le_mul_left t hsqrt).trans hspan.le).trans hshort
  let D := C.filter fun z ↦ z.2 - y ∈ U.carrier
  have hDsupport : D ⊆ S.carrier.product (U.translateBy y).carrier := by
    intro z hz
    obtain ⟨hzC, hzU⟩ := Finset.mem_filter.mp hz
    apply Finset.mem_product.mpr
    refine ⟨(hsupport z hzC).1, ?_⟩
    rw [U.translateBy_carrier, translateFinset]
    exact Finset.mem_image.mpr ⟨z.2 - y, hzU, by abel⟩
  obtain ⟨V, W, E, hVs, hWs, hV, hW, hVl, hWl, hED, hbox, hmE, hbil⟩ :=
    bilinear_square_of_integer_step_fit S (U.translateBy y) D phi delta t (Nat.sqrt U.length)
      hS (U.translateBy_isProper y hU) hUs (by simpa only [hstep, ModAP.translateBy] using hstepU) ht
      (Nat.sqrt_pos.mpr (by omega)) hfit (Nat.sqrt_le_self _) hδ.le hDsupport
      (by simpa only [hScard, ModAP.translateBy, D] using hmassU) hbilinear
  refine ⟨V, W, E, ?_, hVs.trans hWs.symm, hV, hW, hVl.trans hWl.symm,
    ?_, hED.trans (Finset.filter_subset _ _), hbox, ?_, hbil⟩
  · rw [hVs]
    exact hUs
  · rw [hVl]
    have hpow : (S.length : Real) ^ (cor711Exponent delta 1 / 2) ≤ Real.sqrt U.length := by
      rw [Real.sqrt_eq_rpow, div_eq_mul_inv, Real.rpow_mul (Nat.cast_nonneg S.length)]
      simpa only [one_div] using Real.rpow_le_rpow
        (Real.rpow_nonneg (Nat.cast_nonneg S.length) _) hUl (by norm_num : (0 : Real) ≤ 1 / 2)
    have hs := Real.real_sqrt_le_nat_sqrt_succ (a := U.length)
    linarith only [hpow, hs]
  · simpa only [hVl, hWl] using hmE


end LeanProofs.GowersSzemeredi
