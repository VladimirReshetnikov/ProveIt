import GowersSzemeredi.Proofs13UntrimmedSelection
import GowersSzemeredi.Proofs05QuarterDiameterPartition

/-! Lemma 13.5 with no endpoint-deletion budget. The entire selected cell
is retained, giving strong-height density alpha^32/16 instead of /20. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem lemma_13_5_without_endpoint_budget {N : Nat} [NeZero N]
    (hprime : N.Prime) (hodd : N != 2)
    (S : Section13Context N) (D : Stage134Data N) (theta : Real)
    (h134 : IsStage134Data S theta D)
    (hthreshold : simultaneousPolynomialThreshold 2 D.q < D.P.length)
    (hscale : 4 ≤ (D.P.length : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * D.q))) :
    ∃ E : Stage135Data N, IsStage135Data S D E ∧
      S.alpha ^ 32 * E.Q.length / 16 ≤ (criticalHeights S D E).card := by
  classical
  let X := (D.P.length : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * D.q))
  let v := Nat.floor X
  have hq : 1 ≤ D.q := h134.1
  have hP : D.P.IsProper := h134.2.2.1
  have hPpos : 0 < D.P.length := by omega
  have hPone : (1 : Real) ≤ D.P.length := by exact_mod_cast hPpos
  have hX : 4 ≤ X := hscale
  have hv : 1 ≤ v := Nat.le_floor (by norm_num only [Nat.cast_one]; linarith only [hX])
  have hvfloor : (v : Real) ≤ X := Nat.floor_le (by linarith only [hX])
  have hround : X < (v : Real) + 1 := Nat.lt_floor_add_one X
  have hK : (polynomialPartitionConstant 2 : Real) = (2 : Real) ^ (11 : Nat) := by
    norm_num [polynomialPartitionConstant]
  have hden : 2 * (polynomialPartitionConstant 2 : Real) ^ D.q ≤
      (2 : Real) ^ (12 * D.q) := by
    rw [hK, ← pow_mul, ← pow_succ']
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hvupper : (v : Real) ≤ (D.P.length : Real) ^
      (2 * (polynomialPartitionConstant 2 : Real) ^ D.q)⁻¹ := by
    apply hvfloor.trans
    apply Real.rpow_le_rpow_of_exponent_le hPone
    simpa only [one_div] using
      one_div_le_one_div_of_le (by rw [hK]; positivity) hden
  have hPN : D.P.length ≤ N := by
    rw [← hP]
    simpa only [ZMod.card] using Finset.card_le_univ D.P.carrier
  obtain ⟨M, R, hM, hpart, hR, hdiam⟩ := lemma_5_9_quarter_diameter N 2 D.q D.P.length v
    (fun i => stage135Quadratic D.P (D.a i) (D.b i)) (by norm_num) hq
    (fun i => stage135Quadratic_polynomial D.P (D.a i) (D.b i)) hthreshold hPN hv hvupper
  let Q := fun j => section5Transport D.P (R j)
  have hQpart : IsPartition (fun j => (Q j).carrier) D.P.carrier :=
    section5Transport_partition D.P R hP hpart
  have hQproper (j : Fin M) : (Q j).IsProper :=
    section5Transport_isProper D.P (R j) hP (hR j).1 (hpart.cell_subset j)
  have hQlower (j : Fin M) : X - 2 ≤ ((Q j).length : Real) := by
    change X - 2 ≤ ((R j).length : Real)
    rcases (hR j).2.2 with hj | hj
    · rw [hj, Nat.cast_sub hv, Nat.cast_one]
      linarith only [hround]
    · rw [hj]
      linarith only [hround]
  have hvfour : 4 ≤ v := Nat.le_floor (by exact_mod_cast hX)
  have hQthree (j : Fin M) : 3 ≤ (Q j).length := by
    change 3 ≤ (R j).length
    rcases (hR j).2.2 with hj | hj <;> omega
  have hQstep (j : Fin M) : (Q j).step != 0 :=
    stage135Transport_step_ne_zero D.P (R j) hP (hR j).1 (by change 2 ≤ (Q j).length; have := hQthree j; omega) (hpart.cell_subset j)
  have hQdiam (i : Fin D.q) (j : Fin M) : diameterAtMostReal
      ((Q j).carrier.image (stage135AmbientQuadratic (D.a i) (D.b i)))
      (((D.P.length : Real) ^ (-((1 : Real) / (2 : Real) ^ (11 * D.q))) * N) / 4) := by
    have hi := hdiam i j
    rw [hK, ← pow_mul] at hi
    change diameterAtMostReal
      ((section5Transport D.P (R j)).carrier.image (stage135AmbientQuadratic (D.a i) (D.b i))) _
    rw [section5Transport_carrier, Finset.image_image]
    convert hi using 1
    · simp only [stage135Quadratic, stage135AmbientQuadratic, section5IndexPoint,
        Function.comp_def]
    · simp only [one_div]
      ring
  have hlength (j : Fin M) : X / 2 ≤ ((Q j).length : Real) := by
    have hl := hQlower j
    linarith only [hX, hl]
  obtain ⟨j, hj⟩ := stage135_select_untrimmed_partition hprime hodd S D Q hM hP
    h134.2.2.2.1 hQpart hQproper hQstep hQthree hlength h134.2.2.2.2.2.2.2.1 hQdiam
  exact ⟨⟨Q j⟩, hj⟩

end LeanProofs.GowersSzemeredi
