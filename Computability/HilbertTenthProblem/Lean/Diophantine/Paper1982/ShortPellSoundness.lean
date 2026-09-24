import Diophantine.Paper1982.ShortPellDefs

/-!
# Soundness of the polynomial Pell subsystem in Jones 1982, §5

The raw polynomial equations first determine the larger Pell index.
Only then are the ratio estimates used to determine the smaller index
and recover `Q = B^L`. Neither power relation is assumed in the proof.
The printed alternate equation `G = A + F²(F²−A)` is used throughout.
-/

namespace Jones1982

open Pell Diophantine

set_option maxHeartbeats 1000000 in
/-- The §5 Pell equations imply the central-binomial divisibility condition
and both power relations, under the initial size chain of Lemma 2.26. -/
theorem ShortPellWitnesses.sound {R N b B L Q : ℕ}
    (hN : 8 ≤ N) (hb : 0 < b) (hbN : b ≤ N)
    (hchain : 3 < 3 * L ∧ 3 * L ≤ B ∧ B ≤ Q ∧ Q ≤ N ∧ N ≤ R)
    (hW : ShortPellWitnesses R N b B L Q) :
    N ^ 2 ∣ (2 * R).choose R ∧ (∃ v, b = 2 ^ v) ∧ Q = B ^ L := by
  obtain ⟨hL, h3L, hBQ, hQN, hNR⟩ := hchain
  have hR : 8 ≤ R := hN.trans hNR
  have hbR : b ≤ R := hbN.trans hNR
  -- Positivity and (D24) give the first Pell-base bound directly.
  have hA : 1 < hW.A := by
    calc 1 < hW.U + 1 := by have := hW.U_pos; omega
      _ ≤ hW.M * (hW.U + 1) := Nat.le_mul_of_pos_left _ hW.M_pos
      _ = hW.A := hW.D24.symm
  have hA2 : 1 ≤ hW.A ^ 2 := Nat.one_le_pow _ _ hA.le
  have hP2 : 1 ≤ hW.P ^ 2 := Nat.one_le_pow _ _ hW.P_pos
  have hG2 : 1 ≤ hW.G ^ 2 := Nat.one_le_pow _ _ hW.G_pos
  have hD : hW.D ^ 2 = (hW.A ^ 2 - 1) * hW.C ^ 2 + 1 := by
    zify [hA2]
    exact hW.D32
  have hF : hW.F ^ 2 = (hW.A ^ 2 - 1) * hW.E ^ 2 + 1 := by
    zify [hA2]
    exact hW.D34
  have hFA : hW.A ≤ hW.F ^ 2 := by
    have hE2 : 1 ≤ hW.E ^ 2 := Nat.one_le_pow _ _ hW.E_pos
    have hmul := Nat.le_mul_of_pos_right (hW.A ^ 2 - 1) hE2
    have hsq : hW.A ≤ hW.A ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have hG : hW.G = hW.A + hW.F ^ 2 * (hW.F ^ 2 - hW.A) := by
    zify [hFA]
    exact hW.D35
  have hI : hW.I ^ 2 = (hW.G ^ 2 - 1) * hW.H ^ 2 + 1 := by
    zify [hG2]
    exact hW.D37
  have hIF : hW.I ≡ hW.D [MOD hW.F] := by
    rw [hW.D31]
    show (hW.D + hW.o * hW.F) % hW.F = hW.D % hW.F
    simp
  have hBC : 2 * R + 1 ≤ hW.C := by rw [hW.D25]; omega
  have hodd : Odd (2 * R + 1) := ⟨R, by ring⟩
  have hCψ : hW.C = ψ hA (2 * R + 1) :=
    psi_of_PConds hA (by omega) hBC (Or.inr hodd) hW.i_pos
      ⟨hIF, hD, hW.D33, hF, Or.inr hG, hW.D36, hI⟩
  -- The larger index supplies (B14), completing the ratio core.
  have hPellK : IsSquare ((hW.P ^ 2 - 1) * hW.K ^ 2 + 1) := by
    rw [← Int.isSquare_natCast_iff]
    push_cast [Nat.cast_sub hP2]
    exact hW.D20
  have hK : hW.K = R + 1 + hW.h * (hW.P - 1) := by
    zify [hW.P_pos]
    exact hW.D22
  have hcore : B25core R N b hW.h hW.s hW.w (hW.C₁ + hW.φ)
      hW.A (2 * R + 1) hW.C hW.K hW.M hW.P hW.U hW.V hW.W hW.Y := by
    refine ⟨hW.D19, hPellK, hW.D21, hK, hW.D23, hW.D24, rfl, ?_,
      hW.D26, hW.D27, hW.D28, hW.D29, ?_⟩
    · simpa only [add_assoc] using hW.D25
    · intro _
      exact hCψ
  have hVA : hW.V ≤ hW.A := by rw [hW.D29]; omega
  have hDcong : hW.D ≡ hW.W + hW.C * (hW.A - hW.V)
      [MOD 2 * hW.A * hW.V - hW.V * hW.V - 1] := by
    rw [Nat.modEq_iff_dvd, J_cast hW.V_pos hVA]
    push_cast [Nat.cast_sub hVA]
    refine ⟨-(hW.γ : ℤ), ?_⟩
    linear_combination -hW.D30
  obtain ⟨hdvd, hpow⟩ := (lemma_2_25' hR hN hbR hb hbN).2
    ⟨hW.h, hW.s, hW.w, hW.C₁ + hW.φ, hW.A, 2 * R + 1, hW.C, hW.D,
      hW.K, hW.M, hW.P, hW.U, hW.V, hW.W, hW.Y,
      hW.h_pos, hW.s_pos, hW.w_pos, by have := hW.φ_pos; omega,
      hcore, hDcong, hD⟩
  -- The power-size estimates come from the core, before assuming `Q = B^L`.
  obtain ⟨_, _, _, hBA, hlarge, hQsmall⟩ :=
    hcore.power_sizes hR hN hbN hW.s_pos hW.w_pos hL h3L hBQ hQN hNR
  have hC26 : C26Conds' hW.A B L Q hW.C₁ hW.D₁ hW.Δ := by
    apply (C26Conds'.integer_iff hA (by omega) hBA.le).2
    refine ⟨?_, hW.D4.symm, hW.D5⟩
    refine ⟨-(hW.α : ℤ), ?_⟩
    linear_combination -hW.D3
  have hC₁C : hW.C₁ ≤ hW.C := by rw [hW.D25]; omega
  have hC₁ψ : hW.C₁ = ψ hA L :=
    hcore.small_psi hR hN hbN hW.s_pos hW.w_pos hL h3L hBQ hQN hNR
      hW.C₁_pos hC₁C (by rw [← hC26.C2]; exact ⟨hW.D₁, by ring⟩) hC26.C3 hA
  obtain ⟨n, hD₁n, hC₁n⟩ := Jones1978.eq_pell_of_sq hA hC26.C2
  have hn : n = L := (strictMono_y hA).injective (by rw [← hC₁n, hC₁ψ])
  have hsmallCong := hC26.C1
  rw [hD₁n, hn, hC₁ψ] at hsmallCong
  exact ⟨hdvd, hpow, pow_of_χ_congruence (by omega) (by omega) hlarge hQsmall hA hsmallCong⟩

end Jones1982
