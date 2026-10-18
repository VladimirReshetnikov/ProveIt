import GowersSzemeredi.Proofs13PhaseSelection
import GowersSzemeredi.Proofs13SingletonRecurrence
import GowersSzemeredi.Proofs05QuadraticFamilyScale
import GowersSzemeredi.Proofs13QuadraticPartition

/-! Quadratic recurrence in the printed large case, with improved length
and density. Finite localization avoids an asymptotic Weyl threshold.

`lemma_13_5_prime_large_improved` is in `Proofs13FiniteRecurrenceBoundsSide`,
outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem stage135AmbientQuadratic_polynomial {N : Nat} [NeZero N] (a b : ZMod N) :
    PolynomialOn 2 Finset.univ (stage135AmbientQuadratic a b) := by
  have heq : stage135AmbientQuadratic a b = stage135Quadratic (modInterval N 0 N) a b := by
    funext t
    simp [stage135AmbientQuadratic, stage135Quadratic, modInterval]
  rw [heq]
  exact stage135Quadratic_polynomial (modInterval N 0 N) a b

theorem modAP_step_ne_zero_of_proper_length {N : Nat} [NeZero N]
    (Q : ModAP N) (hQ : Q.IsProper) (hlen : 2 ≤ Q.length) : Q.step != 0 := by
  apply bne_iff_ne.mpr
  intro hz
  have hc : Q.carrier.card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro x y hx hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    simp [hz]
  rw [hQ] at hc
  omega

theorem lemma_13_5_prime_large_case {N : Nat} [NeZero N] (hprime : N.Prime)
    (S : Section13Context N) (D : Stage134Data N) (theta : Real)
    (h134 : IsStage134Data S theta D)
    (hlargeCase : 2 < (D.P.length : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * D.q))) :
    ∃ E : Stage135Data N, IsStage135Data S D E ∧
      Nat.floor ((D.P.length : Real) ^ ((1 : Real) / (2 : Real) ^ (11 * D.q))) ≤ E.Q.length ∧
      S.alpha ^ 32 * E.Q.length / 16 ≤ (criticalHeights S D E).card := by
  have hq : 1 ≤ D.q := h134.1
  have hP : D.P.IsProper := h134.2.2.1
  have hPpos : 0 < D.P.length := Nat.pos_of_ne_zero fun hz => by
    rw [hz, Nat.cast_zero, Real.zero_rpow (by positivity : (1 : Real) / 2 ^ (12 * D.q) ≠ 0)]
      at hlargeCase
    norm_num at hlargeCase
  have h12 : (2 : Real) ^ (12 * D.q) = (4096 : Real) ^ D.q := by rw [pow_mul]; norm_num
  have h11 : (2 : Real) ^ (11 * D.q) = (2048 : Real) ^ D.q := by rw [pow_mul]; norm_num
  let U := Nat.floor ((D.P.length : Real) ^ ((2048 : Real) ^ D.q)⁻¹)
  obtain ⟨hUfour, hbudgetR, hlength, hscale⟩ := quadratic_family_floor_scale
    (by exact_mod_cast hPpos : (1 : Real) ≤ D.P.length) hq
    (by simpa only [h12, one_div] using hlargeCase)
  have hbudget : quadraticFamilyBudget D.q U ≤ D.P.length := Nat.cast_le.mp hbudgetR
  -- `N ≥ |P| ≥ U ≥ 4`, so `N ≠ 2`
  have hPN : D.P.length ≤ N := by
    rw [← hP]
    simpa only [ZMod.card] using Finset.card_le_univ D.P.carrier
  have hUL : U ≤ D.P.length := (quadraticFamilyBudget_ge D.q U).trans hbudget
  have hodd : N != 2 := bne_iff_ne.mpr (by omega)
  obtain ⟨M, Q, hpart, hQ⟩ := quadratic_family_phase_localization D.P
    (fun i => stage135AmbientQuadratic (D.a i) (D.b i)) U hP
    (fun i => stage135AmbientQuadratic_polynomial (D.a i) (D.b i)) (by omega) hbudget
  obtain ⟨x, hx⟩ : D.P.carrier.Nonempty := Finset.card_pos.mp (by rw [hP]; exact hPpos)
  obtain ⟨j0, -⟩ := (hpart.1 x).mp hx
  obtain ⟨j, hj⟩ := stage135_select_weighted_cell S D Q j0.pos hP h134.2.2.2.1
    hpart (fun j => (hQ j).1) h134.2.2.2.2.2.2.2.1
  obtain ⟨hQp, hQU, hQphase⟩ := hQ j
  have hselected := stage135_of_phase_cell hprime hodd S D (Q j) hQp
    (modAP_step_ne_zero_of_proper_length _ hQp (by omega)) (hpart.cell_subset j) (by omega) U
    (by omega) (by rw [h12, one_div]; exact hlength.trans (Nat.cast_le.mpr hQU))
    (by simpa only [h11, one_div] using hscale) hj fun i => (hQphase i).imp fun _ hz => hz.2
  exact ⟨⟨Q j⟩, hselected.1, by simpa only [h11, one_div] using hQU, hselected.2⟩

end LeanProofs.GowersSzemeredi
