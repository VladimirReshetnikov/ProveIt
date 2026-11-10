import DiophantineConsistency.P138.P138Rank

/-! # The strong-pair fold and rank, register-free

The early fold and the main index of the eleven-integer circuits (`P138EarlyFold.early_fold`,
`P138Rank.main_index`, and their linear-coefficient copies) read the registers of one particular
circuit. The mathematics uses only a handful of relations among them. This module states those
relations as hypotheses over plain variables of a model of `𝗜𝚺₁` and its difference ring, so
that a circuit with a different back end (package 131's two-root 810/112, whose strong ordinate
has no factor `A` and whose guard has no factor `Dm`) calls one theorem instead of copying two
proofs.

* `delta_of_abs`: for `|A| = B ≥ 3`, `A² − 1 = delta (B − 2)` and `8 ≤ delta (B − 2)`.
* `adjacent_descent`: from `Q > 1` and `(Q − 1)(Q V² − 1) = e²`, `e > 0`, the adjacent Pell
  equation `Q V² − (Q − 1) y² = 1` with `e = (Q − 1) y`
  (`TenPositiveAdjacentInteger.quotient_of_scaled_norm`).
* `strong_fold`: the data are a base `b` with `8 ≤ delta b`; a strong pair
  `f² = 1 + delta b · I0²`; `Q = (delta b · I0)²`; the linear slot `V = f² · bOff − c`; the
  adjacent equation `Q V² − (Q − 1) y² = 1`; `|c| = cn > 0`, `cn² ∣ I0`, `cn < I0`; and a rank
  `0 < 2 Rn < cn` with `bOff ≡ ±Rn (mod cn)`. Conclusion: `Rn` is odd, `cn = ψ_b(Rn)` and
  `1 + delta b · c² = χ_b(Rn)²`.

The proof of `strong_fold` is the one of the two P138 modules: classify the strong pair
(`solution_index`), classify the adjacent pair at base `delta b · I0 − 2` with an odd index
(`odd_index_witness`), transfer `|V|` modulo `f` (`quotient_mod_norm`) and read `V ≡ −c
(mod f²)`, fold to an odd index below the strong index
(`TenPositivePellRecovery.recover_odd_ordinate`), then identify that index with the rank
(`TenPositiveSignedRankIndex.signed_rank_index`,
`TenPositivePellRankReduction.rank_to_main_index`, `sign_eq_of_half`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ZRowsStrongFold
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares P138Bootstrap P138Adjacent P138EarlyFold P138Rank
open ArithmeticPellRecurrence ArithmeticPellClassification ArithmeticPellResidueClasses
  ArithmeticPellHalfIndex

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- For `|A| = B ≥ 3`: `A² − 1 = delta (B − 2)`, and this discriminant is at least `8`. -/
theorem delta_of_abs {A : DiffRing V} {Bn : V} (hBn : |A| = ι Bn) (hB3 : 3 ≤ Bn) :
    A ^ 2 - 1 = ι (delta (Bn - 2)) ∧ 8 ≤ delta (Bn - 2) := by
  have hB2 : 2 ≤ Bn := le_trans (by norm_num) hB3
  have hbB : (ι (Bn - 2) : DiffRing V) = ι Bn - 2 := by rw [ι_tsub' hB2, map_ofNat]
  have hD : A ^ 2 - 1 = ι (delta (Bn - 2)) := by
    unfold delta
    rw [map_mul, map_add, map_add, map_one, map_ofNat, hbB, ← sq_abs, hBn]; ring
  refine ⟨hD, ?_⟩
  apply ι_le_ι.mp
  rw [← hD, map_ofNat]
  have h3 : (3 : DiffRing V) ≤ |A| := by
    rw [hBn, show (3 : DiffRing V) = ι 3 by rw [map_ofNat]]; exact ι_le_ι.mpr hB3
  have hsq : A ^ 2 = |A| ^ 2 := (sq_abs A).symm
  nlinarith

/-- **The adjacent descent.** From `Q > 1` and `(Q − 1)(Q V² − 1) = e²` with `e > 0`:
`e = (Q − 1) y` and `Q V² − (Q − 1) y² = 1`. -/
theorem adjacent_descent {Q Vr : DiffRing V} {e : V} (hQ : 1 < Q) (he0 : 0 < e)
    (he : (Q - 1) * (Q * Vr ^ 2 - 1) = ι e * ι e) :
    ∃ y : V, 0 < y ∧ (ι e : DiffRing V) = (Q - 1) * ι y ∧
      Q * Vr ^ 2 - (Q - 1) * (ι y) ^ 2 = 1 := by
  obtain ⟨dn, hdn⟩ := nonneg_iff.mp (show (0 : DiffRing V) ≤ Q - 1 by linarith)
  have hdn0 : 0 < dn := by
    rcases eq_zero_or_pos dn with h0 | h0
    · rw [h0, map_zero] at hdn; linarith
    · exact h0
  have hCy : 0 < Q * Vr ^ 2 - 1 := by
    have hDa : 0 < (Q - 1) * (Q * Vr ^ 2 - 1) := by
      rw [he]; exact mul_pos (ι_pos he0) (ι_pos he0)
    exact pos_of_mul_pos_right hDa (by linarith)
  have hV : Vr ≠ 0 := by
    intro h0; rw [h0] at hCy; linarith [show Q * (0 : DiffRing V) ^ 2 - 1 = -1 by ring]
  obtain ⟨vn, hvn⟩ := abs_eq_ι Vr
  have hvn0 : 0 < vn := by
    rcases eq_zero_or_pos vn with h0 | h0
    · rw [h0, map_zero] at hvn; exact absurd (abs_eq_zero.mp hvn) hV
    · exact h0
  have hVV : |Vr| * |Vr| = Vr ^ 2 := by rw [abs_mul_abs_self]; ring
  have hscaled : (1 + dn) * ((dn * vn) * (dn * vn)) = dn * dn + dn * (e * e) := by
    apply ι_injective
    simp only [map_add, map_mul, map_one]
    rw [← hdn, ← hvn, ← he]
    linear_combination (Q * (Q - 1) ^ 2) * hVV
  obtain ⟨y, hy, hnorm⟩ :=
    TenPositiveAdjacentInteger.quotient_of_scaled_norm dn dn vn e hdn0 hdn0 hvn0 hscaled
  have hy0 : 0 < y := by
    rcases eq_zero_or_pos y with h0 | h0
    · rw [h0, mul_zero] at hy; exact absurd hy he0.ne'
    · exact h0
  refine ⟨y, hy0, by rw [hy, map_mul, hdn], ?_⟩
  have h := congrArg (ι (V := V)) hnorm
  simp only [map_add, map_mul, map_one] at h
  rw [← hdn, ← hvn, hVV] at h
  linear_combination h

set_option maxHeartbeats 2000000 in
/-- **The strong-pair fold and the rank.** See the module header for the reading of the
hypotheses. The conclusion is the main Pell pair at the rank: `Rn` is odd, `|c| = ψ_b(Rn)` and
`1 + delta b · c² = χ_b(Rn)²`. -/
theorem strong_fold (b I0 f cn y Rn : V) (c Q Vr bOff : DiffRing V)
    (hdb : 8 ≤ delta b) (hf : 0 < f) (hI0pos : 0 < I0)
    (hstrong : f * f = 1 + delta b * I0 * I0)
    (hQJ : Q = ι (delta b * I0) * ι (delta b * I0))
    (hV : Vr = ι (f * f) * bOff - c)
    (haux : Q * Vr ^ 2 - (Q - 1) * (ι y) ^ 2 = 1)
    (hcn : |c| = ι cn) (hcn0 : 0 < cn) (hcdvd : cn * cn ∣ I0) (hcI : cn < I0)
    (hRpos : 0 < Rn) (h2R : 2 * Rn < cn)
    (hrank : (ι cn : DiffRing V) ∣ bOff - ι Rn ∨ (ι cn : DiffRing V) ∣ bOff + ι Rn) :
    Rn % 2 = 1 ∧ cn = ycoord Rn b ∧
      1 + ι (delta b) * c ^ 2 = ι (xcoord Rn b) * ι (xcoord Rn b) := by
  -- the strong pair
  obtain ⟨m, _, hmx, hmy⟩ := solution_index b f I0 hstrong
  have hm : 0 < m := by
    rcases eq_zero_or_pos m with h0 | h0
    · rw [h0, y_zero] at hmy; exact absurd hmy.symm hI0pos.ne'
    · exact h0
  have hsize : 2 * I0 < f := by
    apply ι_lt_ι.mp
    have hst := congrArg (ι (V := V)) hstrong
    simp only [map_mul, map_add, map_one] at hst
    have hd8 : (8 : DiffRing V) ≤ ι (delta b) := by
      rw [show (8 : DiffRing V) = ι 8 by rw [map_ofNat]]; exact ι_le_ι.mpr hdb
    rw [map_mul, map_ofNat]
    exact two_lt_of_norm hd8 (ι_nonneg _) (ι_nonneg _) hst
  -- the adjacent pair at base `J − 2`, `J = delta b · I0`
  set J : V := delta b * I0 with hJdef
  have hJ2 : 2 ≤ J := by
    have h1 : 1 ≤ I0 := pos_iff_one_le.mp hI0pos
    calc (2:V) ≤ 8 := by norm_num
      _ ≤ delta b := hdb
      _ = delta b * 1 := (mul_one _).symm
      _ ≤ delta b * I0 := mul_le_mul_of_nonneg_left h1 (by simp)
  have hJpos : 0 < J := lt_of_lt_of_le (by norm_num) hJ2
  have hJsub : J - 2 + 2 = J := tsub_add_cancel_of_le hJ2
  obtain ⟨vn, hvn⟩ := abs_eq_ι Vr
  have hV2 : Vr ^ 2 = ι vn * ι vn := by rw [← hvn, ← sq_abs]; ring
  have hdJ : (ι (delta (J - 2)) : DiffRing V) = Q - 1 := by
    unfold delta
    rw [map_mul, map_add, map_add, map_one, map_ofNat, ι_tsub' hJ2, map_ofNat, hQJ]; ring
  have hauxV : (J * vn) * (J * vn) = 1 + delta (J - 2) * y * y := by
    apply ι_injective
    simp only [map_mul, map_add, map_one]
    rw [hdJ]
    linear_combination haux - (ι vn * ι vn) * hQJ - Q * hV2
  obtain ⟨s, _, hsx, hsy⟩ := solution_index (J - 2) (J * vn) y hauxV
  obtain ⟨h, hs⟩ := odd_index_witness (J - 2) s (by rw [hJsub, hsx]; exact ⟨vn, rfl⟩)
  have hvn0 : 0 < vn := by
    rcases eq_zero_or_pos vn with h0 | h0
    · exfalso
      rw [h0, mul_zero, mul_zero] at hauxV
      have : (1 : V) ≤ 1 + delta (J - 2) * y * y := le_add_of_nonneg_right (by simp)
      have h1 : (0 : V) < 1 := by norm_num
      rw [← hauxV] at this
      exact absurd this (not_le.mpr h1)
    · exact h0
  have hvq : vn = oddQuotient h (J - 2) := by
    apply mul_left_cancel₀ (ne_of_gt hJpos)
    calc J * vn = xcoord (2 * h + 1) (J - 2) := by rw [← hs, hsx]
      _ = J * oddQuotient h (J - 2) := by rw [odd_exact, hJsub]
  have hstrongnorm : J * J + delta b = delta b * f * f := by
    rw [hJdef]
    calc delta b * I0 * (delta b * I0) + delta b = delta b * (1 + delta b * I0 * I0) := by ring
      _ = delta b * (f * f) := by rw [hstrong]
      _ = delta b * f * f := by ring
  -- the transfer modulo `f` and the odd fold
  have htransfer : SignMod f vn (ycoord (2 * h + 1) b) := by
    rw [hvq]; exact quotient_mod_norm b J f h hJ2 hf hstrongnorm
  have hres : SignMod f vn cn := signed_square_residue f vn cn bOff Vr c hf hV hvn hcn
  have htarget : SignMod f cn (ycoord (2 * h + 1) b) := sign_trans hf (sign_symm hres) htransfer
  have hsodd : (2 * h + 1) % 2 = 1 := by
    rw [mod_add (by simp : (0:V) < 2), mod_mul_self_right]; simp
  obtain ⟨idx, hidx0, _, hidxodd, hcidx⟩ :=
    TenPositivePellRecovery.recover_odd_ordinate m (2 * h + 1) b cn hm hsodd hcn0
      (by rw [hmy]; exact hcI) (by rw [hmy, hmx]; exact hsize) (by rw [hmx]; exact htarget)
  have hc2 : c ^ 2 = ι cn * ι cn := by rw [← hcn, ← sq_abs]; ring
  have hDm : 1 + ι (delta b) * c ^ 2 = ι (xcoord idx b) * ι (xcoord idx b) := by
    have hn := congrArg (ι (V := V)) (ArithmeticPellRecurrence.norm idx b)
    simp only [map_add, map_mul, map_one] at hn
    rw [hn, ← hcidx]
    linear_combination ι (delta b) * hc2
  -- the rank
  have hidx3 : 3 ≤ idx :=
    three_le_of_odd hidx0 hidxodd b hcidx
      (le_trans (le_trans (by norm_num) (mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hRpos)
        (by simp : (0 : V) ≤ 2))) h2R.le)
  have hVV : Vr * Vr = ι (vn * vn) := by rw [map_mul, ← hvn, abs_mul_abs_self]
  have hfix : ∀ (xr rank : DiffRing V),
      xr = ι (f * f) * (ι (0 * cn) - rank) - ι cn → xr * xr = ι (vn * vn) →
      (ι cn : DiffRing V) ∣ rank - ι Rn ∨ (ι cn : DiffRing V) ∣ rank + ι Rn →
      SignMod cn Rn idx := by
    intro xr rank hx hxx hdiv
    obtain ⟨rp, rn, hrk, hmod⟩ :=
      TenPositiveSignedRankIndex.signed_rank_index cn f (delta b) I0 0 vn h xr rank hcn0
        hJ2 (dvd_trans (dvd_mul_right cn cn) hcdvd) hstrong hx hxx (by rw [← hs]; exact hsx)
    have hres' : SignMod cn (absdiff rp rn) Rn := by
      refine sign_of_rank hcn0 (r := rank) (by rw [ι_absdiff, hrk]) hdiv
    have hmain := TenPositivePellRankReduction.rank_to_main_index m (2 * h + 1) b
      cn idx (absdiff rp rn) hm hidx3 hcidx (by rw [hmy]; exact hcdvd)
      (by rw [hmx]; exact htarget) hmod
    exact sign_trans hcn0 (sign_symm hres') hmain
  have hsign : SignMod cn Rn idx := by
    rcases eq_or_eq_neg_abs c with h8 | h8 <;> rw [hcn] at h8
    · refine hfix Vr (-bOff) ?_ hVV ?_
      · rw [hV, zero_mul, map_zero]; rw [h8]; ring
      · rcases hrank with hr | hr
        · right
          have := dvd_neg.mpr hr
          rwa [show -(bOff - ι Rn) = -bOff + ι Rn by ring] at this
        · left
          have := dvd_neg.mpr hr
          rwa [show -(bOff + ι Rn) = -bOff - ι Rn by ring] at this
    · refine hfix (-Vr) bOff ?_ (by rw [neg_mul_neg]; exact hVV) hrank
      rw [hV, zero_mul, map_zero]; rw [h8]; ring
  have h2i : 2 * idx < cn := by rw [hcidx]; exact twice_index_lt_y _ _ hidx3
  have heq : Rn = idx := sign_eq_of_half hRpos hidx0 h2R h2i hsign
  exact ⟨by rw [heq]; exact hidxodd, by rw [heq]; exact hcidx, by rw [heq]; exact hDm⟩

#print axioms delta_of_abs
#print axioms adjacent_descent
#print axioms strong_fold

end DiophantineConsistency.ZRowsStrongFold
