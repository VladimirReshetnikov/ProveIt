import DiophantineConsistency.LinCof.LCCarrier

/-! # Early folding for the linear cofactor: `Dm = d²` before the first Pell root

The linear-cofactor form of `P138EarlyFold.early_fold`. At a zero of
`LCValue.valueK p x κ ω Λ ψ wt` (square even weight), in every model of `𝗜𝚺₁`
(`early_fold`, packaged as the record `EarlyFold`):

* `Bn = |A| ≥ 3`, base `b = Bn − 2` (so `delta b = A² − 1 = Delta`);
* the strong pair: with `B = u²` (`LCSquares.roots`) and `cn = |c|`, the ordinate is
  `I0 = cn² u` and `f² = Df = 1 + Delta c⁴ B = 1 + Delta I0²`, classified as `f = χ_b(m)`,
  `I0 = ψ_b(m)`. In `P138` the ordinate was `|U| p0`; here `P` is outside the strong chain;
* the auxiliary pair: `J = Delta I0`, `Q = J²`, `Q V² − (Q − 1) y² = 1`
  (`LCAdjacent.aux_integral`), classified at base `J − 2` with odd index `2h + 1`,
  `|V| = oddQuotient h (J − 2)`;
* the transfer `|V| ≡ ±ψ_b(2h+1) (mod f)` and `V ≡ −c (mod f²)` (`LCSquares.V_bOff`) give
  `|c| ≡ ±ψ_b(2h+1) (mod f)`;
* `|c| < I0` (as `u ≥ 2`, from `B = r A Dm ≥ 3`) and `2 I0 < f`, so the odd fold
  (`TenPositivePellRecovery.recover_odd_ordinate`) gives an odd `0 < idx < m` with
  `|c| = ψ_b(idx)`; hence `Dm = 1 + Delta c² = χ_b(idx)²`.

The guard roots `Dt = τ²`, `Dg = g²` are already in `LCSquares.guard_roots`, and the carrier
facts in `LCCarrier`; neither uses this fold. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.LCEarlyFold
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing LCValue P138Ports LCBootstrap LCNoRoot LCSquares LCBudget LCAdjacent
open ArithmeticPellRecurrence ArithmeticPellClassification ArithmeticPellResidueClasses
  ArithmeticPellHalfIndex ArithmeticGcdNormalization ModelBetaFunction ModelBoundedForallArith
open ZRowsCoprimeSquares (abs_eq_ι eq_or_eq_neg_abs)
open P138Bootstrap (one_le_of_pos' one_le_abs)
open P138Adjacent (ι_pos)
open P138EarlyFold (ι_tsub' pos_of_ι signed_square_residue two_lt_of_norm)
open LCNorm (Weight)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section Record
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V) (κ ω Λ ψ wt : DiffRing V)
local notation "𝓡" => regsK p x κ ω Λ ψ wt

/-- **The early-fold data at a zero.** -/
structure EarlyFold where
  Bn : V
  u : V
  I0 : V
  f : V
  e : V
  y : V
  vn : V
  cn : V
  m : V
  h : V
  idx : V
  hBn : |(𝓡).A| = ι Bn
  hB3 : 3 ≤ Bn
  hDelta : (𝓡).Delta = ι (delta (Bn - 2))
  hu : 0 < u
  hu2 : 2 ≤ u
  hf : 0 < f
  he : 0 < e
  hy : 0 < y
  hB : (𝓡).B = ι u * ι u
  hDf : (𝓡).Df = ι f * ι f
  hDa : Da p x κ ω Λ ψ wt = ι e * ι e
  hey : ι e = ((𝓡).Q - 1) * ι y
  haux : (𝓡).Q * (𝓡).V ^ 2 - ((𝓡).Q - 1) * (ι y) ^ 2 = 1
  hvn : |(𝓡).V| = ι vn
  hvn0 : 0 < vn
  hcn : |x 8| = ι cn
  hcn0 : 0 < cn
  hI0 : I0 = cn * cn * u
  hI0pos : 0 < I0
  hcI : cn < I0
  hm : 0 < m
  hmx : xcoord m (Bn - 2) = f
  hmy : ycoord m (Bn - 2) = I0
  hQJ : (𝓡).Q = ι (delta (Bn - 2) * I0) * ι (delta (Bn - 2) * I0)
  hsx : xcoord (2 * h + 1) (delta (Bn - 2) * I0 - 2) = delta (Bn - 2) * I0 * vn
  hsy : ycoord (2 * h + 1) (delta (Bn - 2) * I0 - 2) = y
  hvsign : SignMod f vn (ycoord (2 * h + 1) (Bn - 2))
  hcsign : SignMod f cn (ycoord (2 * h + 1) (Bn - 2))
  hidx0 : 0 < idx
  hidxm : idx < m
  hidxodd : idx % 2 = 1
  hcidx : cn = ycoord idx (Bn - 2)
  hDm : (𝓡).Dm = ι (xcoord idx (Bn - 2)) * ι (xcoord idx (Bn - 2))
  hstrong : f * f = 1 + delta (Bn - 2) * I0 * I0
  hcdvd : cn * cn ∣ I0
  hres : SignMod f vn cn

end Record

section Regs
variable {p : Fin 6 → DiffRing V} {x : Fin 11 → DiffRing V} {κ ω Λ : DiffRing V} {e : ℕ}
variable (ψ wt : DiffRing V)
local notation "𝓡" => regsK p x κ ω Λ ψ wt

/-- At a zero, `B ≥ 3`. -/
theorem B_ge3 (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e)
    (hwt : Weight wt) (hz : valueK p x κ ω Λ ψ wt = 0) : 3 ≤ (𝓡).B := by
  have hBud := budget_pos ψ wt hp h hwt hz
  have hA := A_ge ψ wt hp h hBud
  have hr := one_le_abs (s_r_ne p x κ ω Λ ψ wt hp hz).2
  have hDm1 : 1 ≤ |(𝓡).Dm| := le_trans (Dm_ge p x κ ω Λ ψ wt hp) (le_abs_self _)
  have h1 : 1 * 3 ≤ |x 4| * |(𝓡).A| := mul_le_mul hr hA (by norm_num) (abs_nonneg _)
  have h2 : 1 * 3 * 1 ≤ |x 4| * |(𝓡).A| * |(𝓡).Dm| :=
    mul_le_mul h1 hDm1 (by norm_num) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hB : |(𝓡).B| = |x 4| * |(𝓡).A| * |(𝓡).Dm| := by rw [B_eq, abs_mul, abs_mul]
  rw [← abs_of_pos (B_pos ψ wt hp h hwt hz), hB]
  linarith

set_option maxHeartbeats 2000000 in
/-- **Early folding.** At a zero, the strong, auxiliary and main roots exist as above. -/
theorem early_fold (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e)
    (hwt : Weight wt) (hz : valueK p x κ ω Λ ψ wt = 0) :
    Nonempty (EarlyFold p x κ ω Λ ψ wt) := by
  have hBud := budget_pos ψ wt hp h hwt hz
  have hc : x 8 ≠ 0 := c_ne ψ wt hp h hBud
  obtain ⟨u, f, e', hu, hf, he, hB, hDf, hDa⟩ := roots ψ wt hp h hwt hz
  obtain ⟨y, hy, hey, haux⟩ := aux_integral ψ wt hp h hwt hz hDa he
  -- `u ≥ 2`
  have huR : (2 : DiffRing V) ≤ ι u := by
    by_contra hn
    have h1 : (ι u : DiffRing V) ≤ 1 := by
      have := one_le_of_pos' (sub_pos.mpr (lt_of_not_ge hn)); linarith
    have h0 : (0 : DiffRing V) ≤ ι u := ι_nonneg _
    have h3 := B_ge3 ψ wt hp h hwt hz
    rw [hB] at h3
    nlinarith
  have hu2 : 2 ≤ u := ι_le_ι.mp (by rw [map_ofNat]; exact huR)
  -- the base
  obtain ⟨Bn, hBn⟩ := abs_eq_ι (𝓡).A
  have hB3 : 3 ≤ Bn := by
    have h' := A_ge ψ wt hp h hBud
    rw [hBn, show (3 : DiffRing V) = ι 3 by rw [map_ofNat]] at h'
    exact ι_le_ι.mp h'
  have hB2 : 2 ≤ Bn := le_trans (by norm_num) hB3
  set b : V := Bn - 2 with hbdef
  have hbB : (ι b : DiffRing V) = ι Bn - 2 := by
    rw [hbdef, ι_tsub' hB2, map_ofNat]
  have hDelta : (𝓡).Delta = ι (delta b) := by
    unfold delta
    rw [Delta_eq, map_mul, map_add, map_add, map_one, map_ofNat, hbB, ← sq_abs, hBn]; ring
  -- the strong pair
  obtain ⟨cn, hcn⟩ := abs_eq_ι (x 8)
  have hcn0 : 0 < cn := by
    rcases eq_zero_or_pos cn with h0 | h0
    · rw [h0, map_zero] at hcn; exact absurd (abs_eq_zero.mp hcn) hc
    · exact h0
  have hc2 : x 8 ^ 2 = ι cn * ι cn := by rw [← hcn, ← sq_abs]; ring
  have hc4 : x 8 ^ 4 = ι cn * ι cn * (ι cn * ι cn) := by rw [← hc2]; ring
  obtain ⟨I0, hI0⟩ : ∃ I0 : V, I0 = cn * cn * u := ⟨_, rfl⟩
  have hI0R : (ι I0 : DiffRing V) = ι cn * ι cn * ι u := by rw [hI0]; simp only [map_mul]
  have hstrong : f * f = 1 + delta b * I0 * I0 := by
    apply ι_injective
    simp only [map_mul, map_add, map_one]
    rw [← hDf, Df_eq, hDelta, hB, hc4, hI0R]; ring
  obtain ⟨m, _, hmx, hmy⟩ := solution_index b f I0 hstrong
  have hI0pos : 0 < I0 := by rw [hI0]; exact mul_pos (mul_pos hcn0 hcn0) hu
  have hm : 0 < m := by
    rcases eq_zero_or_pos m with h0 | h0
    · rw [h0, y_zero] at hmy; exact absurd hmy.symm hI0pos.ne'
    · exact h0
  have hdb : 8 ≤ delta b :=
    ι_le_ι.mp (by rw [← hDelta, map_ofNat]; exact Delta_ge8 ψ wt hp h hBud)
  have hsize : 2 * I0 < f := by
    apply ι_lt_ι.mp
    have hst := congrArg (ι (V := V)) hstrong
    simp only [map_mul, map_add, map_one] at hst
    have hd8 : (8 : DiffRing V) ≤ ι (delta b) := by
      rw [show (8 : DiffRing V) = ι 8 by rw [map_ofNat]]; exact ι_le_ι.mpr hdb
    rw [map_mul, map_ofNat]
    exact two_lt_of_norm hd8 (ι_nonneg _) (ι_nonneg _) hst
  -- the auxiliary pair
  set J : V := delta b * I0 with hJdef
  have hJ2 : 2 ≤ J := by
    have h1 : 1 ≤ I0 := pos_iff_one_le.mp hI0pos
    calc (2:V) ≤ 8 := by norm_num
      _ ≤ delta b := hdb
      _ = delta b * 1 := (mul_one _).symm
      _ ≤ delta b * I0 := mul_le_mul_of_nonneg_left h1 (by simp)
  have hJpos : 0 < J := lt_of_lt_of_le (by norm_num) hJ2
  have hJsub : J - 2 + 2 = J := tsub_add_cancel_of_le hJ2
  have hQJ : (𝓡).Q = ι J * ι J := by
    rw [Q_eq, hDelta, hB, hc4, hJdef, map_mul, hI0R]; ring
  obtain ⟨vn, hvn⟩ := abs_eq_ι (𝓡).V
  have hV2 : (𝓡).V ^ 2 = ι vn * ι vn := by rw [← hvn, ← sq_abs]; ring
  have hdJ : (ι (delta (J - 2)) : DiffRing V) = (𝓡).Q - 1 := by
    unfold delta
    rw [map_mul, map_add, map_add, map_one, map_ofNat, ι_tsub' hJ2, map_ofNat, hQJ]; ring
  have hauxV : (J * vn) * (J * vn) = 1 + delta (J - 2) * y * y := by
    apply ι_injective
    simp only [map_mul, map_add, map_one]
    rw [hdJ]
    linear_combination haux - (ι vn * ι vn) * hQJ - (𝓡).Q * hV2
  obtain ⟨s, _, hsx, hsy⟩ := solution_index (J - 2) (J * vn) y hauxV
  obtain ⟨h', hs⟩ := odd_index_witness (J - 2) s (by rw [hJsub, hsx]; exact ⟨vn, rfl⟩)
  have hvn0 : 0 < vn := by
    rcases eq_zero_or_pos vn with h0 | h0
    · exfalso
      rw [h0, mul_zero, mul_zero] at hauxV
      have : (1 : V) ≤ 1 + delta (J - 2) * y * y := le_add_of_nonneg_right (by simp)
      have h1 : (0 : V) < 1 := by norm_num
      rw [← hauxV] at this
      exact absurd this (not_le.mpr h1)
    · exact h0
  have hvq : vn = oddQuotient h' (J - 2) := by
    apply mul_left_cancel₀ (ne_of_gt hJpos)
    calc J * vn = xcoord (2 * h' + 1) (J - 2) := by rw [← hs, hsx]
      _ = J * oddQuotient h' (J - 2) := by rw [odd_exact, hJsub]
  have hstrongnorm : J * J + delta b = delta b * f * f := by
    rw [hJdef]
    calc delta b * I0 * (delta b * I0) + delta b = delta b * (1 + delta b * I0 * I0) := by ring
      _ = delta b * (f * f) := by rw [hstrong]
      _ = delta b * f * f := by ring
  have htransfer : SignMod f vn (ycoord (2 * h' + 1) b) := by
    rw [hvq]; exact quotient_mod_norm b J f h' hJ2 hf hstrongnorm
  -- `V ≡ −c (mod f²)`
  have hres : SignMod f vn cn :=
    signed_square_residue f vn cn (bOff p x κ ω Λ ψ wt) (𝓡).V (x 8) hf
      (by rw [V_bOff, hDf, map_mul]) hvn hcn
  have htarget : SignMod f cn (ycoord (2 * h' + 1) b) :=
    sign_trans hf (sign_symm hres) htransfer
  have hcdvd : cn * cn ∣ I0 := ⟨u, hI0⟩
  -- size bounds
  have hcI : cn < I0 := by
    apply ι_lt_ι.mp
    rw [hI0R]
    have hc1 : (1 : DiffRing V) ≤ ι cn := by
      rw [← map_one ι]; exact ι_le_ι.mpr (pos_iff_one_le.mp hcn0)
    have h1 : (2 : DiffRing V) ≤ ι cn * ι u := by nlinarith
    have h2 : (ι cn : DiffRing V) * 2 ≤ ι cn * (ι cn * ι u) :=
      mul_le_mul_of_nonneg_left h1 (ι_nonneg _)
    have e1 : (ι cn : DiffRing V) * ι cn * ι u = ι cn * (ι cn * ι u) := by ring
    rw [e1]; linarith
  have hsodd : (2 * h' + 1) % 2 = 1 := by
    rw [mod_add (by simp : (0:V) < 2), mod_mul_self_right]; simp
  obtain ⟨idx, hidx0, hidxm, hidxodd, hcidx⟩ :=
    TenPositivePellRecovery.recover_odd_ordinate m (2 * h' + 1) b cn hm hsodd hcn0
      (by rw [hmy]; exact hcI) (by rw [hmy, hmx]; exact hsize) (by rw [hmx]; exact htarget)
  have hDm : (𝓡).Dm = ι (xcoord idx b) * ι (xcoord idx b) := by
    rw [← map_mul, ArithmeticPellRecurrence.norm, Dm_eq, hDelta, ← sq_abs, hcn, hcidx]
    simp only [map_add, map_mul, map_one]; ring
  exact ⟨⟨Bn, u, I0, f, e', y, vn, cn, m, h', idx, hBn, hB3, hDelta, hu, hu2, hf, he, hy, hB,
    hDf, hDa, hey, haux, hvn, hvn0, hcn, hcn0, hI0, hI0pos, hcI, hm, hmx, hmy, hQJ,
    (by rw [← hs]; exact hsx), (by rw [← hs]; exact hsy), htransfer, htarget, hidx0, hidxm,
    hidxodd, hcidx, hDm, hstrong, hcdvd, hres⟩⟩

end Regs

#print axioms B_ge3
#print axioms early_fold

end DiophantineConsistency.LCEarlyFold
