import DiophantineConsistency.P138.P138Adjacent
import DiophantineConsistency.P138.P138Budget
import DiophantineConsistency.ArithmeticPellClassification
import DiophantineConsistency.ArithmeticPellHalfIndex
import DiophantineConsistency.BFS943.PellRecovery
import DiophantineConsistency.BFS943.Direct80Residue
import Mathlib.Algebra.Ring.GeomSum

/-! # Early folding: the main square `Dm = d²` before the first Pell root

132-lowops §4 and signed-quadratic §2, as used by `PROOF.md` ("The early folding theorem uses
only these strong and auxiliary norms and the bound `|c| ≤ |I|`"). At a zero of the 924/107
output, in every model of `𝗜𝚺₁` (`early_fold`, packaged as the record `EarlyFold`):

* `B = |A| ≥ 3`, base `b = B − 2` (so `delta b = (b+1)(b+3) = A² − 1 = Delta`);
* the strong pair: `I0 = |U| p0` (`I = U p0`), `f² = 1 + Delta I0²`, classified as
  `f = χ_b(m)`, `I0 = ψ_b(m)` (`ArithmeticPellClassification.solution_index`);
* the auxiliary pair: `J = Delta I0 = |Delta I|`, `Q = J²`, `Q V² − (Q − 1) y² = 1`
  (`P138Adjacent.aux_integral`), classified at base `J − 2` with odd index `2h + 1`
  (`odd_index_witness`), `J |V| = χ_{J−2}(2h+1)`, `|V| = oddQuotient h (J − 2)`;
* the transfer `|V| ≡ ±ψ_b(2h+1) (mod f)` (`quotient_mod_norm`) and `V ≡ −c (mod f²)` give
  `|c| ≡ ±ψ_b(2h+1) (mod f)`;
* `|c| < I0` and `2 I0 < f`, so the odd fold (`TenPositivePellRecovery.recover_odd_ordinate`)
  gives an odd `0 < p < m` with `|c| = ψ_b(p)`; hence `Dm = 1 + Delta c² = χ_b(p)²`.

This uses neither `Dt` being a square, nor the first index, the projector or the orientation.
Consequences:

* `guard_split`: `P = (p0/d)²`; `Dt` and `Dg = 1 + D Dt s²` are coprime and positive, hence
  `Dt = τ²`, `Dg = g²`, `p0 = d τ g`;
* `Z_eq_S`: `Z = ±S p0 f y` (cancel `delta` in `delta Z = S w`, `w = ±p0 f e`, `e = delta y`), so
  `S ∣ Ac` (`S_dvd_Ac`);
* `H_dvd_Kq5`: `H ∣ Kq⁵` with `Kq = X(X + 2ac) − 1` (`zc ≡ K (mod H)`, `K = H X c − 2 Kq`,
  `H` odd). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P138EarlyFold
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares P138Value P138Ports P138Bootstrap P138NoRoot
  P138Squares P138Budget P138Adjacent
open ArithmeticPellRecurrence ArithmeticPellClassification ArithmeticPellResidueClasses
  ArithmeticPellHalfIndex ArithmeticGcdNormalization ModelBetaFunction ModelBoundedForallArith

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ι_tsub' {a b : V} (h : b ≤ a) : (ι (a - b) : DiffRing V) = ι a - ι b := by
  have e := congrArg (ι (V := V)) (tsub_add_cancel_of_le h)
  rw [map_add] at e
  linear_combination e

theorem pos_of_ι {a : V} (h : (0 : DiffRing V) < ι a) : 0 < a := by
  rw [← map_zero ι] at h; exact ι_lt_ι.mp h

/-- The signed residue: `V = f² w − c` with `|V| = vn`, `|c| = cn` gives `vn ≡ ±cn (mod f)`. -/
theorem signed_square_residue (f vn cn : V) (w Vr cR : DiffRing V) (hf : 0 < f)
    (hV : Vr = ι (f * f) * w - cR) (hvn : |Vr| = ι vn) (hcn : |cR| = ι cn) :
    SignMod f vn cn := by
  have hVV : Vr * Vr = ι (vn * vn) := by rw [map_mul, ← hvn, abs_mul_abs_self]
  rcases eq_or_eq_neg_abs cR with hc | hc
  · rw [hcn] at hc
    exact TenPositive80Residue.square_multiple_residue f cn vn w Vr hf (by rw [hV, hc]) hVV
  · rw [hcn] at hc
    exact TenPositive80Residue.square_multiple_residue f cn vn (-w) (-Vr) hf
      (by rw [hV, hc]; ring) (by rw [neg_mul_neg]; exact hVV)

/-- `F² = 1 + D I²` with `D ≥ 8` gives `2 I < F`. -/
theorem two_lt_of_norm {F I D : DiffRing V} (hD : 8 ≤ D) (hI : 0 ≤ I) (hF : 0 ≤ F)
    (h : F * F = 1 + D * I * I) : 2 * I < F := by
  by_contra hn
  have hle : F ≤ 2 * I := le_of_not_gt hn
  have h1 : F * F ≤ (2 * I) * (2 * I) := mul_le_mul hle hle hF (by linarith)
  have h2 := mul_nonneg (sub_nonneg.mpr hD) (mul_nonneg hI hI)
  have h3 := mul_nonneg hI hI
  nlinarith

section Regs
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V)
local notation "𝓡" => regs p x

/-- **The early-fold data at a zero.** -/
structure EarlyFold where
  Bn : V
  p0 : V
  f : V
  e : V
  y : V
  Un : V
  vn : V
  cn : V
  m : V
  h : V
  idx : V
  hBn : |(𝓡).A| = ι Bn
  hB3 : 3 ≤ Bn
  hDelta : (𝓡).Delta = ι (delta (Bn - 2))
  hp0 : 0 < p0
  hf : 0 < f
  he : 0 < e
  hy : 0 < y
  hBP : (𝓡).BP = ι p0 * ι p0
  hDf : (𝓡).Df = ι f * ι f
  hDa : Da p x = ι e * ι e
  hey : ι e = ((𝓡).Q - 1) * ι y
  haux : (𝓡).Q * (𝓡).V ^ 2 - ((𝓡).Q - 1) * (ι y) ^ 2 = 1
  hUn : |(𝓡).U| = ι Un
  hUn0 : 0 < Un
  hvn : |(𝓡).V| = ι vn
  hvn0 : 0 < vn
  hcn : |x 8| = ι cn
  hcn0 : 0 < cn
  hcI : cn < Un * p0
  hm : 0 < m
  hmx : xcoord m (Bn - 2) = f
  hmy : ycoord m (Bn - 2) = Un * p0
  hQJ : (𝓡).Q = ι (delta (Bn - 2) * (Un * p0)) * ι (delta (Bn - 2) * (Un * p0))
  hsx : xcoord (2 * h + 1) (delta (Bn - 2) * (Un * p0) - 2) = delta (Bn - 2) * (Un * p0) * vn
  hsy : ycoord (2 * h + 1) (delta (Bn - 2) * (Un * p0) - 2) = y
  hvsign : SignMod f vn (ycoord (2 * h + 1) (Bn - 2))
  hcsign : SignMod f cn (ycoord (2 * h + 1) (Bn - 2))
  hidx0 : 0 < idx
  hidxm : idx < m
  hidxodd : idx % 2 = 1
  hcidx : cn = ycoord idx (Bn - 2)
  hDm : (𝓡).Dm = ι (xcoord idx (Bn - 2)) * ι (xcoord idx (Bn - 2))
  hstrong : f * f = 1 + delta (Bn - 2) * (Un * p0) * (Un * p0)
  hcdvd : cn * cn ∣ Un * p0
  hres : SignMod f vn cn

set_option maxHeartbeats 2000000 in
/-- **Early folding.** At a zero, the strong, auxiliary and main roots exist as above. -/
theorem early_fold (hp : PortFacts p) (hz : value p x = 0) : Nonempty (EarlyFold p x) := by
  have hc : x 8 ≠ 0 := c_ne p x hp (by linarith [budget_ge p x hp hz])
  obtain ⟨p0, f, e, hp0, hf, he, hBP, hDf, hDa⟩ := roots p x hp hz
  obtain ⟨y, hy, hey, haux⟩ := aux_integral p x hp hz hc hDa he
  -- the base
  obtain ⟨Bn, hBn⟩ := abs_eq_ι (𝓡).A
  have hB3 : 3 ≤ Bn := by
    have h := abs_A p x hp
    rw [hBn, show (3 : DiffRing V) = ι 3 by rw [map_ofNat]] at h
    exact ι_le_ι.mp h
  have hB2 : 2 ≤ Bn := le_trans (by norm_num) hB3
  set b : V := Bn - 2 with hbdef
  have hbB : (ι b : DiffRing V) = ι Bn - 2 := by
    rw [hbdef, ι_tsub' hB2, map_ofNat]
  have hDelta : (𝓡).Delta = ι (delta b) := by
    unfold delta
    rw [Delta_eq, map_mul, map_add, map_add, map_one, map_ofNat, hbB, ← sq_abs, hBn]; ring
  -- the strong pair
  obtain ⟨Un, hUn⟩ := abs_eq_ι (𝓡).U
  have hU0 := U_ne p x hp hz hc
  have hUn0 : 0 < Un := by
    rcases eq_zero_or_pos Un with h0 | h0
    · rw [h0, map_zero] at hUn; exact absurd (abs_eq_zero.mp hUn) hU0
    · exact h0
  set I0 : V := Un * p0 with hI0
  have hU2 : (𝓡).U ^ 2 = ι Un * ι Un := by rw [← hUn, ← sq_abs]; ring
  have hstrong : f * f = 1 + delta b * I0 * I0 := by
    apply ι_injective
    simp only [map_mul, map_add, map_one]
    rw [← hDf, Df_eq, hDelta, hU2, hBP, hI0, map_mul]; ring
  obtain ⟨m, _, hmx, hmy⟩ := solution_index b f I0 hstrong
  have hstrong0 := hstrong
  have hI0pos : 0 < I0 := mul_pos hUn0 hp0
  have hm : 0 < m := by
    rcases eq_zero_or_pos m with h0 | h0
    · rw [h0, y_zero] at hmy; exact absurd hmy.symm hI0pos.ne'
    · exact h0
  have hdb : 8 ≤ delta b :=
    ι_le_ι.mp (by rw [← hDelta, map_ofNat]; exact Delta_gt p x hp)
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
    rw [Q_eq, hDelta, hU2, hBP, hJdef, hI0, map_mul, map_mul]; ring
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
  have htransfer : SignMod f vn (ycoord (2 * h + 1) b) := by
    rw [hvq]; exact quotient_mod_norm b J f h hJ2 hf hstrongnorm
  -- `V ≡ −c (mod f²)`
  obtain ⟨cn, hcn⟩ := abs_eq_ι (x 8)
  have hcn0 : 0 < cn := by
    rcases eq_zero_or_pos cn with h0 | h0
    · rw [h0, map_zero] at hcn; exact absurd (abs_eq_zero.mp hcn) hc
    · exact h0
  have hres : SignMod f vn cn :=
    signed_square_residue f vn cn (bOff p x) (𝓡).V (x 8) hf
      (by rw [V_bOff, hDf, map_mul]) hvn hcn
  have htarget : SignMod f cn (ycoord (2 * h + 1) b) := sign_trans hf (sign_symm hres) htransfer
  have hcdvd : cn * cn ∣ I0 := by
    obtain ⟨rn, hrn⟩ := abs_eq_ι (x 4)
    have hU' : (ι Un : DiffRing V) = ι (Bn * rn * (cn * cn)) := by
      rw [← hUn, U_eq, abs_mul, abs_mul, abs_pow, hBn, hrn, hcn]; simp only [map_mul]; ring
    rw [hI0, ι_injective hU']
    exact dvd_mul_of_dvd_left (dvd_mul_left (cn * cn) (Bn * rn)) p0
  -- size bounds
  have hcI : cn < I0 := by
    apply ι_lt_ι.mp
    have hUc : 3 * |x 8| ^ 2 ≤ |(𝓡).U| := by
      rw [U_eq, abs_mul, abs_mul, abs_pow]
      have hA := abs_A p x hp
      have hr := one_le_abs (s_r_ne p x hp hz).2
      have h0 : 0 ≤ |x 8| ^ 2 := by positivity
      have : 3 * 1 ≤ |(𝓡).A| * |x 4| := mul_le_mul hA hr (by norm_num) (abs_nonneg _)
      nlinarith
    have hc1 : 1 ≤ |x 8| := one_le_abs hc
    have hp01 : (1 : DiffRing V) ≤ ι p0 := by rw [← map_one ι]; exact ι_le_ι.mpr (pos_iff_one_le.mp hp0)
    rw [hI0, map_mul, ← hUn, ← hcn]
    have : |x 8| < |(𝓡).U| := by nlinarith
    calc |x 8| < |(𝓡).U| := this
      _ = |(𝓡).U| * 1 := (mul_one _).symm
      _ ≤ |(𝓡).U| * ι p0 := mul_le_mul_of_nonneg_left hp01 (abs_nonneg _)
  have hsodd : (2 * h + 1) % 2 = 1 := by
    rw [mod_add (by simp : (0:V) < 2), mod_mul_self_right]; simp
  obtain ⟨idx, hidx0, hidxm, hidxodd, hcidx⟩ :=
    TenPositivePellRecovery.recover_odd_ordinate m (2 * h + 1) b cn hm hsodd hcn0
      (by rw [hmy]; exact hcI) (by rw [hmy, hmx]; exact hsize) (by rw [hmx]; exact htarget)
  have hDm : (𝓡).Dm = ι (xcoord idx b) * ι (xcoord idx b) := by
    rw [← map_mul, ArithmeticPellRecurrence.norm, Dm_eq, hDelta, ← sq_abs, hcn, hcidx]
    simp only [map_add, map_mul, map_one]; ring
  exact ⟨⟨Bn, p0, f, e, y, Un, vn, cn, m, h, idx, hBn, hB3, hDelta, hp0, hf, he, hy, hBP, hDf,
    hDa, hey, haux, hUn, hUn0, hvn, hvn0, hcn, hcn0, hcI, hm, hmx, hmy, hQJ,
    (by rw [← hs]; exact hsx), (by rw [← hs]; exact hsy), htransfer, htarget, hidx0, hidxm,
    hidxodd, hcidx, hDm, hstrong0, hcdvd, hres⟩⟩

/-! ## Consequences -/

/-- **The guard splits.** `P = (p0/d)²`, `Dt = τ²`, `Dg = g²`, `p0 = d τ g`. -/
theorem guard_split (hp : PortFacts p) (hz : value p x = 0) (E : EarlyFold p x) :
    ∃ τ g : V, 0 < τ ∧ 0 < g ∧ (𝓡).Dt = ι τ * ι τ ∧
      1 + (𝓡).D4 * (𝓡).Dt * x 10 ^ 2 = ι g * ι g ∧
      E.p0 = xcoord E.idx (E.Bn - 2) * τ * g := by
  obtain ⟨d, hd_def⟩ : ∃ d : V, d = xcoord E.idx (E.Bn - 2) := ⟨_, rfl⟩
  have hDm' : (𝓡).Dm = ι d * ι d := by rw [hd_def]; exact E.hDm
  have hd : 0 < d := by rw [hd_def]; exact lt_of_lt_of_le (by norm_num) (one_le_x _ _)
  -- `d² ∣ p0²`
  have hdiv : d * d ∣ E.p0 * E.p0 := by
    refine ι_dvd_iff.mp ⟨(𝓡).P, ?_⟩
    rw [map_mul, map_mul, ← E.hBP, BP_eq, hDm']
  obtain ⟨t, ht⟩ := dvd_of_mul_self_dvd_mul_self hdiv
  have hdR : (ι d : DiffRing V) ≠ 0 := (ι_pos hd).ne'
  have hP : (𝓡).P = ι t * ι t := by
    have h1 : ι d * ι d * (𝓡).P = ι d * ι d * (ι t * ι t) := by
      have e1 : ι d * ι d * (𝓡).P = (𝓡).BP := by rw [BP_eq, hDm']
      rw [e1, E.hBP, ht, map_mul]; ring
    exact mul_left_cancel₀ (mul_ne_zero hdR hdR) h1
  -- `Dt` and `Dg` are coprime and positive
  have hcop : ∃ α β : DiffRing V, (𝓡).Dt * α + (1 + (𝓡).D4 * (𝓡).Dt * x 10 ^ 2) * β = 1 :=
    ⟨-((𝓡).D4 * x 10 ^ 2), 1, by ring⟩
  have hprod : (𝓡).Dt * (1 + (𝓡).D4 * (𝓡).Dt * x 10 ^ 2) = ι t * ι t := by rw [← P_eq, hP]
  obtain ⟨⟨τ, hτ⟩, ⟨g, hg⟩⟩ := abs_squares_of_mul_square hcop hprod
  have hDt : 0 < (𝓡).Dt := by linarith [(Dt_facts p x hp).1]
  have hPpos := P_pos p x hp hz
  have hDg : 0 < 1 + (𝓡).D4 * (𝓡).Dt * x 10 ^ 2 := by
    rw [P_eq] at hPpos; exact pos_of_mul_pos_right hPpos hDt.le
  rw [abs_of_pos hDt] at hτ
  rw [abs_of_pos hDg] at hg
  have hτ0 : 0 < τ := by
    rcases eq_zero_or_pos τ with h0 | h0
    · rw [h0, map_zero, mul_zero] at hτ; linarith
    · exact h0
  have hg0 : 0 < g := by
    rcases eq_zero_or_pos g with h0 | h0
    · rw [h0, map_zero, mul_zero] at hg; linarith
    · exact h0
  refine ⟨τ, g, hτ0, hg0, hτ, hg, ?_⟩
  -- `t = τ g`, both positive square roots of `P`
  have htg : (ι t : DiffRing V) * ι t = (ι τ * ι g) * (ι τ * ι g) := by
    rw [← hP, P_eq, hg, hτ]; ring
  have ht0 : (0 : DiffRing V) ≤ ι t := ι_nonneg _
  have htg0 : (0 : DiffRing V) ≤ ι τ * ι g := mul_nonneg (ι_nonneg _) (ι_nonneg _)
  have htg' : (ι t : DiffRing V) = ι τ * ι g := by
    rcases mul_self_eq_mul_self_iff.mp htg with h1 | h1
    · exact h1
    · have : ι t = (0 : DiffRing V) := by linarith
      rw [this, zero_mul] at hP; rw [hP] at hPpos; exact absurd hPpos (lt_irrefl _)
  rw [← hd_def]
  apply ι_injective
  rw [ht]; simp only [map_mul]; rw [htg']; ring

/-- **`Z = ±S p0 f y`.** -/
theorem Z_eq_S (hp : PortFacts p) (hz : value p x = 0) (E : EarlyFold p x) :
    (𝓡).Z = (𝓡).S * (ι E.p0 * ι E.f * ι E.y) ∨ (𝓡).Z = -((𝓡).S * (ι E.p0 * ι E.f * ι E.y)) := by
  obtain ⟨w, hw, hww⟩ := prod_square p x hp hz
  have hδ : (𝓡).Q - 1 ≠ 0 := (nonzero p x hp).2.2.1
  have hsq : w * w = (ι E.p0 * ι E.f * ι E.e) * (ι E.p0 * ι E.f * ι E.e) := by
    rw [hww, E.hBP, E.hDf, E.hDa]; ring
  rcases mul_self_eq_mul_self_iff.mp hsq with h1 | h1
  · left
    apply mul_left_cancel₀ hδ
    rw [hw, h1, E.hey]; ring
  · right
    apply mul_left_cancel₀ hδ
    rw [hw, h1, E.hey]; ring

/-- **`S ∣ Ac`.** -/
theorem S_dvd_Ac (hp : PortFacts p) (hz : value p x = 0) (E : EarlyFold p x) :
    (𝓡).S ∣ (𝓡).Ac := by
  have hAc : (𝓡).Ac = (𝓡).S * x 9 - (𝓡).Z := by rw [Z_eq]; ring
  rcases Z_eq_S p x hp hz E with h | h
  · exact ⟨x 9 - ι E.p0 * ι E.f * ι E.y, by rw [hAc, h]; ring⟩
  · exact ⟨x 9 + ι E.p0 * ι E.f * ι E.y, by rw [hAc, h]; ring⟩

/-- The projector register `Kq = X (X + 2 a c) − 1` (132-lowops §5). -/
def Kq : DiffRing V := (𝓡).X * ((𝓡).X + 2 * (𝓡).a * x 8) - 1

theorem K_Kq : (𝓡).K = (𝓡).H * (𝓡).X * x 8 - 2 * Kq p x := by
  unfold Kq; rw [K_eq, H_def]; ring

/-- An odd divisor of `2 Y` divides `Y`. -/
theorem odd_dvd_of_dvd_two_mul {H Y : DiffRing V} (hH : ∃ m : DiffRing V, H = 2 * m + 1)
    (h : H ∣ 2 * Y) : H ∣ Y := by
  obtain ⟨m, rfl⟩ := hH
  obtain ⟨k, hk⟩ := h
  exact ⟨Y - m * k, by linear_combination (-m) * hk⟩

/-- **`H ∣ Kq⁵`.** -/
theorem H_dvd_Kq5 (hp : PortFacts p) (hz : value p x = 0) (E : EarlyFold p x) :
    (𝓡).H ∣ Kq p x ^ 5 := by
  have hHS : (𝓡).H ∣ (𝓡).S := ⟨x 10 * x 4, by rw [S_eq]; ring⟩
  have hHAc : (𝓡).H ∣ (𝓡).Ac := dvd_trans hHS (S_dvd_Ac p x hp hz E)
  have h1 : (𝓡).H ∣ (𝓡).Ac - (𝓡).zc ^ 5 :=
    ⟨3 * (𝓡).H * (𝓡).zc ^ 3 - 19 * (𝓡).H ^ 2 * (𝓡).zc ^ 2 - 57 * (𝓡).H ^ 4, by rw [Ac_eq]; ring⟩
  have h2 : (𝓡).H ∣ (𝓡).zc ^ 5 - (𝓡).K ^ 5 :=
    dvd_trans (show (𝓡).H ∣ (𝓡).zc - (𝓡).K from ⟨x 7, by rw [zc_eq]; ring⟩)
      (sub_dvd_pow_sub_pow _ _ 5)
  have h3 : (𝓡).H ∣ (𝓡).K ^ 5 - (-2 * Kq p x) ^ 5 :=
    dvd_trans (show (𝓡).H ∣ (𝓡).K - -2 * Kq p x from ⟨(𝓡).X * x 8, by rw [K_Kq]; ring⟩)
      (sub_dvd_pow_sub_pow _ _ 5)
  have h4 : (𝓡).H ∣ -(2 * (2 * (2 * (2 * (2 * Kq p x ^ 5))))) := by
    have e : -(2 * (2 * (2 * (2 * (2 * Kq p x ^ 5))))) =
        ((𝓡).Ac - (((𝓡).Ac - (𝓡).zc ^ 5) + ((𝓡).zc ^ 5 - (𝓡).K ^ 5))) -
          ((𝓡).K ^ 5 - (-2 * Kq p x) ^ 5) := by ring
    rw [e]
    exact dvd_sub (dvd_sub hHAc (dvd_add h1 h2)) h3
  have hodd := H_odd p x
  exact odd_dvd_of_dvd_two_mul hodd (odd_dvd_of_dvd_two_mul hodd (odd_dvd_of_dvd_two_mul hodd
    (odd_dvd_of_dvd_two_mul hodd (odd_dvd_of_dvd_two_mul hodd (dvd_neg.mp h4)))))

end Regs

#print axioms signed_square_residue
#print axioms early_fold
#print axioms guard_split
#print axioms Z_eq_S
#print axioms S_dvd_Ac
#print axioms K_Kq
#print axioms H_dvd_Kq5

end DiophantineConsistency.P138EarlyFold
