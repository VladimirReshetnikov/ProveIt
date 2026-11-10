import DiophantineConsistency.LinCof.LCRank
import DiophantineConsistency.P138.P138FirstIndex

/-! # The first index for the linear cofactor: `2n = R + 1`

The linear-cofactor form of `P138FirstIndex.first_index`, for any index modulus `μ` of the `k`
slot (`LCWindow.IndexModulus`: `k = R + 1 + hμ`, `μ ∣ X Y²`). The 298/146 form has `μ = X Y²`,
the 300/144 form `μ = X Y`; the argument is the same, with the natural modulus `m = |μ|` of
`LCWindow.modulus` (`m ∣ X Y²`, `3R + 1 < m`). At a zero, with the main index `R` of `LCRank`:

* `Dt = τ²` (`LCSquares.guard_roots`) is the first norm `τ² = 1 + ℓ(ℓ+1) k²`, `ℓ = XY²`
  (`LCValue.SlotLaw.Dt_eq`). For `X > 0` it is classified at base `2(ℓ − 1) + 1`, for `X < 0`
  at base `2(λ − 2) + 1` with `λ = −ℓ`: `τ = χ(n)`, `|k| = 2ψ(n)`.
* Residues modulo `m ∣ ℓ`: for `X > 0`, `m ∣ bF + 1` and `ψ(n) ≡ n`; for `X < 0`,
  `m ∣ bF + 3` and the alternating residue `ψ(n) ≡ ±n` (`P138FirstIndex.alt_sign`). Together
  with `k ≡ R + 1 (mod m)`: `2n ≡ ±(R + 1) (mod m)`.
* No wrap: `n < R` (otherwise `|k|/2 = ψ_bF(n) ≥ ψ_b(R) = |c|`, against
  `|c| > |k|(|Y| − ½)`), and `3R + 1 < m`, so `2n = R + 1`.
* For `X > 0` the residue sign is exact, which forces `k > 0`.

Compared with `P138`, the modulus divides `X Y²` instead of `X Y`, and `|Y| ≥ 3` comes from the
positive budget (`LCRank.three_le_abs_Y`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.LCFirstIndex
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing LCValue P138Ports LCBootstrap LCSquares LCBudget LCAdjacent LCWindow
  LCEarlyFold LCRank
open ArithmeticPellRecurrence ArithmeticPellHalfIndex ArithmeticPellFirstNorm
open ZRowsCoprimeSquares (abs_eq_ι eq_or_eq_neg_abs ι_dvd_iff)
open P138Adjacent (ι_pos)
open P138EarlyFold (ι_tsub' pos_of_ι)
open P138FirstIndex (alt_sign eq_zero_of_dvd_small)
open LCNorm (Weight)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section Record
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V) (κ ω Λ ψ wt : DiffRing V)
local notation "𝓡" => regsK p x κ ω Λ ψ wt

/-- **The first index.** -/
structure FirstIndex (E : EarlyFold p x κ ω Λ ψ wt) (M : MainIndex p x κ ω Λ ψ wt E) where
  n : V
  bF : V
  hn : 2 * n = M.Rn + 1
  hk : |(𝓡).k| = ι (2 * ycoord n bF)
  hDt : (𝓡).Dt = ι (xcoord n bF) * ι (xcoord n bF)
  hbFhi : (ι bF : DiffRing V) + 2 ≤ 2 * |(𝓡).X| * |(𝓡).Y| ^ 2 + 1
  hbFlo : 2 * |(𝓡).X| * |(𝓡).Y| ^ 2 - 3 ≤ (ι bF : DiffRing V)
  hpos : 0 < (𝓡).X → (∃ ln : V, ι ln = (𝓡).X * (𝓡).Y ^ 2 ∧ bF = 2 * (ln - 1) + 1) ∧ 0 < (𝓡).k

end Record

section Regs
variable {p : Fin 6 → DiffRing V} {x : Fin 11 → DiffRing V} {κ ω Λ : DiffRing V} {e : ℕ}
variable (ψ wt : DiffRing V)
local notation "𝓡" => regsK p x κ ω Λ ψ wt

/-- `4 ≤ |X|`. -/
theorem four_le_abs_X (hp : PortFacts p) : 4 ≤ |(𝓡).X| := by
  have := abs_X_ge p x κ ω Λ ψ wt hp
  have : (4 : DiffRing V) ≤ 2 ^ 66 := by norm_num
  linarith

set_option maxHeartbeats 1000000 in
/-- The classified first norm, before the no-wrap argument. -/
theorem first_classified (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e) (hY3 : 3 ≤ |(𝓡).Y|)
    (mE kn τ : V) (hm0 : 0 < mE) (hmE : (ι mE : DiffRing V) ∣ (𝓡).X * (𝓡).Y ^ 2)
    (hkn : |(𝓡).k| = ι kn) (hDt : (𝓡).Dt = ι τ * ι τ) :
    ∃ n bF : V, xcoord n bF = τ ∧ 2 * ycoord n bF = kn ∧
      ((ι mE : DiffRing V) ∣ ι kn - ι (2 * n) ∨ (ι mE : DiffRing V) ∣ ι kn + ι (2 * n)) ∧
      (ι bF : DiffRing V) + 2 ≤ 2 * |(𝓡).X| * |(𝓡).Y| ^ 2 + 1 ∧
      2 * |(𝓡).X| * |(𝓡).Y| ^ 2 - 3 ≤ (ι bF : DiffRing V) ∧
      (0 < (𝓡).X → (∃ ln : V, ι ln = (𝓡).X * (𝓡).Y ^ 2 ∧ bF = 2 * (ln - 1) + 1) ∧
        (ι mE : DiffRing V) ∣ ι kn - ι (2 * n)) := by
  obtain ⟨xn, hxn⟩ := abs_eq_ι (𝓡).X
  obtain ⟨yn, hyn⟩ := abs_eq_ι (𝓡).Y
  have hX4 := four_le_abs_X ψ wt (κ := κ) (ω := ω) (Λ := Λ) (x := x) hp
  have habs : |(𝓡).X * (𝓡).Y ^ 2| = ι xn * (ι yn * ι yn) := by
    rw [abs_mul, abs_pow, hxn, hyn]; ring
  obtain ⟨w0, hw0⟩ : (ι mE : DiffRing V) ∣ ι xn * (ι yn * ι yn) := by
    rw [← habs]; exact (dvd_abs _ _).mpr hmE
  have hk2 : (𝓡).k ^ 2 = ι kn * ι kn := by rw [← sq_abs, hkn]; ring
  have hY2 : (𝓡).Y ^ 2 = ι yn * ι yn := by rw [← sq_abs, hyn]; ring
  have hDt' : ι τ * ι τ =
      1 + ((𝓡).X * (𝓡).Y ^ 2) * ((𝓡).X * (𝓡).Y ^ 2 + 1) * (ι kn * ι kn) := by
    rw [← hDt, h.Dt_eq ψ wt, hk2]
  have hlam2 : (2 : V) ≤ xn * yn * yn := by
    apply ι_le_ι.mp
    rw [map_mul, map_mul, map_ofNat, ← hxn, ← hyn]
    have h12 : (4 : DiffRing V) * 3 ≤ |(𝓡).X| * |(𝓡).Y| :=
      mul_le_mul hX4 hY3 (by norm_num) (abs_nonneg _)
    have h36 : (4 : DiffRing V) * 3 * 3 ≤ |(𝓡).X| * |(𝓡).Y| * |(𝓡).Y| :=
      mul_le_mul h12 hY3 (by norm_num) (by linarith)
    linarith
  rcases lt_or_gt_of_ne (X_ne p x κ ω Λ ψ wt hp) with hXneg | hXpos
  · -- `X < 0`: base `2(λ − 2) + 1`, `λ = −ℓ`
    have hX : (𝓡).X = -ι xn := by rw [← hxn, abs_of_neg hXneg]; ring
    set lam : V := xn * yn * yn with hlam
    have hl : (𝓡).X * (𝓡).Y ^ 2 = -ι lam := by rw [hX, hY2, hlam]; simp only [map_mul]; ring
    have hl2 : (ι (lam - 2) : DiffRing V) = ι lam - 2 := by rw [ι_tsub' hlam2, map_ofNat]
    have hnorm : τ * τ = 1 + discriminant (lam - 2) * kn * kn := by
      apply ι_injective
      unfold discriminant
      simp only [map_mul, map_add, map_one, map_ofNat]
      rw [hl2, hDt', hl]; ring
    obtain ⟨n, _, hx, hy⟩ := solution_index (lam - 2) τ kn hnorm
    refine ⟨n, 2 * (lam - 2) + 1, hx, hy, ?_, ?_, ?_, fun h' => absurd h' (not_lt.mpr hXneg.le)⟩
    · have hd : mE ∣ 2 * (lam - 2) + 1 + 3 := by
        refine ι_dvd_iff.mp ⟨2 * w0, ?_⟩
        simp only [map_add, map_mul, map_ofNat, map_one]
        rw [hl2, hlam]; simp only [map_mul]; linear_combination 2 * hw0
      rcases alt_sign (2 * (lam - 2) + 1) mE hm0 hd n with h' | h'
      · left
        obtain ⟨w, hw⟩ := h'
        refine ⟨2 * w, ?_⟩
        rw [← hy, map_mul, map_mul, map_ofNat]; linear_combination 2 * hw
      · right
        obtain ⟨w, hw⟩ := h'
        refine ⟨2 * w, ?_⟩
        rw [← hy, map_mul, map_mul, map_ofNat]; linear_combination 2 * hw
    · simp only [map_add, map_mul, map_ofNat, map_one]
      rw [hl2, hlam, map_mul, map_mul, ← hxn, ← hyn]; nlinarith
    · simp only [map_add, map_mul, map_ofNat, map_one]
      rw [hl2, hlam, map_mul, map_mul, ← hxn, ← hyn]; nlinarith
  · -- `X > 0`: base `2(ℓ − 1) + 1`
    have hX : (𝓡).X = ι xn := by rw [← hxn, abs_of_pos hXpos]
    set ln : V := xn * yn * yn with hln
    have hl : (𝓡).X * (𝓡).Y ^ 2 = ι ln := by rw [hX, hY2, hln]; simp only [map_mul]; ring
    have hl1 : (1 : V) ≤ ln := le_trans (by norm_num) hlam2
    have hl1' : (ι (ln - 1) : DiffRing V) = ι ln - 1 := by rw [ι_tsub' hl1, map_one]
    have hnorm : τ * τ = 1 + discriminant (ln - 1) * kn * kn := by
      apply ι_injective
      unfold discriminant
      simp only [map_mul, map_add, map_one, map_ofNat]
      rw [hl1', hDt', hl]; ring
    obtain ⟨n, _, hx, hy⟩ := solution_index (ln - 1) τ kn hnorm
    have hd : mE ∣ 2 * (ln - 1) + 1 + 1 := by
      refine ι_dvd_iff.mp ⟨2 * w0, ?_⟩
      simp only [map_add, map_mul, map_ofNat, map_one]
      rw [hl1', hln]; simp only [map_mul]; linear_combination 2 * hw0
    obtain ⟨_, s, _, hys⟩ :=
      ArithmeticPellCongruences.residue_quotients n (2 * (ln - 1) + 1) mE hd
    have hexact : (ι mE : DiffRing V) ∣ ι kn - ι (2 * n) :=
      ⟨2 * ι s, by rw [← hy, hys]; simp only [map_mul, map_add, map_ofNat]; ring⟩
    refine ⟨n, 2 * (ln - 1) + 1, hx, hy, Or.inl hexact, ?_, ?_,
      fun _ => ⟨⟨ln, hl.symm, rfl⟩, hexact⟩⟩
    · simp only [map_add, map_mul, map_ofNat, map_one]
      rw [hl1', hln, map_mul, map_mul, ← hxn, ← hyn]; nlinarith
    · simp only [map_add, map_mul, map_ofNat, map_one]
      rw [hl1', hln, map_mul, map_mul, ← hxn, ← hyn]; nlinarith

set_option maxHeartbeats 2000000 in
/-- **The first index is `(R + 1)/2`.** -/
theorem first_index (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e)
    (hκ : IndexModulus p x κ ω Λ ψ wt e) (hwt : Weight wt) (hz : valueK p x κ ω Λ ψ wt = 0)
    (E : EarlyFold p x κ ω Λ ψ wt) (M : MainIndex p x κ ω Λ ψ wt E) :
    Nonempty (FirstIndex p x κ ω Λ ψ wt E M) := by
  have hB : 0 < (𝓡).Budget := budget_pos ψ wt hp h hwt hz
  obtain ⟨mE, hmE, hkdvd0, hE3⟩ := modulus ψ wt hp h hκ hB
  obtain ⟨hk0, _⟩ := centered ψ wt hp h hB
  have hci := (c_interval ψ wt hp h hB).1
  have hY3 := three_le_abs_Y ψ wt hp h hB
  obtain ⟨τ, _, _, _, hDt, _⟩ := guard_roots ψ wt hp h hwt hz
  obtain ⟨kn, hkn⟩ := abs_eq_ι (𝓡).k
  rw [M.hR] at hE3
  have hm0 : 0 < mE := pos_of_ι (by have := ι_nonneg M.Rn; linarith)
  obtain ⟨n, bF, hx, hy, hres, hhi, hlo, hposX⟩ :=
    first_classified ψ wt hp h hY3 mE kn τ hm0 hmE hkn hDt
  have hX4 := four_le_abs_X ψ wt (κ := κ) (ω := ω) (Λ := Λ) (x := x) hp
  -- `n < R`
  have hnR : n < M.Rn := by
    by_contra hcon
    have hle : M.Rn ≤ n := le_of_not_gt hcon
    have hbb : E.Bn - 2 ≤ bF := by
      apply ι_le_ι.mp
      rw [ι_tsub' (le_trans (by norm_num) E.hB3), map_ofNat, ← E.hBn]
      have hA : |(𝓡).A| ≤ |(𝓡).Y| * (|(𝓡).X| + 1) + 2 := by
        have e' : (𝓡).A = (𝓡).Y * ((𝓡).X + 1) + 2 := by rw [A_eq, a_eq]; ring
        rw [e']
        calc |(𝓡).Y * ((𝓡).X + 1) + 2| ≤ |(𝓡).Y * ((𝓡).X + 1)| + |(2 : DiffRing V)| :=
              abs_add_le _ _
          _ ≤ |(𝓡).Y| * (|(𝓡).X| + 1) + 2 := by
              rw [abs_mul, abs_two]
              have := mul_le_mul_of_nonneg_left (abs_add_le (𝓡).X 1) (abs_nonneg (𝓡).Y)
              rw [abs_one] at this; linarith
      have h4Y : 4 * |(𝓡).Y| ≤ |(𝓡).X| * |(𝓡).Y| :=
        mul_le_mul_of_nonneg_right hX4 (abs_nonneg _)
      have h5 : |(𝓡).X| * |(𝓡).Y| * 5 ≤ |(𝓡).X| * |(𝓡).Y| * (2 * |(𝓡).Y| - 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      nlinarith
    have h1 := (ArithmeticPellFirstIndex.base_mono (E.Bn - 2) bF hbb M.Rn).2
    have h2 : ycoord M.Rn bF ≤ ycoord n bF :=
      (ArithmeticPellStrongDivisibility.y_strictMono bF).monotone hle
    have hcn : E.cn ≤ ycoord n bF := by rw [M.hc]; exact le_trans h1 h2
    have h3 : 2 * ι E.cn ≤ |(𝓡).k| := by
      rw [hkn, ← hy, map_mul, map_ofNat]
      have := ι_le_ι.mpr hcn; linarith
    rw [E.hcn] at hci
    have : |(𝓡).k| * 5 ≤ |(𝓡).k| * (2 * |(𝓡).Y| - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    have : 0 < |(𝓡).k| := abs_pos.mpr hk0
    linarith
  -- `k ≡ R + 1 (mod m)`
  have hkdvd : (ι mE : DiffRing V) ∣ (𝓡).k - (ι M.Rn + 1) := by rw [← M.hR]; exact hkdvd0
  have hkn0 : 0 < kn := pos_of_ι (by rw [← hkn]; exact abs_pos.mpr hk0)
  have hsmall : (ι (2 * n) : DiffRing V) + (ι M.Rn + 1) < ι mE := by
    have : ι n + 1 ≤ (ι M.Rn : DiffRing V) := by
      rw [← map_one ι, ← map_add]; exact ι_le_ι.mpr (lt_iff_succ_le.mp hnR)
    rw [map_mul, map_ofNat]; linarith
  have hpos2 : (0 : DiffRing V) < ι (2 * n) + (ι M.Rn + 1) := by
    have := ι_nonneg (2 * n); have := ι_nonneg M.Rn; linarith
  have hnone : ¬ (ι mE : DiffRing V) ∣ ι (2 * n) + (ι M.Rn + 1) := by
    intro h'
    have := eq_zero_of_dvd_small h' (by rw [abs_of_pos hpos2]; exact hsmall)
    linarith
  have hcomb : (ι mE : DiffRing V) ∣ ι (2 * n) - (ι M.Rn + 1) ∨
      (ι mE : DiffRing V) ∣ ι (2 * n) + (ι M.Rn + 1) := by
    obtain ⟨d, hd⟩ := hkdvd
    rcases eq_or_eq_neg_abs (𝓡).k with hks | hks <;> rw [hkn] at hks <;> rw [hks] at hd
    · rcases hres with ⟨w, hw⟩ | ⟨w, hw⟩
      · exact Or.inl ⟨d - w, by linear_combination hd - hw⟩
      · exact Or.inr ⟨w - d, by linear_combination hw - hd⟩
    · rcases hres with ⟨w, hw⟩ | ⟨w, hw⟩
      · exact Or.inr ⟨-(d + w), by linear_combination -hd - hw⟩
      · exact Or.inl ⟨d + w, by linear_combination hd + hw⟩
  have hnR' : 2 * n = M.Rn + 1 := by
    rcases hcomb with h' | h'
    · have h0 := eq_zero_of_dvd_small h' (by
        rw [abs_sub_lt_iff]; constructor <;> linarith [ι_nonneg (2 * n), ι_nonneg M.Rn])
      apply ι_injective
      rw [map_add, map_one]; linarith
    · exact absurd h' hnone
  refine ⟨⟨n, bF, hnR', by rw [hkn, hy], by rw [hDt, hx], hhi, hlo, fun hX0 => ?_⟩⟩
  obtain ⟨hln, hexact⟩ := hposX hX0
  refine ⟨hln, ?_⟩
  rcases eq_or_eq_neg_abs (𝓡).k with hks | hks
  · rw [hks]; exact abs_pos.mpr hk0
  · exfalso
    rw [hkn] at hks
    obtain ⟨d, hd⟩ := hkdvd
    obtain ⟨w, hw⟩ := hexact
    rw [hks] at hd
    exact hnone ⟨-(d + w), by linear_combination -hd - hw⟩

end Regs

#print axioms first_classified
#print axioms first_index

end DiophantineConsistency.LCFirstIndex
