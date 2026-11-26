import IPRADerivations.Core.Gcd

/-!
# Arithmetic of pentagonal tilings

Packet: `geometry/pentagonal_tiling_ipra_2026-11-16` (the arithmetic lemmas marked `Lh` in its
theorem ledger: P1, P10, D3, S1, H1). Angles are in degrees, or in tenths of a full turn for the
regular pentagon (`3/10` of a turn per corner, `5/10` for a straight angle).

* `absurd_of`: `a + (c + 1) = a` is absurd (a reusable way to close a numeric case);
* `local_obstruction` (P1): for `k ≥ 1`, `3k + 5l ≠ 10`: around a point that carries at least
  one corner of a regular pentagon, `k` corners and `l` straight angles never make a full turn.
  The cases `l = 0` and `l = 1` are the full-vertex and the T-junction obstruction;
* `hyperbolic_order` (H1): `10 < 3n ↔ 4 ≤ n`, the condition for the hyperbolic tiling `{5, n}`;
* `type15_angle_sum` (P10): `150 + 60 + 135 + 105 + 90 = 540`;
* `dual_angle_sums` (D3): the three dual uniform pentagons have angle sum `540`;
* `dodecahedron_euler` (S1): `V + F = E + 2` for `V = 20`, `E = 30`, `F = 12`.

The geometric content of the packet (the periodic cells and their certificates) is not
formalized.
-/

namespace LeanProofs.IPRA.Geometry.PentagonArithmetic

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `a + (c + 1) = a` is absurd. -/
theorem absurd_of {a c : PTm n} (h : Γ ⊢[PRAAx] a + succ c ≐ a) : Γ ⊢[PRAAx] Fm.bot :=
  succ_ne_zero (a := c)
    ((add_monus' (succ c) a).eqSymm.eqTrans ((congrMonus h (.eqRefl a)).eqTrans (le_refl a)))

/-! ## The local obstruction for regular pentagons -/

section Obstruction

variable {k K K₁ K₂ K₃ l l₁ l₂ : PTm n}

theorem leaf_l2 (hk : Γ ⊢[PRAAx] k ≐ succ K) (hl : Γ ⊢[PRAAx] l ≐ succ (succ l₂))
    (h : Γ ⊢[PRAAx] num 3 * k + num 5 * l ≐ num 10) : Γ ⊢[PRAAx] Fm.bot := by
  refine absurd_of (a := num 10) (c := num 2 + num 3 * K + num 5 * l₂) ?_
  ipra_lc natEq h - 3 * natEq hk - 5 * natEq hl

theorem leaf_3 (hk : Γ ⊢[PRAAx] k ≐ succ K) (hK : Γ ⊢[PRAAx] K ≐ zero) (hl : Γ ⊢[PRAAx] l ≐ zero)
    (h : Γ ⊢[PRAAx] num 3 * k + num 5 * l ≐ num 10) : Γ ⊢[PRAAx] Fm.bot := by
  refine absurd_of (a := num 3) (c := num 6) ?_
  ipra_lc -natEq h + 3 * natEq hk + 3 * natEq hK + 5 * natEq hl

theorem leaf_6 (hk : Γ ⊢[PRAAx] k ≐ succ K) (hK : Γ ⊢[PRAAx] K ≐ succ K₁) (hK₁ : Γ ⊢[PRAAx] K₁ ≐ zero)
    (hl : Γ ⊢[PRAAx] l ≐ zero) (h : Γ ⊢[PRAAx] num 3 * k + num 5 * l ≐ num 10) : Γ ⊢[PRAAx] Fm.bot := by
  refine absurd_of (a := num 6) (c := num 3) ?_
  ipra_lc -natEq h + 3 * natEq hk + 3 * natEq hK + 3 * natEq hK₁ + 5 * natEq hl

theorem leaf_9 (hk : Γ ⊢[PRAAx] k ≐ succ K) (hK : Γ ⊢[PRAAx] K ≐ succ K₁) (hK₁ : Γ ⊢[PRAAx] K₁ ≐ succ K₂)
    (hK₂ : Γ ⊢[PRAAx] K₂ ≐ zero) (hl : Γ ⊢[PRAAx] l ≐ zero)
    (h : Γ ⊢[PRAAx] num 3 * k + num 5 * l ≐ num 10) : Γ ⊢[PRAAx] Fm.bot := by
  refine absurd_of (a := num 9) (c := zero) ?_
  ipra_lc -natEq h + 3 * natEq hk + 3 * natEq hK + 3 * natEq hK₁ + 3 * natEq hK₂ + 5 * natEq hl

theorem leaf_12 (hk : Γ ⊢[PRAAx] k ≐ succ K) (hK : Γ ⊢[PRAAx] K ≐ succ K₁) (hK₁ : Γ ⊢[PRAAx] K₁ ≐ succ K₂)
    (hK₂ : Γ ⊢[PRAAx] K₂ ≐ succ K₃) (hl : Γ ⊢[PRAAx] l ≐ zero)
    (h : Γ ⊢[PRAAx] num 3 * k + num 5 * l ≐ num 10) : Γ ⊢[PRAAx] Fm.bot := by
  refine absurd_of (a := num 10) (c := num 1 + num 3 * K₃) ?_
  ipra_lc natEq h - 3 * natEq hk - 3 * natEq hK - 3 * natEq hK₁ - 3 * natEq hK₂ - 5 * natEq hl

theorem leaf_8 (hk : Γ ⊢[PRAAx] k ≐ succ K) (hK : Γ ⊢[PRAAx] K ≐ zero) (hl : Γ ⊢[PRAAx] l ≐ succ l₁)
    (hl₁ : Γ ⊢[PRAAx] l₁ ≐ zero) (h : Γ ⊢[PRAAx] num 3 * k + num 5 * l ≐ num 10) : Γ ⊢[PRAAx] Fm.bot := by
  refine absurd_of (a := num 8) (c := num 1) ?_
  ipra_lc -natEq h + 3 * natEq hk + 3 * natEq hK + 5 * natEq hl + 5 * natEq hl₁

theorem leaf_11 (hk : Γ ⊢[PRAAx] k ≐ succ K) (hK : Γ ⊢[PRAAx] K ≐ succ K₁) (hl : Γ ⊢[PRAAx] l ≐ succ l₁)
    (hl₁ : Γ ⊢[PRAAx] l₁ ≐ zero) (h : Γ ⊢[PRAAx] num 3 * k + num 5 * l ≐ num 10) : Γ ⊢[PRAAx] Fm.bot := by
  refine absurd_of (a := num 10) (c := num 3 * K₁) ?_
  ipra_lc natEq h - 3 * natEq hk - 3 * natEq hK - 5 * natEq hl - 5 * natEq hl₁

/-- No straight angle: `3k = 10` with `k ≥ 1` is impossible. -/
theorem obs_l0 (hk : Γ ⊢[PRAAx] k ≐ succ K) (hl : Γ ⊢[PRAAx] l ≐ zero)
    (h : Γ ⊢[PRAAx] num 3 * k + num 5 * l ≐ num 10) : Γ ⊢[PRAAx] Fm.bot := by
  refine .orE (zero_or_succ K) (leaf_3 hk.wk Prf.hyp0 hl.wk h.wk) ?_
  refine .orE (zero_or_succ (pred K)) (leaf_6 hk.wk.wk Prf.hyp1 Prf.hyp0 hl.wk.wk h.wk.wk) ?_
  refine .orE (zero_or_succ (pred (pred K)))
    (leaf_9 hk.wk.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0 hl.wk.wk.wk h.wk.wk.wk)
    (leaf_12 hk.wk.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0 hl.wk.wk.wk h.wk.wk.wk)

/-- One straight angle: `3k + 5 = 10` with `k ≥ 1` is impossible. -/
theorem obs_l1 (hk : Γ ⊢[PRAAx] k ≐ succ K) (hl : Γ ⊢[PRAAx] l ≐ succ l₁) (hl₁ : Γ ⊢[PRAAx] l₁ ≐ zero)
    (h : Γ ⊢[PRAAx] num 3 * k + num 5 * l ≐ num 10) : Γ ⊢[PRAAx] Fm.bot :=
  .orE (zero_or_succ K) (leaf_8 hk.wk Prf.hyp0 hl.wk hl₁.wk h.wk) (leaf_11 hk.wk Prf.hyp0 hl.wk hl₁.wk h.wk)

end Obstruction

/-- P1: for `k ≥ 1`, `3k + 5l ≠ 10`. -/
theorem local_obstruction {k l : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) :
    Γ ⊢[PRAAx] neg (num 3 * k + num 5 * l ≐ num 10) := by
  refine .impI (.orE (zero_or_succ l) (obs_l0 hk.wk.wk Prf.hyp0 Prf.hyp1) ?_)
  refine .orE (zero_or_succ (pred l)) (obs_l1 hk.wk.wk.wk Prf.hyp1 Prf.hyp0 Prf.hyp1.wk) ?_
  exact leaf_l2 hk.wk.wk.wk (Prf.hyp1.eqTrans (congrSucc Prf.hyp0)) Prf.hyp1.wk

/-! ## The hyperbolic order criterion -/

/-- `4 ≤ m` gives `10 < 3m`. -/
theorem hyperbolic_of_le {m : PTm n} (h : Γ ⊢[PRAAx] le (num 4) m) : Γ ⊢[PRAAx] lt (num 10) (num 3 * m) := by
  refine le_of_eq_add (d := succ (num 3 * monus m (num 4))) ?_
  ipra_lc 3 * natEq (eq_add_of_le h)

/-- `m < 4` and `10 < 3m` are incompatible. -/
theorem small_absurd {m : PTm n} (h₁ : Γ ⊢[PRAAx] lt m (num 4)) (h₂ : Γ ⊢[PRAAx] lt (num 10) (num 3 * m)) :
    Γ ⊢[PRAAx] Fm.bot := by
  refine absurd_of (a := num 9)
    (c := num 1 + monus (num 3 * m) (succ (num 10)) + num 3 * monus (num 4) (succ m)) ?_
  ipra_lc -natEq (eq_add_of_le h₂) - 3 * natEq (eq_add_of_le h₁)

/-- `10 < 3m` gives `4 ≤ m`. -/
theorem le_of_hyperbolic {m : PTm n} (h : Γ ⊢[PRAAx] lt (num 10) (num 3 * m)) : Γ ⊢[PRAAx] le (num 4) m :=
  .orE (lt_or_le m (num 4)) (.botE _ (small_absurd Prf.hyp0 h.wk)) Prf.hyp0

/-- H1: `10 < 3m ↔ 4 ≤ m`. -/
theorem hyperbolic_order (m : PTm n) : Γ ⊢[PRAAx] Fm.iff (lt (num 10) (num 3 * m)) (le (num 4) m) :=
  Prf.iffI (.impI (le_of_hyperbolic Prf.hyp0)) (.impI (hyperbolic_of_le Prf.hyp0))

/-! ## Angle sums and the Euler count -/

/-- P10: the Type 15 angles `150, 60, 135, 105, 90` sum to `540`. -/
theorem type15_angle_sum :
    Γ ⊢[PRAAx] (num 150 + num 60 + num 135 + num 105 + num 90 : PTm n) ≐ num 540 := by
  apply deriveNat; ipra_simps; norm_num

/-- D3: the three dual uniform pentagons have angle sum `540`. -/
theorem dual_angle_sums :
    Γ ⊢[PRAAx] ((num 120 + num 120 + num 120 + num 90 + num 90 : PTm n) ≐ num 540) ⋏
      (((num 120 + num 120 + num 90 + num 120 + num 90 : PTm n) ≐ num 540) ⋏
        ((num 120 + num 120 + num 120 + num 120 + num 60 : PTm n) ≐ num 540)) :=
  .andI (by apply deriveNat; ipra_simps; norm_num)
    (.andI (by apply deriveNat; ipra_simps; norm_num) (by apply deriveNat; ipra_simps; norm_num))

/-- S1: the dodecahedron has `V + F = E + 2` with `V = 20`, `E = 30`, `F = 12`. -/
theorem dodecahedron_euler : Γ ⊢[PRAAx] (num 20 + num 12 : PTm n) ≐ num 30 + num 2 := by
  apply deriveNat; ipra_simps; norm_num

/-- `thm:hyperbolic-order`, cleared: `1/2 + 1/5 + 1/m < 1` times `10m` is `7m + 10 < 10m`, and
`7m + 10 < 10m ↔ 4 ≤ m`. -/
theorem coxeter_hyperbolic (m : PTm n) :
    Γ ⊢[PRAAx] Fm.iff (lt (num 7 * m + num 10) (num 10 * m)) (le (num 4) m) := by
  refine .andI (.impI ?_) (.impI ?_)
  · let C := lt (num 7 * m + num 10) (num 10 * m) :: Γ
    refine le_of_hyperbolic (le_of_eq_add (d := monus (num 10 * m) (succ (num 7 * m + num 10))) ?_)
    ipra_lc natEq (eq_add_of_le (Prf.hyp0 : C ⊢[PRAAx] lt (num 7 * m + num 10) (num 10 * m)))
  · let C := le (num 4) m :: Γ
    refine le_of_eq_add (d := monus (num 3 * m) (succ (num 10))) ?_
    ipra_lc natEq (eq_add_of_le (hyperbolic_of_le (Prf.hyp0 : C ⊢[PRAAx] le (num 4) m)))

end LeanProofs.IPRA.Geometry.PentagonArithmetic
