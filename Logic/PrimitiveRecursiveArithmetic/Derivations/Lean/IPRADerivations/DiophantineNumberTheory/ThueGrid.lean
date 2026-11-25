import IPRADerivations.Core.Pigeonhole
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.DiophantineNumberTheory.ModularCertificate
import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.Core.LinearCombination

/-!
# A modular root of `−1` gives a sum of two squares

Packet: `diophantine-number-theory/fermat_two_squares_ipra_2026-11-22`, `fermat_two_squares_ipra.tex`,
`thm:root-to-squares` ("A modular root gives a representation") with its proof in §"Root-to-squares
extraction": for `n > 0` and `n ∣ t² + 1` there are explicit terms `G₁(n, t)`, `G₂(n, t)` with
`G₁² + G₂² = n`. Primality is not a hypothesis.

With `h = ⌊√n⌋` and `B = h + 1`: if `h² = n` the output is `(0, h)`. Otherwise the `n + 1` indices
`i ≤ n` are the points `(u_i, v_i) = (i mod B, ⌊i/B⌋)` of the grid `[0, h]²`, labelled by
`(u_i + t v_i) mod n`; the pigeonhole principle with search witnesses (`Core/Pigeonhole`) returns `I < J ≤ n`
with equal labels, and `x = |u_J − u_I|`, `y = |v_J − v_I|` satisfy `x² + y² = n`.

* `ad`, `ad_cases`: the absolute difference and its two cases;
* `rem_cancel`: additive cancellation modulo `n`;
* `same_orient`, `congr_sq`: in each of the four sign patterns the collision gives `x² ≡ (t y)² (mod n)`
  (either `x + t y ≡ 0` or `x ≡ t y`); the signed identity `x² + y² = (x + t y)(x − t y) + (t² + 1) y²` of the
  paper is not used;
* `sum_dvd`: `n ∣ x² + y²`;
* `finish`: `n ∣ S`, `1 ≤ S`, `S < 2n` give `S = n`, with `S = x² + y² ≤ 2h² < 2n`;
* `core`: the statement for abstract points of the grid;
* `grid_squares`: the collision of the search gives `gX² + gY² = n` when `n` is not a square;
* `G1`, `G2`, `root_to_squares` (`thm:root-to-squares`).

The outputs are not sorted (the paper returns `min`, `max`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.ThueGrid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_lt')
open LeanProofs.IPRA.Combinatorics.LegendreDigits (dm)
open LeanProofs.IPRA.DiophantineNumberTheory.ModularCertificate (rem_add_mul rem_add_congr rem_mul_congr2 shift_pos)
open LeanProofs.IPRA.Foundations.BoundedReflection (eqb_cases eq_of_eqb one_ne_zero)
open LeanProofs.IPRA.Pigeonhole (phpI phpJ pigeonhole)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Absolute differences -/

/-- `|a − b|`. -/
abbrev ad (a b : PTm k) : PTm k := monus a b + monus b a

theorem ad_cases (a b : PTm k) : Γ ⊢[PRAAx] (b ≐ a + ad a b) ⋎ (a ≐ b + ad a b) := by
  refine .orE (le_total a b) ?_ ?_
  · have hz : (le a b :: Γ) ⊢[PRAAx] monus a b ≐ zero := Prf.hyp0
    have z := natEq hz
    have e := natEq (eq_add_of_le (Prf.hyp0 (Γ := Γ) (φ := le a b)))
    exact .orI₁ (by apply deriveNat; ipra_simps; linear_combination e - z)
  · have hz : (le b a :: Γ) ⊢[PRAAx] monus b a ≐ zero := Prf.hyp0
    have z := natEq hz
    have e := natEq (eq_add_of_le (Prf.hyp0 (Γ := Γ) (φ := le b a)))
    exact .orI₂ (by apply deriveNat; ipra_simps; linear_combination e - z)

/-- A vanishing difference identifies the two numbers. -/
theorem eq_of_zero {a a' X : PTm k} (hx : Γ ⊢[PRAAx] (a' ≐ a + X) ⋎ (a ≐ a' + X))
    (x0 : Γ ⊢[PRAAx] X ≐ zero) : Γ ⊢[PRAAx] a ≐ a' := by
  refine .orE hx ?_ ?_
  · exact (Prf.hyp0.eqTrans ((congrAdd (.eqRefl _) x0.wk).eqTrans (add_zero _))).eqSymm
  · exact Prf.hyp0.eqTrans ((congrAdd (.eqRefl _) x0.wk).eqTrans (add_zero _))

/-- A difference of two numbers `≤ h` is `≤ h`. -/
theorem le_of_diff {a a' X h : PTm k} (hx : Γ ⊢[PRAAx] (a' ≐ a + X) ⋎ (a ≐ a' + X))
    (ha : Γ ⊢[PRAAx] le a h) (ha' : Γ ⊢[PRAAx] le a' h) : Γ ⊢[PRAAx] le X h := by
  refine .orE hx ?_ ?_
  · have e := natEq (Prf.hyp0 (Γ := Γ) (φ := a' ≐ a + X))
    have h1 : ((a' ≐ a + X) :: Γ) ⊢[PRAAx] le a' h := ha'.wk
    ipra_le sl h1 + 𝔞 a with e
  · have e := natEq (Prf.hyp0 (Γ := Γ) (φ := a ≐ a' + X))
    have h1 : ((a ≐ a' + X) :: Γ) ⊢[PRAAx] le a h := ha.wk
    ipra_le sl h1 + 𝔞 a' with e

/-! ## Congruences -/

/-- Additive cancellation modulo `n`. -/
theorem rem_cancel {n c a b : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n))
    (h : Γ ⊢[PRAAx] rem (c + a) n ≐ rem (c + b) n) : Γ ⊢[PRAAx] rem a n ≐ rem b n := by
  have d1 := natEq (Prf.andE₁ (dm hn (c + a))); have d2 := natEq (Prf.andE₁ (dm hn (c + b)))
  have e : Γ ⊢[PRAAx] n * quo (c + b) n + a ≐ n * quo (c + a) n + b := by
    ipra_lc d1 - d2 + natEq h
  exact (rem_add_mul hn (quo (c + b) n) a).eqSymm.eqTrans
    ((congrAp2 remF e (.eqRefl _)).eqTrans (rem_add_mul hn (quo (c + a) n) b))

theorem sq_alg1 (X T : PTm k) : Γ ⊢[PRAAx] (X + T) * X ≐ T * X + X * X := by
  ipra_ring

theorem sq_alg2 (X T : PTm k) : Γ ⊢[PRAAx] (X + T) * T ≐ T * X + T * T := by
  ipra_ring

/-- `x + T ≡ 0` gives `x² ≡ T²`. -/
theorem same_orient {n c X T : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n))
    (h : Γ ⊢[PRAAx] rem c n ≐ rem (c + (X + T)) n) : Γ ⊢[PRAAx] rem (X * X) n ≐ rem (T * T) n := by
  have h0 : Γ ⊢[PRAAx] rem (c + zero) n ≐ rem (c + (X + T)) n :=
    (congrAp2 remF (add_zero c) (.eqRefl _)).eqTrans h
  have z0 := (rem_cancel hn h0).eqSymm
  have m1 := (rem_mul_congr2 hn z0 (.eqRefl (rem X n))).eqTrans (congrAp2 remF (zero_mul X) (.eqRefl _))
  have m2 := (rem_mul_congr2 hn z0 (.eqRefl (rem T n))).eqTrans (congrAp2 remF (zero_mul T) (.eqRefl _))
  have m := m1.eqTrans m2.eqSymm
  exact rem_cancel hn ((congrAp2 remF (sq_alg1 X T) (.eqRefl _)).eqSymm.eqTrans
    (m.eqTrans (congrAp2 remF (sq_alg2 X T) (.eqRefl _))))

theorem lin1 {t uI vI uJ vJ X Y : PTm k} (ex : Γ ⊢[PRAAx] uJ ≐ uI + X) (ey : Γ ⊢[PRAAx] vJ ≐ vI + Y) :
    Γ ⊢[PRAAx] uJ + t * vJ ≐ (uI + t * vI) + (X + t * Y) := by
  ipra_lc natEq ex + 𝔞 t * natEq ey

theorem lin2 {t v v' Y c : PTm k} (ey : Γ ⊢[PRAAx] v ≐ v' + Y) :
    Γ ⊢[PRAAx] c + t * v ≐ (c + t * v') + t * Y := by
  ipra_lc 𝔞 t * natEq ey

theorem lin3 {t u u' X w : PTm k} (ex : Γ ⊢[PRAAx] u ≐ u' + X) :
    Γ ⊢[PRAAx] u + t * w ≐ (u' + t * w) + X := by
  ipra_lc natEq ex

/-- The collision in each of the four sign patterns: `x² ≡ (t y)² (mod n)`. -/
theorem congr_sq {n t uI vI uJ vJ X Y : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n))
    (hc : Γ ⊢[PRAAx] rem (uI + t * vI) n ≐ rem (uJ + t * vJ) n)
    (hx : Γ ⊢[PRAAx] (uJ ≐ uI + X) ⋎ (uI ≐ uJ + X))
    (hy : Γ ⊢[PRAAx] (vJ ≐ vI + Y) ⋎ (vI ≐ vJ + Y)) :
    Γ ⊢[PRAAx] rem (X * X) n ≐ rem ((t * Y) * (t * Y)) n := by
  refine .orE hx ?_ ?_
  · refine .orE hy.wk ?_ ?_
    · -- `u_J = u_I + x`, `v_J = v_I + y`
      exact same_orient hn.wk.wk (hc.wk.wk.eqTrans (congrAp2 remF (lin1 Prf.hyp1 Prf.hyp0) (.eqRefl _)))
    · -- `u_J = u_I + x`, `v_I = v_J + y`
      have e1 := lin2 (Γ := (vI ≐ vJ + Y) :: (uJ ≐ uI + X) :: Γ) (t := t) (c := uI) Prf.hyp0
      have e2 := lin3 (Γ := (vI ≐ vJ + Y) :: (uJ ≐ uI + X) :: Γ) (t := t) (w := vJ) Prf.hyp1
      have hc' := (congrAp2 remF e1 (.eqRefl n)).eqSymm.eqTrans (hc.wk.wk.eqTrans (congrAp2 remF e2 (.eqRefl n)))
      have hB := (rem_cancel hn.wk.wk hc').eqSymm
      exact rem_mul_congr2 hn.wk.wk hB hB
  · refine .orE hy.wk ?_ ?_
    · -- `u_I = u_J + x`, `v_J = v_I + y`
      have e1 := lin3 (Γ := (vJ ≐ vI + Y) :: (uI ≐ uJ + X) :: Γ) (t := t) (w := vI) Prf.hyp1
      have e2 := lin2 (Γ := (vJ ≐ vI + Y) :: (uI ≐ uJ + X) :: Γ) (t := t) (c := uJ) Prf.hyp0
      have hc' := (congrAp2 remF e1 (.eqRefl n)).eqSymm.eqTrans (hc.wk.wk.eqTrans (congrAp2 remF e2 (.eqRefl n)))
      have hB := rem_cancel hn.wk.wk hc'
      exact rem_mul_congr2 hn.wk.wk hB hB
    · -- `u_I = u_J + x`, `v_I = v_J + y`
      exact same_orient hn.wk.wk (hc.wk.wk.eqSymm.eqTrans (congrAp2 remF (lin1 Prf.hyp1 Prf.hyp0) (.eqRefl _)))

theorem norm_alg (t Y : PTm k) : Γ ⊢[PRAAx] (t * Y) * (t * Y) + Y * Y ≐ (t * t + one) * (Y * Y) := by
  ipra_ring

/-- `n ∣ t² + 1` and `x² ≡ (t y)²` give `n ∣ x² + y²`. -/
theorem sum_dvd {n t X Y : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n)) (hd : Γ ⊢[PRAAx] dvd n (t * t + one))
    (hC : Γ ⊢[PRAAx] rem (X * X) n ≐ rem ((t * Y) * (t * Y)) n) : Γ ⊢[PRAAx] dvd n (X * X + Y * Y) := by
  have a1 := rem_add_congr hn hC (.eqRefl (rem (Y * Y) n))
  have hd' : Γ ⊢[PRAAx] rem (t * t + one) n ≐ rem zero n := hd.eqTrans (rem_zero n).eqSymm
  have a2 := rem_mul_congr2 hn hd' (.eqRefl (rem (Y * Y) n))
  exact a1.eqTrans ((congrAp2 remF (norm_alg t Y) (.eqRefl _)).eqTrans
    (a2.eqTrans ((congrAp2 remF (zero_mul _) (.eqRefl _)).eqTrans (rem_zero n))))

/-! ## The size argument -/

/-- `x² + y² ≥ 1` unless `x = y = 0`. -/
theorem pos_of_not_both {X Y : PTm k} (h : ((Y ≐ zero) :: (X ≐ zero) :: Γ) ⊢[PRAAx] Fm.bot) :
    Γ ⊢[PRAAx] le one (X * X + Y * Y) := by
  refine .orE (zero_or_succ X) ?_ ?_
  · refine .orE (zero_or_succ Y) (.botE _ h) ?_
    have e := natEq (Prf.hyp0 (Γ := (X ≐ zero) :: Γ) (φ := Y ≐ succ (pred Y)))
    ipra_le 𝔞 (pred Y) * 𝔞 (pred Y) + 2 * 𝔞 (pred Y) + 𝔞 X * 𝔞 X with (𝔞 Y + 𝔞 (pred Y) + 1) * e
  · have e := natEq (Prf.hyp0 (Γ := Γ) (φ := X ≐ succ (pred X)))
    ipra_le 𝔞 (pred X) * 𝔞 (pred X) + 2 * 𝔞 (pred X) + 𝔞 Y * 𝔞 Y with (𝔞 X + 𝔞 (pred X) + 1) * e

/-- `n ∣ S`, `1 ≤ S` and `S = x² + y²` with `x, y ≤ h`, `h² < n` give `S = n`. -/
theorem finish {n h X Y : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n)) (hlo : Γ ⊢[PRAAx] lt (h * h) n)
    (hX : Γ ⊢[PRAAx] le X h) (hY : Γ ⊢[PRAAx] le Y h) (hdv : Γ ⊢[PRAAx] dvd n (X * X + Y * Y))
    (hS1 : Γ ⊢[PRAAx] le one (X * X + Y * Y)) : Γ ⊢[PRAAx] X * X + Y * Y ≐ n := by
  have dS : Γ ⊢[PRAAx] X * X + Y * Y ≐ n * quo (X * X + Y * Y) n + zero :=
    (Prf.andE₁ (dm hn (X * X + Y * Y))).eqTrans (congrAdd (.eqRefl _) hdv)
  have hS2 : Γ ⊢[PRAAx] lt (X * X + Y * Y) (two * n) := by
    ipra_le 2 * sl hlo + sl hX * (𝔞 h + 𝔞 X) + sl hY * (𝔞 h + 𝔞 Y) + 1
  refine .orE (lt_or_le (quo (X * X + Y * Y) n) two) ?_ ?_
  · refine .orE (lt_succ_cases (Prf.hyp0 (Γ := Γ) (φ := lt (quo (X * X + Y * Y) n) two))) ?_ ?_
    · refine .orE (lt_succ_cases (Prf.hyp0 (Γ := lt (quo (X * X + Y * Y) n) two :: Γ)
        (φ := lt (quo (X * X + Y * Y) n) one))) (lt_zero_absurd _ Prf.hyp0) ?_
      -- the quotient is `0`
      have q0 := natEq (Prf.hyp0 (Γ := lt (quo (X * X + Y * Y) n) one :: lt (quo (X * X + Y * Y) n) two :: Γ)
        (φ := quo (X * X + Y * Y) n ≐ zero))
      have dS' : ((quo (X * X + Y * Y) n ≐ zero) :: lt (quo (X * X + Y * Y) n) one ::
          lt (quo (X * X + Y * Y) n) two :: Γ) ⊢[PRAAx]
          X * X + Y * Y ≐ n * quo (X * X + Y * Y) n + zero := dS.wk.wk.wk
      have dSn := natEq dS'
      have hS1' : ((quo (X * X + Y * Y) n ≐ zero) :: lt (quo (X * X + Y * Y) n) one ::
          lt (quo (X * X + Y * Y) n) two :: Γ) ⊢[PRAAx] le one (X * X + Y * Y) := hS1.wk.wk.wk
      have bad : ((quo (X * X + Y * Y) n ≐ zero) :: lt (quo (X * X + Y * Y) n) one ::
          lt (quo (X * X + Y * Y) n) two :: Γ) ⊢[PRAAx] le one zero := by
        ipra_le sl hS1' with dSn + 𝔞 n * q0
      exact lt_zero_absurd _ bad
    · -- the quotient is `1`
      have q1 := natEq (Prf.hyp0 (Γ := lt (quo (X * X + Y * Y) n) two :: Γ)
        (φ := quo (X * X + Y * Y) n ≐ one))
      have dS' : ((quo (X * X + Y * Y) n ≐ one) :: lt (quo (X * X + Y * Y) n) two :: Γ) ⊢[PRAAx]
          X * X + Y * Y ≐ n * quo (X * X + Y * Y) n + zero := dS.wk.wk
      have dSn := natEq dS'
      apply deriveNat; ipra_simps
      linear_combination dSn + 𝔞 n * q1
  · -- the quotient is at least `2`
    have hq : (le two (quo (X * X + Y * Y) n) :: Γ) ⊢[PRAAx] le two (quo (X * X + Y * Y) n) := Prf.hyp0
    have dSn := natEq (dS.wk (ψ := le two (quo (X * X + Y * Y) n)))
    have hS2' : (le two (quo (X * X + Y * Y) n) :: Γ) ⊢[PRAAx] lt (X * X + Y * Y) (two * n) := hS2.wk
    have bad : (le two (quo (X * X + Y * Y) n) :: Γ) ⊢[PRAAx] le one zero := by
      ipra_le sl hS2' + 𝔞 n * sl hq with dSn
    exact lt_zero_absurd _ bad

/-! ## The statement for abstract points of the grid -/

/-- Two distinct points `(u_I, v_I)`, `(u_J, v_J)` of the grid `[0, h]²` with the same label, for a
non-square `n` with `h² < n` and `n ∣ t² + 1`: the coordinate differences `x`, `y` satisfy `x² + y² = n`. -/
theorem core {n t h uI uJ vI vJ X Y I J : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n))
    (hlo : Γ ⊢[PRAAx] lt (h * h) n) (hd : Γ ⊢[PRAAx] dvd n (t * t + one))
    (dI : Γ ⊢[PRAAx] I ≐ succ h * vI + uI) (dJ : Γ ⊢[PRAAx] J ≐ succ h * vJ + uJ)
    (hIJ : Γ ⊢[PRAAx] lt I J)
    (huI : Γ ⊢[PRAAx] le uI h) (huJ : Γ ⊢[PRAAx] le uJ h) (hvI : Γ ⊢[PRAAx] le vI h)
    (hvJ : Γ ⊢[PRAAx] le vJ h)
    (hc : Γ ⊢[PRAAx] rem (uI + t * vI) n ≐ rem (uJ + t * vJ) n)
    (hx : Γ ⊢[PRAAx] (uJ ≐ uI + X) ⋎ (uI ≐ uJ + X))
    (hy : Γ ⊢[PRAAx] (vJ ≐ vI + Y) ⋎ (vI ≐ vJ + Y)) : Γ ⊢[PRAAx] X * X + Y * Y ≐ n := by
  have hC := congr_sq hn hc hx hy
  have hdv := sum_dvd hn hd hC
  have hS1 : Γ ⊢[PRAAx] le one (X * X + Y * Y) := by
    refine pos_of_not_both ?_
    have eu := eq_of_zero (Γ := (Y ≐ zero) :: (X ≐ zero) :: Γ) hx.wk.wk Prf.hyp1
    have ev := eq_of_zero (Γ := (Y ≐ zero) :: (X ≐ zero) :: Γ) hy.wk.wk Prf.hyp0
    have eIJ := dI.wk.wk.eqTrans ((congrAdd (congrMul (.eqRefl _) ev) eu).eqTrans dJ.wk.wk.eqSymm)
    exact lt_irrefl J _ (lt_congr eIJ (.eqRefl _) hIJ.wk.wk)
  exact finish hn hlo (le_of_diff hx huI huJ) (le_of_diff hy hvI hvJ) hdv hS1

/-- `⌊i/B⌋ ≤ h` for `i ≤ n < (h + 1)²`, `B = h + 1`. -/
theorem vbound {i n h v u : PTm k} (di : Γ ⊢[PRAAx] i ≐ succ h * v + u) (hi : Γ ⊢[PRAAx] le i n)
    (hhi : Γ ⊢[PRAAx] lt n ((h + one) * (h + one))) : Γ ⊢[PRAAx] le v h := by
  refine .orE (lt_or_le h v) ?_ Prf.hyp0
  have hlt : (lt h v :: Γ) ⊢[PRAAx] lt h v := Prf.hyp0
  have hi' : (lt h v :: Γ) ⊢[PRAAx] le i n := hi.wk
  have hhi' : (lt h v :: Γ) ⊢[PRAAx] lt n ((h + one) * (h + one)) := hhi.wk
  have din := natEq (di.wk (ψ := lt h v))
  have bad : (lt h v :: Γ) ⊢[PRAAx] le one zero := by
    ipra_le sl hhi' + sl hi' + 𝔞 u + (𝔞 h + 1) * sl hlt with din
  exact lt_zero_absurd _ bad

/-! ## The search -/

/-- The label `(i mod B + t ⌊i/B⌋) mod n` of the index `i`, over `0 = i`, `1 = ⟨n, t⟩`, `B = ⌊√n⌋ + 1`. -/
abbrev sgB : PTm 2 :=
  rem (rem (var 0) (succ (isqrt (fstT (var 1)))) + sndT (var 1) * quo (var 0) (succ (isqrt (fstT (var 1)))))
    (fstT (var 1))

theorem sg_at (i n t : PTm k) : Γ ⊢[PRAAx] inst2 sgB i (pairT n t) ≐
    rem (rem i (succ (isqrt n)) + t * quo i (succ (isqrt n))) n := by
  have e : inst2 sgB i (pairT n t) = rem (rem i (succ (isqrt (fstT (pairT n t)))) +
      sndT (pairT n t) * quo i (succ (isqrt (fstT (pairT n t))))) (fstT (pairT n t)) := by
    simp [inst2, subst_ap1]
  rw [e]
  have b : Γ ⊢[PRAAx] succ (isqrt (fstT (pairT n t))) ≐ succ (isqrt n) :=
    congrSucc (congrAp1 isqrtF (fst_pair n t))
  exact congrAp2 remF (congrAdd (congrAp2 remF (.eqRefl _) b)
    (congrMul (snd_pair n t) (congrAp2 quoF (.eqRefl _) b))) (fst_pair n t)

/-- The two colliding indices. -/
abbrev gI (n t : PTm k) : PTm k := phpI sgB n (pairT n t)
abbrev gJ (n t : PTm k) : PTm k := phpJ sgB n (pairT n t)

/-- The coordinate differences of the two colliding grid points. -/
abbrev gX (n t : PTm k) : PTm k := ad (rem (gI n t) (succ (isqrt n))) (rem (gJ n t) (succ (isqrt n)))
abbrev gY (n t : PTm k) : PTm k := ad (quo (gI n t) (succ (isqrt n))) (quo (gJ n t) (succ (isqrt n)))

/-- For a non-square `n > 0` with `n ∣ t² + 1`: `gX² + gY² = n`. -/
theorem grid_squares {n t : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n))
    (hlo : Γ ⊢[PRAAx] lt (isqrt n * isqrt n) n) (hd : Γ ⊢[PRAAx] dvd n (t * t + one)) :
    Γ ⊢[PRAAx] gX n t * gX n t + gY n t * gY n t ≐ n := by
  have Bpos : Γ ⊢[PRAAx] succ (isqrt n) ≐ succ (pred (succ (isqrt n))) := congrSucc (pred_succ _).eqSymm
  have hr : Γ ⊢[PRAAx] Permutation.rangeAll sgB n (pairT n t) := by
    refine .allI ?_
    rw [shift_pairT]
    exact lt_congr (sg_at _ _ _).eqSymm (.eqRefl _) (rem_lt' (shift_pos hn) _)
  have ph := pigeonhole (S := sgB) hr
  have hIJ := Prf.andE₁ ph
  have hJ := Prf.andE₁ (Prf.andE₂ ph)
  have hc := (sg_at (gI n t) n t).eqSymm.eqTrans ((Prf.andE₂ (Prf.andE₂ ph)).eqTrans (sg_at (gJ n t) n t))
  have dI := dm Bpos (gI n t); have dJ := dm Bpos (gJ n t)
  have hhi := lt_isqrt_succ_sq (Γ := Γ) n
  have huI : Γ ⊢[PRAAx] le (rem (gI n t) (succ (isqrt n))) (isqrt n) :=
    (succ_monus_succ _ _).eqSymm.eqTrans (Prf.andE₂ dI)
  have huJ : Γ ⊢[PRAAx] le (rem (gJ n t) (succ (isqrt n))) (isqrt n) :=
    (succ_monus_succ _ _).eqSymm.eqTrans (Prf.andE₂ dJ)
  have hvJ := vbound (Prf.andE₁ dJ) hJ hhi
  have hvI := vbound (Prf.andE₁ dI) (le_trans (le_of_lt hIJ) hJ) hhi
  exact core hn hlo hd (Prf.andE₁ dI) (Prf.andE₁ dJ) hIJ huI huJ hvI hvJ hc (ad_cases _ _) (ad_cases _ _)

/-! ## The two outputs -/

/-- `G₁(n, t)`: `0` if `n` is a square, otherwise the first coordinate difference. -/
abbrev G1 (n t : PTm k) : PTm k := monus one (eqb (isqrt n * isqrt n) n) * gX n t

/-- `G₂(n, t)`: `⌊√n⌋` if `n` is a square, otherwise the second coordinate difference. -/
abbrev G2 (n t : PTm k) : PTm k :=
  eqb (isqrt n * isqrt n) n * isqrt n + monus one (eqb (isqrt n * isqrt n) n) * gY n t

theorem sq_case {M Eb X Y h n : PTm k} (m0 : Γ ⊢[PRAAx] M ≐ zero) (e1 : Γ ⊢[PRAAx] Eb ≐ one)
    (ehn : Γ ⊢[PRAAx] h * h ≐ n) :
    Γ ⊢[PRAAx] (M * X) * (M * X) + (Eb * h + M * Y) * (Eb * h + M * Y) ≐ n := by
  ipra_lc (𝔞 M * 𝔞 X * 𝔞 X + 2 * 𝔞 Eb * 𝔞 h * 𝔞 Y + 𝔞 M * 𝔞 Y * 𝔞 Y) * natEq m0 + (𝔞 Eb + 1) * 𝔞 h * 𝔞 h * natEq e1 +
    natEq ehn

theorem grid_case {M Eb X Y h n : PTm k} (m1 : Γ ⊢[PRAAx] M ≐ one) (e0 : Γ ⊢[PRAAx] Eb ≐ zero)
    (hXY : Γ ⊢[PRAAx] X * X + Y * Y ≐ n) :
    Γ ⊢[PRAAx] (M * X) * (M * X) + (Eb * h + M * Y) * (Eb * h + M * Y) ≐ n := by
  ipra_lc (𝔞 M + 1) * (𝔞 X * 𝔞 X + 𝔞 Y * 𝔞 Y) * natEq m1 + (𝔞 Eb * 𝔞 h * 𝔞 h + 2 * 𝔞 h * 𝔞 M * 𝔞 Y) * natEq e0 +
    natEq hXY

/-- `thm:root-to-squares`: for `n > 0` and `n ∣ t² + 1`: `G₁(n, t)² + G₂(n, t)² = n`. -/
theorem root_to_squares {n t : PTm k} (hn : Γ ⊢[PRAAx] n ≐ succ (pred n))
    (hd : Γ ⊢[PRAAx] dvd n (t * t + one)) : Γ ⊢[PRAAx] G1 n t * G1 n t + G2 n t * G2 n t ≐ n := by
  refine .orE (eqb_cases (isqrt n * isqrt n) n) ?_ ?_
  · -- `n` is not a square
    have e0 : ((eqb (isqrt n * isqrt n) n ≐ zero) :: Γ) ⊢[PRAAx] eqb (isqrt n * isqrt n) n ≐ zero := Prf.hyp0
    have m1 := (congrMonus (.eqRefl (one : PTm k)) e0).eqTrans (monus_zero one)
    have hlo : ((eqb (isqrt n * isqrt n) n ≐ zero) :: Γ) ⊢[PRAAx] lt (isqrt n * isqrt n) n := by
      refine .orE (lt_or_eq_of_le (isqrt_le n)) Prf.hyp0 ?_
      exact one_ne_zero _ ((eqb_of_eq Prf.hyp0).eqSymm.eqTrans e0.wk)
    exact grid_case m1 e0 (grid_squares hn.wk hlo hd.wk)
  · -- `n = h²`
    have e1 : ((eqb (isqrt n * isqrt n) n ≐ one) :: Γ) ⊢[PRAAx] eqb (isqrt n * isqrt n) n ≐ one := Prf.hyp0
    have m0 := (congrMonus (.eqRefl (one : PTm k)) e1).eqTrans (monus_self one)
    exact sq_case m0 e1 (eq_of_eqb e1)

end LeanProofs.IPRA.DiophantineNumberTheory.ThueGrid
