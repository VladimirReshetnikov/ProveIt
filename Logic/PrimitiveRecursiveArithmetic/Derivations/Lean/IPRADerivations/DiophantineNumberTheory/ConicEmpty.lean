import IPRADerivations.DiophantineNumberTheory.Coprime
import IPRADerivations.Geometry.PlatonicSolids
import IPRADerivations.Core.LinearCombination

/-!
# An empty conic detected by a prime-power obstruction

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Section `sec:conics`, "An empty conic detected by
a prime-power obstruction": the conic `X² + Y² = 3Z²` has no rational projective point. "The only square residues
modulo `3` are `0` and `1`, so `x² + y² ≡ 0 (mod 3)` forces `3 ∣ x` and `3 ∣ y`. Write `x = 3u`, `y = 3v` and
cancel `3` ... to obtain `z² = 3(u² + v²)`. The same square-residue table gives `3 ∣ z`, contradicting
primitivity. Every step is a finite divisibility calculation."

Squares do not see signs, so natural coordinates suffice.

* `sq_res`: the square-residue table: `3 ∣ x` and `x² ≡ 0`, or `x² ≡ 1 (mod 3)`;
* `sum_sq_dvd`: `x² + y² = 3w` gives `3 ∣ x` and `3 ∣ y`;
* `empty_conic`: `x² + y² = 3z²` gives `3 ∣ x`, `3 ∣ y`, `3 ∣ z`;
* `no_primitive`: no solution has `gcd(gcd(x, y), z) = 1`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.ConicEmpty

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (gcd_greatest')
open LeanProofs.IPRA.Geometry.PlatonicSolids (lt_three_cases)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem one_lt_three : Γ ⊢[PRAAx] lt (num 1) (num 3) :=
  (le_of_eq_add (d := num 1) (by apply deriveNat; ipra_simps <;> ring) : Γ ⊢[PRAAx] le (succ (num 1)) (num 3))

theorem two_lt_three : Γ ⊢[PRAAx] lt (num 2) (num 3) :=
  (le_of_eq_add (d := zero) (by apply deriveNat; ipra_simps <;> ring) : Γ ⊢[PRAAx] le (succ (num 2)) (num 3))

theorem three_pos : Γ ⊢[PRAAx] num 3 ≐ succ (pred (num 3)) := congrSucc (pred_succ (num 2)).eqSymm

/-- The square-residue table modulo `3`. -/
theorem sq_res (x : PTm n) :
    Γ ⊢[PRAAx] (dvd (num 3) x ⋏ rem (x * x) (num 3) ≐ zero) ⋎ (rem (x * x) (num 3) ≐ num 1) := by
  have d : Γ ⊢[PRAAx] (x ≐ num 3 * quo x (num 3) + rem x (num 3)) ⋏ lt (rem x (num 3)) (num 3) := div_mod x (num 2)
  refine .orE (lt_three_cases (Prf.andE₂ d)) ?_ (.orE Prf.hyp0 ?_ ?_)
  · -- `x = 3a`
    refine .orI₁ (.andI Prf.hyp0 ?_)
    have hx : ((rem x (num 3) ≐ num 0) :: Γ) ⊢[PRAAx] x ≐ num 3 * quo x (num 3) + num 0 :=
      (Prf.andE₁ d).wk.eqTrans (congrAdd (.eqRefl _) Prf.hyp0)
    have e := natEq hx
    refine Prf.andE₂ (div_mod_unique (K' := num 2) (q := num 3 * quo x (num 3) * quo x (num 3)) ?_ (zero_lt_succ _))
    ipra_lc (𝔞 x + 3 * 𝔞 (quo x (num 3))) * e
  · -- `x = 3a + 1`
    refine .orI₂ ?_
    have hx : ((rem x (num 3) ≐ num 1) :: ((rem x (num 3) ≐ num 1) ⋎ (rem x (num 3) ≐ num 2)) :: Γ) ⊢[PRAAx] x ≐ num 3 * quo x (num 3) + num 1 :=
      (Prf.andE₁ d).wk.wk.eqTrans (congrAdd (.eqRefl _) Prf.hyp0)
    have e := natEq hx
    refine Prf.andE₂ (div_mod_unique (K' := num 2) (q := num 3 * quo x (num 3) * quo x (num 3) + num 2 * quo x (num 3))
      ?_ one_lt_three)
    ipra_lc (𝔞 x + 3 * 𝔞 (quo x (num 3)) + 1) * e
  · -- `x = 3a + 2`
    refine .orI₂ ?_
    have hx : ((rem x (num 3) ≐ num 2) :: ((rem x (num 3) ≐ num 1) ⋎ (rem x (num 3) ≐ num 2)) :: Γ) ⊢[PRAAx] x ≐ num 3 * quo x (num 3) + num 2 :=
      (Prf.andE₁ d).wk.wk.eqTrans (congrAdd (.eqRefl _) Prf.hyp0)
    have e := natEq hx
    refine Prf.andE₂ (div_mod_unique (K' := num 2)
      (q := num 3 * quo x (num 3) * quo x (num 3) + num 4 * quo x (num 3) + num 1) ?_ one_lt_three)
    ipra_lc (𝔞 x + 3 * 𝔞 (quo x (num 3)) + 2) * e

/-- A nonzero residue `S c < 3` contradicts `x² + y² = 3w`. -/
theorem residue_absurd {x y w Qx Qy c : PTm n} (h : Γ ⊢[PRAAx] x * x + y * y ≐ num 3 * w)
    (hq : Γ ⊢[PRAAx] x * x + y * y ≐ num 3 * (Qx + Qy) + succ c) (hc : Γ ⊢[PRAAx] lt (succ c) (num 3)) :
    Γ ⊢[PRAAx] Fm.bot := by
  have h0 : Γ ⊢[PRAAx] num 3 * w ≐ num 3 * w + zero := (add_zero _).eqSymm
  have u := euclid_unique (K := num 3) ((hq.eqSymm.eqTrans h).eqTrans h0) hc (zero_lt_succ (num 2))
  exact succ_ne_zero (Prf.andE₂ u)

/-- Adding the residues: `x² + y² = 3(⌊x²/3⌋ + ⌊y²/3⌋) + (r_x + r_y)`. -/
theorem sum_residue {Δ : List (Fm PTm n)} {x y rx ry c : PTm n} (hrx : Δ ⊢[PRAAx] rem (x * x) (num 3) ≐ rx)
    (hry : Δ ⊢[PRAAx] rem (y * y) (num 3) ≐ ry) (hc : Δ ⊢[PRAAx] rx + ry ≐ succ c) :
    Δ ⊢[PRAAx] x * x + y * y ≐ num 3 * (quo (x * x) (num 3) + quo (y * y) (num 3)) + succ c := by
  have dx : Δ ⊢[PRAAx] x * x ≐ num 3 * quo (x * x) (num 3) + rem (x * x) (num 3) := Prf.andE₁ (div_mod (x * x) (num 2))
  have dy : Δ ⊢[PRAAx] y * y ≐ num 3 * quo (y * y) (num 3) + rem (y * y) (num 3) := Prf.andE₁ (div_mod (y * y) (num 2))
  ipra_lc natEq dx + natEq dy + natEq hrx + natEq hry + natEq hc

/-- `x² + y² = 3w` gives `3 ∣ x` and `3 ∣ y`. -/
theorem sum_sq_dvd {x y w : PTm n} (h : Γ ⊢[PRAAx] x * x + y * y ≐ num 3 * w) :
    Γ ⊢[PRAAx] dvd (num 3) x ⋏ dvd (num 3) y := by
  refine .orE (sq_res x) ?_ ?_
  · refine .orE (sq_res y) (.andI (Prf.andE₁ Prf.hyp1) (Prf.andE₁ Prf.hyp0)) ?_
    exact .botE _ (residue_absurd h.wk.wk (sum_residue (c := zero) (Prf.andE₂ Prf.hyp1) Prf.hyp0
      (by apply deriveNat; ipra_simps <;> ring)) one_lt_three)
  · refine .orE (sq_res y) ?_ ?_
    · exact .botE _ (residue_absurd h.wk.wk (sum_residue (c := zero) Prf.hyp1 (Prf.andE₂ Prf.hyp0)
        (by apply deriveNat; ipra_simps <;> ring)) one_lt_three)
    · exact .botE _ (residue_absurd h.wk.wk (sum_residue (c := num 1) Prf.hyp1 Prf.hyp0
        (by apply deriveNat; ipra_simps <;> ring)) two_lt_three)

/-- `x² + y² = 3z²` gives `3 ∣ x`, `3 ∣ y` and `3 ∣ z`. -/
theorem empty_conic {x y z : PTm n} (h : Γ ⊢[PRAAx] x * x + y * y ≐ num 3 * (z * z)) :
    Γ ⊢[PRAAx] dvd (num 3) x ⋏ (dvd (num 3) y ⋏ dvd (num 3) z) := by
  have hxy := sum_sq_dvd h
  have hx3 : Γ ⊢[PRAAx] x ≐ num 3 * quo x (num 3) := eq_of_dvd (d' := num 2) (Prf.andE₁ hxy)
  have hy3 : Γ ⊢[PRAAx] y ≐ num 3 * quo y (num 3) := eq_of_dvd (d' := num 2) (Prf.andE₂ hxy)
  have hz : Γ ⊢[PRAAx] z * z ≐ num 3 * (quo x (num 3) * quo x (num 3) + quo y (num 3) * quo y (num 3)) := by
    refine mul_cancel three_pos ?_
    ipra_lc -natEq h + (𝔞 x + 3 * 𝔞 (quo x (num 3))) * natEq hx3 + (𝔞 y + 3 * 𝔞 (quo y (num 3))) * natEq hy3
  have hz' : Γ ⊢[PRAAx] z * z + zero * zero ≐
      num 3 * (quo x (num 3) * quo x (num 3) + quo y (num 3) * quo y (num 3)) := by
    ipra_lc natEq hz
  exact .andI (Prf.andE₁ hxy) (.andI (Prf.andE₂ hxy) (Prf.andE₁ (sum_sq_dvd hz')))

/-- No solution of `x² + y² = 3z²` is primitive. -/
theorem no_primitive {x y z : PTm n} (h : Γ ⊢[PRAAx] x * x + y * y ≐ num 3 * (z * z))
    (hp : Γ ⊢[PRAAx] gcd (gcd x y) z ≐ one) : Γ ⊢[PRAAx] Fm.bot := by
  have d := empty_conic h
  have g1 := gcd_greatest' three_pos (Prf.andE₁ d) (Prf.andE₁ (Prf.andE₂ d))
  have g2 := gcd_greatest' three_pos g1 (Prf.andE₂ (Prf.andE₂ d))
  have d1 : Γ ⊢[PRAAx] dvd (num 3) one := dvd_congr hp g2
  have r1 : Γ ⊢[PRAAx] rem one (num 3) ≐ one :=
    Prf.andE₂ (div_mod_unique (K' := num 2) (q := zero) (by apply deriveNat; ipra_simps <;> ring) one_lt_three)
  exact succ_ne_zero (r1.eqSymm.eqTrans d1)

end LeanProofs.IPRA.DiophantineNumberTheory.ConicEmpty
