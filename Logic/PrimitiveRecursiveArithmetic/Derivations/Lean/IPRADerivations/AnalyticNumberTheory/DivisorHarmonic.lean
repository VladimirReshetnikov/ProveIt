import IPRADerivations.AnalyticNumberTheory.DivisorHyperbola

/-!
# The divisor sum against the harmonic sum (`pnt_ipra_constructive_2026-11-14`, `sb:divisor-approx`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, proof of Lemma
`sb:divisor-approx`: "`D(y) = 2 Σ_{n≤m} ⌊y/n⌋ − m² = 2yH_m − m² + e`, `|e| ≤ 2m`" (`m = ⌊√y⌋`).
`DivisorHyperbola.hyperbola` is the first equality (`S(y, y) + m² = 2 S(m, y)`, where `D(y) = S(y, y)`).
This module proves the second, with the harmonic sum `H_m = S(m, F)/F` at a common denominator
`F = L!` (`m ≤ L`, so every `n ≤ m` divides `F`):

* `floor_pt`: `F ⌊y/n⌋ ≤ y (F/n) ≤ F ⌊y/n⌋ + F` for `n ≤ L` (Euclidean division of `y` by `n`);
* `floor_sum`: `F S(m, y) ≤ y S(m, F) ≤ F S(m, y) + mF`, i.e. `Σ_{n≤m} ⌊y/n⌋ = y H_m − e'`, `0 ≤ e' ≤ m`;
* `divisor_harmonic`: `F (D(y) + m²) ≤ 2y S(m, F) ≤ F (D(y) + m² + 2m)`, i.e.
  `D(y) = 2y H_m − m² + e` with `−2m ≤ e ≤ 0`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.DivisorHarmonic

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB inst2_h)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorHyperbola (hyperbola)
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (sum_ones)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Analysis.Products (fact)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `F ⌊y/(k+1)⌋ ≤ y ⌊F/(k+1)⌋ ≤ F ⌊y/(k+1)⌋ + F` for `F = L!`, `k + 1 ≤ L`. -/
theorem floor_pt (k y : PTm n) {L : PTm n} (hk : Γ ⊢[PRAAx] le (succ k) L) :
    Γ ⊢[PRAAx] le (fact L * quo y (succ k)) (y * quo (fact L) (succ k)) ⋏
      le (y * quo (fact L) (succ k)) (fact L * quo y (succ k) + fact L) := by
  have dm := div_mod (Γ := Γ) y k
  refine .andI ?_ ?_
  · refine le_of_eq_add (d := rem y (succ k) * quo (fact L) (succ k)) ?_
    ipra_lc 𝔞 (quo (fact L) (succ k)) * natEq (Prf.andE₁ dm) -
      𝔞 (quo y (succ k)) * natEq (eq_of_dvd' (congrSucc (pred_succ _).eqSymm) (dvd_fact hk))
  · refine le_of_eq_add (d := succ (monus (succ k) (succ (rem y (succ k)))) * quo (fact L) (succ k)) ?_
    ipra_lc (𝔞 (quo y (succ k)) + 1) * natEq (eq_of_dvd' (congrSucc (pred_succ _).eqSymm) (dvd_fact hk)) -
      𝔞 (quo (fact L) (succ k)) * natEq (Prf.andE₁ dm) +
      𝔞 (quo (fact L) (succ k)) * natEq (eq_add_of_le (Prf.andE₂ dm))

/-! ## The bodies, with parameter `z = (F, y)` -/

/-- `F ⌊y/(k+1)⌋`. -/
abbrev Ab : PTm 2 := fstT (var 1) * quo (sndT (var 1)) (succ (var 0))
/-- `y ⌊F/(k+1)⌋`. -/
abbrev Bb : PTm 2 := sndT (var 1) * quo (fstT (var 1)) (succ (var 0))
/-- `F`. -/
abbrev Cb : PTm 2 := fstT (var 1)

theorem inst2_Ab (k z : PTm n) : inst2 Ab k z = fstT z * quo (sndT z) (succ k) := by simp [inst2]
theorem inst2_Bb (k z : PTm n) : inst2 Bb k z = sndT z * quo (fstT z) (succ k) := by simp [inst2]
theorem inst2_Cb (k z : PTm n) : inst2 Cb k z = fstT z := by simp [inst2]
theorem inst2_one (k z : PTm n) : inst2 (one : PTm 2) k z = one := by simp [inst2]

theorem shift_fact' (L : PTm n) : Syn.shift (fact L) = fact (Syn.shift L) := by simp [Syn.shift]

theorem sumA (m F y : PTm n) : Γ ⊢[PRAAx] ap2 (sumF Ab) m (pairT F y) ≐ F * S m y := by
  refine sum_scale Ab hB m F y (pairT F y) (.allI (.impI ?_))
  rw [inst2_Ab, inst2_h, shift_pairT]
  exact congrMul (fst_pair _ _) (congrAp2 quoF (snd_pair _ _) (.eqRefl _))

theorem sumB (m F y : PTm n) : Γ ⊢[PRAAx] ap2 (sumF Bb) m (pairT F y) ≐ y * S m F := by
  refine sum_scale Bb hB m y F (pairT F y) (.allI (.impI ?_))
  rw [inst2_Bb, inst2_h, shift_pairT]
  exact congrMul (snd_pair _ _) (congrAp2 quoF (fst_pair _ _) (.eqRefl _))

theorem sumC (m F y : PTm n) : Γ ⊢[PRAAx] ap2 (sumF Cb) m (pairT F y) ≐ F * m := by
  refine (sum_scale Cb (one : PTm 2) m F F (pairT F y) (.allI (.impI ?_))).eqTrans
    (congrMul (.eqRefl _) (sum_ones m F))
  rw [inst2_Cb, inst2_one, shift_pairT]
  exact (fst_pair _ _).eqTrans (by ipra_ring)

/-- `F S(m, y) ≤ y S(m, F) ≤ F S(m, y) + mF` for `F = L!`, `m ≤ L`. -/
theorem floor_sum {m y L : PTm n} (hmL : Γ ⊢[PRAAx] le m L) :
    Γ ⊢[PRAAx] le (fact L * S m y) (y * S m (fact L)) ⋏
      le (y * S m (fact L)) (fact L * S m y + fact L * m) := by
  have hmL' := LeanProofs.IPRA.Order.shift_le hmL
  have ptw : ∀ (_ : Unit), (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) ⊢[PRAAx]
      le (fact (Syn.shift L) * quo (Syn.shift y) (succ (var 0))) (Syn.shift y * quo (fact (Syn.shift L)) (succ (var 0))) ⋏
      le (Syn.shift y * quo (fact (Syn.shift L)) (succ (var 0)))
        (fact (Syn.shift L) * quo (Syn.shift y) (succ (var 0)) + fact (Syn.shift L)) :=
    fun _ => floor_pt (var 0) (Syn.shift y) (le_trans Prf.hyp0 hmL'.wk)
  have eA_at : (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) ⊢[PRAAx]
      fstT (pairT (fact (Syn.shift L)) (Syn.shift y)) * quo (sndT (pairT (fact (Syn.shift L)) (Syn.shift y))) (succ (var 0)) ≐
        fact (Syn.shift L) * quo (Syn.shift y) (succ (var 0)) :=
    congrMul (fst_pair _ _) (congrAp2 quoF (snd_pair _ _) (.eqRefl _))
  have eB_at : (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) ⊢[PRAAx]
      sndT (pairT (fact (Syn.shift L)) (Syn.shift y)) * quo (fstT (pairT (fact (Syn.shift L)) (Syn.shift y))) (succ (var 0)) ≐
        Syn.shift y * quo (fact (Syn.shift L)) (succ (var 0)) :=
    congrMul (snd_pair _ _) (congrAp2 quoF (fst_pair _ _) (.eqRefl _))
  have low := sum_le_params Ab Bb (pairT (fact L) y) (pairT (fact L) y) m (.allI (.impI (by
    rw [inst2_Ab, inst2_Bb, shift_pairT, shift_fact']
    exact le_congr eA_at.eqSymm eB_at.eqSymm (Prf.andE₁ (ptw ())))))
  have up := sum_le_params Bb (addBody Ab Cb) (pairT (fact L) y) (pairT (fact L) y) m (.allI (.impI (by
    rw [inst2_Bb, inst2_addBody, inst2_Ab, inst2_Cb, shift_pairT, shift_fact']
    exact le_congr eB_at.eqSymm (congrAdd eA_at.eqSymm (fst_pair _ _).eqSymm) (Prf.andE₂ (ptw ())))))
  have eA := natEq (sumA (Γ := Γ) m (fact L) y)
  have eB := natEq (sumB (Γ := Γ) m (fact L) y)
  have eC := natEq (sumC (Γ := Γ) m (fact L) y)
  have eAC := natEq (sum_add (Γ := Γ) Ab Cb m (pairT (fact L) y))
  refine .andI ?_ ?_
  · ipra_le sl low with eB - eA
  · ipra_le sl up with eA + eC + eAC - eB

/-- `sb:divisor-approx`, the hyperbola step: `F (D(y) + m²) ≤ 2y S(m, F) ≤ F (D(y) + m² + 2m)` for
`m² ≤ y < (m+1)²`, `F = L!`, `m ≤ L`; i.e. `D(y) = 2y H_m − m² + e` with `−2m ≤ e ≤ 0`. -/
theorem divisor_harmonic {y m L : PTm n} (h1 : Γ ⊢[PRAAx] le (m * m) y) (h2 : Γ ⊢[PRAAx] lt y (succ m * succ m))
    (hmL : Γ ⊢[PRAAx] le m L) :
    Γ ⊢[PRAAx] le (fact L * (S y y + m * m)) (two * (y * S m (fact L))) ⋏
      le (two * (y * S m (fact L))) (fact L * (S y y + m * m + two * m)) := by
  have hyp := natEq (hyperbola h1 h2)
  have fs := floor_sum (y := y) hmL
  have lo := Prf.andE₁ fs
  have hi := Prf.andE₂ fs
  refine .andI ?_ ?_
  · ipra_le 2 * sl lo with 𝔞 (fact L) * hyp
  · ipra_le 2 * sl hi with -(𝔞 (fact L) * hyp)

end LeanProofs.IPRA.AnalyticNumberTheory.DivisorHarmonic

export_ipra AnalyticNumberTheory.DivisorHarmonic (shift_fact')
