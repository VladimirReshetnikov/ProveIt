import IPRADerivations.DiophantineNumberTheory.Coprime

/-!
# No rational square root of a nonsquare

Packet: `diophantine-number-theory/pell_ipra_2026-11-15`, Lemma `lem:irrational`: if `D` is not
a perfect square, then `p² ≠ D q²` for `q ≠ 0`.

Reduce by `g = gcd(q, p)`: `q = g s`, `p = g r`, `gcd(s, r) = 1`, and `r² = D s²`. Then
`s ∣ r²`, so `s ∣ r` by Gauss's lemma, hence `s = 1` and `D = r²`, so `isqrt D = r`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.IrrationalSqrt

open_ipra exports
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem alg₁ {p q D g r s : PTm n} (h : Γ ⊢[PRAAx] p * p ≐ D * (q * q)) (eq : Γ ⊢[PRAAx] q ≐ g * s)
    (ep : Γ ⊢[PRAAx] p ≐ g * r) : Γ ⊢[PRAAx] (g * g) * (r * r) ≐ (g * g) * (D * (s * s)) := by
  refine withEq h fun h₁ => withEq eq fun h₂ => withEq ep fun h₃ => ?_
  apply deriveNat; ipra_simps; rw [h₂, h₃] at h₁; linear_combination h₁

/-- `q ≥ 1`, `p² = D q²` give `D = (isqrt D)²`. -/
theorem square_of_rational_root {p q D : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q))
    (h : Γ ⊢[PRAAx] p * p ≐ D * (q * q)) : Γ ⊢[PRAAx] D ≐ isqrt D * isqrt D := by
  have hg := gcd_pos (B := p) hq
  have hgd := gcd_dvd' (b := p) hq
  have eq := eq_of_dvd' hg (Prf.andE₁ hgd)
  have ep := eq_of_dvd' hg (Prf.andE₂ hgd)
  have hs := pos_of_eq_mul hq eq
  have hc := coprime_quotients (c := p) hq
  -- `r² = D s²`.
  have e := mul_cancel (pos_mul hg hg) (alg₁ h eq ep)
  -- `s ∣ r²`, so `s ∣ r`, so `s = 1`.
  have d₁ : Γ ⊢[PRAAx] dvd (quo q (gcd q p)) (quo p (gcd q p) * quo p (gcd q p)) :=
    dvd_of_eq' hs (w := D * quo q (gcd q p)) (by
      refine withEq e fun h₁ => ?_
      apply deriveNat; ipra_simps; rw [h₁]; ring)
  have d₂ := gauss hs hc d₁
  have s1 := eq_one_of_coprime_dvd hs hc d₂
  -- `D = r²`.
  have eD : Γ ⊢[PRAAx] D ≐ quo p (gcd q p) * quo p (gcd q p) := by
    refine withEq e fun h₁ => withEq s1 fun h₂ => ?_
    apply deriveNat; ipra_simps; rw [h₁, h₂]; ring
  have hr : Γ ⊢[PRAAx] isqrt D ≐ quo p (gcd q p) := by
    refine isqrt_unique (le_congr (.eqRefl _) eD.eqSymm (le_refl _)) ?_
    refine le_of_eq_add (d := quo p (gcd q p) + quo p (gcd q p)) ?_
    refine withEq eD fun h₁ => ?_
    apply deriveNat; ipra_simps; rw [h₁]; ring
  exact eD.eqTrans (congrMul hr.eqSymm hr.eqSymm)

/-- Lemma `lem:irrational`; variables `0 = D`, `1 = p`, `2 = q - 1`. -/
abbrev irrationalFormula : Fm PTm 3 :=
  neg (var 0 ≐ isqrt (var 0) * isqrt (var 0)) ⟶
    neg (var 1 * var 1 ≐ var 0 * (succ (var 2) * succ (var 2)))

theorem no_rational_sqrt : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 irrationalFormula :=
  closeUniv 3 (.impI (.impI (.impE Prf.hyp1
    (square_of_rational_root (congrSucc (pred_succ _).eqSymm) Prf.hyp0))))

end LeanProofs.IPRA.DiophantineNumberTheory.IrrationalSqrt
