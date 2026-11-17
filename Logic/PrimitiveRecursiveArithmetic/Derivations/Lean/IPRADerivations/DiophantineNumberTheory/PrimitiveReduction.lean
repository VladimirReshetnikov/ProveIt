import IPRADerivations.DiophantineNumberTheory.Coprime
import IPRADerivations.DiophantineNumberTheory.QuarticStep
import IPRADerivations.AnalyticNumberTheory.Smooth
import IPRADerivations.AnalyticNumberTheory.Totient

/-!
# Primitive reduction

Packet: `flt_ipra`, `sections/foundations.tex`, Lemma `lem:primitive`.

* `dvd_of_pw_dvd_pw`: `dⁿ ∣ zⁿ → d ∣ z` for `d, z, n ≥ 1`, through `g = gcd(d, z)`, the coprime
  quotients `d = g d₁`, `z = g z₁` and `d₁ ∣ z₁ⁿ` with `gcd(d₁, z₁ⁿ) = 1`;
* for a positive solution of `xⁿ + yⁿ = zⁿ` (`n ≥ 1`) and `d = gcd(x, y)`: `d ∣ z` (`prim_dvd`), the
  quotients `x', y', z'` satisfy `x'ⁿ + y'ⁿ = z'ⁿ` (`prim_eq`), are pairwise coprime
  (`prim_xy`, `prim_xz`, `prim_yz`), and `z' ≤ z` (`prim_le`);
* for a positive solution of `x⁴ + y⁴ = z²`: `d² ∣ z` and `x'⁴ + y'⁴ = (z/d²)²` with
  `gcd(x', y') = 1` (`quartic_dvd`, `quartic_eq`).

No prime factorization is used: the arguments are gcd computations and Gauss's lemma.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.PrimitiveReduction

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Foundations.ChineseRemainder (gcd_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.AnalyticNumberTheory.Smooth (pw_dvd_base)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (coprime_pow)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (q4)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `dⁿ ∣ zⁿ → d ∣ z` for `d, z, n ≥ 1`. -/
theorem dvd_of_pw_dvd_pw {d z e : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hz : Γ ⊢[PRAAx] z ≐ succ (pred z))
    (he : Γ ⊢[PRAAx] e ≐ succ (pred e)) (h : Γ ⊢[PRAAx] dvd (pw d e) (pw z e)) : Γ ⊢[PRAAx] dvd d z := by
  have hg := gcd_pos (B := z) hd
  have hgd := gcd_dvd' (b := z) hd
  have eD := eq_of_dvd' hg (Prf.andE₁ hgd)
  have eZ := eq_of_dvd' hg (Prf.andE₂ hgd)
  have hd₁ := pos_of_eq_mul hd eD
  have hcop := coprime_quotients (c := z) hd
  have ew := eq_of_dvd' (pw_pos' hd e) h
  have pz := (congrPw eZ (.eqRefl e)).eqTrans (pw_mul_base _ _ e)
  have pd := (congrPw eD (.eqRefl e)).eqTrans (pw_mul_base _ _ e)
  have e₁ : Γ ⊢[PRAAx] pw (gcd d z) e * pw (quo z (gcd d z)) e ≐
      pw (gcd d z) e * (pw (quo d (gcd d z)) e * quo (pw z e) (pw d e)) := by
    have a := natEq ew; have b := natEq pz; have c := natEq pd
    apply deriveNat; ipra_simps
    linear_combination a - b + 𝔞 (quo (pw z e) (pw d e)) * c
  have e₂ := mul_cancel (pw_pos' hg e) e₁
  have ps := (congrPw (.eqRefl (quo d (gcd d z))) he).eqTrans (pw_succ _ _)
  have hdv : Γ ⊢[PRAAx] dvd (quo d (gcd d z)) (pw (quo z (gcd d z)) e) := by
    refine dvd_of_eq' hd₁ (w := pw (quo d (gcd d z)) (pred e) * quo (pw z e) (pw d e)) ?_
    have a := natEq e₂; have b := natEq ps
    apply deriveNat; ipra_simps
    linear_combination a + 𝔞 (quo (pw z e) (pw d e)) * b
  have d1 := eq_one_of_coprime_dvd hd₁ (coprime_pow hd₁ hcop e) hdv
  have ed : Γ ⊢[PRAAx] gcd d z ≐ d :=
    ((mul_comm _ _).eqTrans (one_mul _)).eqSymm.eqTrans ((congrMul (.eqRefl _) d1.eqSymm).eqTrans eD.eqSymm)
  exact dvd_congr_left ed (Prf.andE₂ hgd)

theorem pw_zero_base {e : PTm n} (he : Γ ⊢[PRAAx] e ≐ succ (pred e)) : Γ ⊢[PRAAx] pw zero e ≐ zero :=
  (congrPw (.eqRefl zero) he).eqTrans ((pw_succ _ _).eqTrans (mul_zero _))

theorem quo_pos {a b : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hd : Γ ⊢[PRAAx] dvd (gcd a b) a) :
    Γ ⊢[PRAAx] quo a (gcd a b) ≐ succ (pred (quo a (gcd a b))) :=
  pos_of_eq_mul ha (eq_of_dvd' (gcd_pos (B := b) ha) hd)

/-- A common divisor of `u` and `w` with `uⁿ + vⁿ = wⁿ` divides `v`; so `gcd(u, v) = 1` forces
`gcd(u, w) = 1`. -/
theorem coprime_third {u v w e : PTm n} (hu : Γ ⊢[PRAAx] u ≐ succ (pred u)) (hv : Γ ⊢[PRAAx] v ≐ succ (pred v))
    (he : Γ ⊢[PRAAx] e ≐ succ (pred e)) (h : Γ ⊢[PRAAx] pw u e + pw v e ≐ pw w e)
    (huv : Γ ⊢[PRAAx] gcd u v ≐ one) : Γ ⊢[PRAAx] gcd u w ≐ one := by
  have hc := gcd_pos (B := w) hu
  have hcd := gcd_dvd' (b := w) hu
  have du := pw_dvd_base e hc (Prf.andE₁ hcd); have dw := pw_dvd_base e hc (Prf.andE₂ hcd)
  have dv := dvd_sub' (pw_pos' hc e) (dvd_congr ((h.eqSymm).eqTrans (add_comm _ _)) dw) du
  have cv := dvd_of_pw_dvd_pw hc hv he dv
  exact eq_one_of_dvd_one hc (dvd_congr huv (gcd_greatest' hc (Prf.andE₁ hcd) cv))

/-! ## Fermat's equation -/

section Fermat

variable {x y z e : PTm n} (hx : Γ ⊢[PRAAx] x ≐ succ (pred x)) (hy : Γ ⊢[PRAAx] y ≐ succ (pred y))
  (he : Γ ⊢[PRAAx] e ≐ succ (pred e)) (h : Γ ⊢[PRAAx] pw x e + pw y e ≐ pw z e)
include hx hy he h

theorem z_pos : Γ ⊢[PRAAx] z ≐ succ (pred z) := by
  refine .orE (zero_or_succ z) ?_ Prf.hyp0
  have px := pw_pos' (Γ := (z ≐ zero) :: Γ) hx.wk e
  have hz := h.wk.eqTrans ((congrPw Prf.hyp0 (.eqRefl e)).eqTrans (pw_zero_base he.wk))
  have a := natEq hz; have b := natEq px
  exact succ_ne_zero' _ (a := pred (pw x e) + pw y e) (by apply deriveNat; ipra_simps; linear_combination a - b)

/-- `d = gcd(x, y)` divides `z`. -/
theorem prim_dvd : Γ ⊢[PRAAx] dvd (gcd x y) z := by
  have hg := gcd_pos (B := y) hx
  have hgd := gcd_dvd' (b := y) hx
  have dx := pw_dvd_base e hg (Prf.andE₁ hgd); have dy := pw_dvd_base e hg (Prf.andE₂ hgd)
  exact dvd_of_pw_dvd_pw hg (z_pos hx hy he h) he (dvd_congr h (dvd_add' (pw_pos' hg e) dx dy))

/-- The reduced equation `x'ⁿ + y'ⁿ = z'ⁿ`. -/
theorem prim_eq : Γ ⊢[PRAAx] pw (quo x (gcd x y)) e + pw (quo y (gcd x y)) e ≐ pw (quo z (gcd x y)) e := by
  have hg := gcd_pos (B := y) hx
  have hgd := gcd_dvd' (b := y) hx
  have ex := (congrPw (eq_of_dvd' hg (Prf.andE₁ hgd)) (.eqRefl e)).eqTrans (pw_mul_base _ _ e)
  have ey := (congrPw (eq_of_dvd' hg (Prf.andE₂ hgd)) (.eqRefl e)).eqTrans (pw_mul_base _ _ e)
  have ez := (congrPw (eq_of_dvd' hg (prim_dvd hx hy he h)) (.eqRefl e)).eqTrans (pw_mul_base _ _ e)
  refine mul_cancel (pw_pos' hg e) ?_
  have a := natEq ex; have b := natEq ey; have c := natEq ez; have d := natEq h
  apply deriveNat; ipra_simps
  linear_combination c - a - b + d

omit he h in
theorem prim_xy : Γ ⊢[PRAAx] gcd (quo x (gcd x y)) (quo y (gcd x y)) ≐ one := coprime_quotients hx

theorem prim_xz : Γ ⊢[PRAAx] gcd (quo x (gcd x y)) (quo z (gcd x y)) ≐ one := by
  have hgd := gcd_dvd' (b := y) hx
  exact coprime_third (quo_pos hx (Prf.andE₁ hgd))
    (pos_of_eq_mul hy (eq_of_dvd' (gcd_pos (B := y) hx) (Prf.andE₂ hgd))) he (prim_eq hx hy he h) (prim_xy hx hy)

theorem prim_yz : Γ ⊢[PRAAx] gcd (quo y (gcd x y)) (quo z (gcd x y)) ≐ one := by
  have hgd := gcd_dvd' (b := y) hx
  have hy' := pos_of_eq_mul hy (eq_of_dvd' (gcd_pos (B := y) hx) (Prf.andE₂ hgd))
  exact coprime_third hy' (quo_pos hx (Prf.andE₁ hgd)) he ((add_comm _ _).eqTrans (prim_eq hx hy he h))
    (gcd_comm_one hy' (prim_xy hx hy))

/-- The reduced right-hand coordinate does not increase. -/
theorem prim_le : Γ ⊢[PRAAx] le (quo z (gcd x y)) z := by
  have hg := gcd_pos (B := y) hx
  have ez := eq_of_dvd' hg (prim_dvd hx hy he h)
  have zq := pos_of_eq_mul (z_pos hx hy he h) ez
  exact dvd_le' zq (dvd_of_eq' zq (w := gcd x y) (ez.eqTrans (mul_comm _ _))) (z_pos hx hy he h)

end Fermat

/-! ## The quartic `x⁴ + y⁴ = z²` -/

section Quartic

variable {x y z : PTm n} (hx : Γ ⊢[PRAAx] x ≐ succ (pred x)) (hy : Γ ⊢[PRAAx] y ≐ succ (pred y))
  (hz : Γ ⊢[PRAAx] z ≐ succ (pred z)) (h : Γ ⊢[PRAAx] q4 x + q4 y ≐ z * z)
include hx hy hz h

omit hy in
/-- `d² ∣ z` for `d = gcd(x, y)`. -/
theorem quartic_dvd : Γ ⊢[PRAAx] dvd (gcd x y * gcd x y) z := by
  have hg := gcd_pos (B := y) hx
  have hgd := gcd_dvd' (b := y) hx
  have ex := eq_of_dvd' hg (Prf.andE₁ hgd); have ey := eq_of_dvd' hg (Prf.andE₂ hgd)
  have hgg := pos_mul hg hg
  refine dvd_of_sq_dvd_sq hgg hz (dvd_of_eq' (pos_mul hgg hgg)
    (w := q4 (quo x (gcd x y)) + q4 (quo y (gcd x y))) ?_)
  have a := natEq ex; have b := natEq ey; have c := natEq h
  apply deriveNat; simp only [q4]; ipra_simps
  linear_combination -c + (𝔞 x ^ 3 + 𝔞 x ^ 2 * (𝔞 (gcd x y) * 𝔞 (quo x (gcd x y))) +
      𝔞 x * (𝔞 (gcd x y) * 𝔞 (quo x (gcd x y))) ^ 2 + (𝔞 (gcd x y) * 𝔞 (quo x (gcd x y))) ^ 3) * a +
    (𝔞 y ^ 3 + 𝔞 y ^ 2 * (𝔞 (gcd x y) * 𝔞 (quo y (gcd x y))) +
      𝔞 y * (𝔞 (gcd x y) * 𝔞 (quo y (gcd x y))) ^ 2 + (𝔞 (gcd x y) * 𝔞 (quo y (gcd x y))) ^ 3) * b

/-- The reduced quartic `x'⁴ + y'⁴ = (z/d²)²`, with `gcd(x', y') = 1` by `prim_xy`. -/
theorem quartic_eq : Γ ⊢[PRAAx] q4 (quo x (gcd x y)) + q4 (quo y (gcd x y)) ≐
    quo z (gcd x y * gcd x y) * quo z (gcd x y * gcd x y) := by
  have hg := gcd_pos (B := y) hx
  have hgd := gcd_dvd' (b := y) hx
  have hgg := pos_mul hg hg
  have ex := eq_of_dvd' hg (Prf.andE₁ hgd); have ey := eq_of_dvd' hg (Prf.andE₂ hgd)
  have ez := eq_of_dvd' hgg (quartic_dvd hx hz h)
  refine mul_cancel (pos_mul hgg hgg) ?_
  have a := natEq ex; have b := natEq ey; have c := natEq ez; have d := natEq h
  apply deriveNat; simp only [q4]; ipra_simps
  linear_combination d - (𝔞 x ^ 3 + 𝔞 x ^ 2 * (𝔞 (gcd x y) * 𝔞 (quo x (gcd x y))) +
      𝔞 x * (𝔞 (gcd x y) * 𝔞 (quo x (gcd x y))) ^ 2 + (𝔞 (gcd x y) * 𝔞 (quo x (gcd x y))) ^ 3) * a -
    (𝔞 y ^ 3 + 𝔞 y ^ 2 * (𝔞 (gcd x y) * 𝔞 (quo y (gcd x y))) +
      𝔞 y * (𝔞 (gcd x y) * 𝔞 (quo y (gcd x y))) ^ 2 + (𝔞 (gcd x y) * 𝔞 (quo y (gcd x y))) ^ 3) * b
    + (𝔞 z + 𝔞 (gcd x y) * 𝔞 (gcd x y) * 𝔞 (quo z (gcd x y * gcd x y))) * c

end Quartic

end LeanProofs.IPRA.DiophantineNumberTheory.PrimitiveReduction
