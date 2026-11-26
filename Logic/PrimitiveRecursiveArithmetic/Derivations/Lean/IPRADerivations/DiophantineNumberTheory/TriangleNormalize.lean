import IPRADerivations.DiophantineNumberTheory.DescentTools
import IPRADerivations.Core.Header

/-!
# Normalization of square-area triangles

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Lemma `lem:triangle-normalize`.
From positive `a, b, c, s` with `a² + b² = c²` and `a b = 2 s²`, the computed
`g = gcd(a, b)`, `A = a/g`, `B = b/g`, `C = c/g`, `S = s/g` are positive, satisfy the same two
equations, `gcd(A, B) = 1`, and `C ≤ c`:

* `g² ∣ a² + b² = c²`, so `g ∣ c` (`DescentTools.sq_dvd_tool`) and `A² + B² = C²` after cancelling `g²`;
* `gcd(A, B) = 1` (`Coprime.coprime_quotients`), so one of `A, B` is even (`DescentTools.leg_parity`);
* if `A = 2A'` then `s² = g² A' B`, and symmetrically, so `g ∣ s` and `A B = 2 S²`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.TriangleNormalize

open_ipra
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Foundations.ChineseRemainder (gcd_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.Pythagoras (two_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.DescentTools (sq_dvd_tool leg_parity)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `lem:triangle-normalize`. -/
theorem triangle_normalize {a b c s : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) (hc : Γ ⊢[PRAAx] c ≐ succ (pred c)) (hs : Γ ⊢[PRAAx] s ≐ succ (pred s))
    (hE : Γ ⊢[PRAAx] a * a + b * b ≐ c * c) (hR : Γ ⊢[PRAAx] a * b ≐ two * (s * s)) :
    Γ ⊢[PRAAx]
      (quo a (gcd a b) ≐ succ (pred (quo a (gcd a b)))) ⋏ ((quo b (gcd a b) ≐ succ (pred (quo b (gcd a b)))) ⋏
      ((quo c (gcd a b) ≐ succ (pred (quo c (gcd a b)))) ⋏ ((quo s (gcd a b) ≐ succ (pred (quo s (gcd a b)))) ⋏
      ((quo a (gcd a b) * quo a (gcd a b) + quo b (gcd a b) * quo b (gcd a b) ≐ quo c (gcd a b) * quo c (gcd a b)) ⋏
      ((quo a (gcd a b) * quo b (gcd a b) ≐ two * (quo s (gcd a b) * quo s (gcd a b))) ⋏
      ((gcd (quo a (gcd a b)) (quo b (gcd a b)) ≐ one) ⋏ le (quo c (gcd a b)) c)))))) := by
  have hg := gcd_pos (B := b) ha
  have hgg := pos_mul hg hg
  have hd := gcd_dvd' (b := b) ha
  have eA := eq_of_dvd' hg (Prf.andE₁ hd)
  have eB := eq_of_dvd' hg (Prf.andE₂ hd)
  have pA := pos_of_eq_mul ha eA
  have pB := pos_of_eq_mul hb eB
  have cop := coprime_quotients (c := b) ha
  -- `g ∣ c`.
  have hgc : Γ ⊢[PRAAx] dvd (gcd a b) c := by
    refine sq_dvd_tool hg (dvd_of_eq' hgg (w := quo a (gcd a b) * quo a (gcd a b) + quo b (gcd a b) * quo b (gcd a b)) ?_)
    have x := natEq hE; have y := natEq eA; have z := natEq eB
    apply deriveNat; ipra_simps
    linear_combination -x + (𝔞 a + 𝔞 (gcd a b) * 𝔞 (quo a (gcd a b))) * y +
      (𝔞 b + 𝔞 (gcd a b) * 𝔞 (quo b (gcd a b))) * z
  have eC := eq_of_dvd' hg hgc
  have pC := pos_of_eq_mul hc eC
  have pyth : Γ ⊢[PRAAx] quo a (gcd a b) * quo a (gcd a b) + quo b (gcd a b) * quo b (gcd a b) ≐
      quo c (gcd a b) * quo c (gcd a b) := by
    refine mul_cancel hgg ?_
    have x := natEq hE; have y := natEq eA; have z := natEq eB; have w := natEq eC
    apply deriveNat; ipra_simps
    linear_combination x - (𝔞 a + 𝔞 (gcd a b) * 𝔞 (quo a (gcd a b))) * y -
      (𝔞 b + 𝔞 (gcd a b) * 𝔞 (quo b (gcd a b))) * z + (𝔞 c + 𝔞 (gcd a b) * 𝔞 (quo c (gcd a b))) * w
  -- `g ∣ s`, using the even leg.
  have hgs : Γ ⊢[PRAAx] dvd (gcd a b) s := by
    refine .orE (leg_parity cop pyth) ?_ ?_
    · let C₁ := ((quo a (gcd a b) ≐ two * half (quo a (gcd a b))) ⋏
        (quo b (gcd a b) ≐ two * half (quo b (gcd a b)) + one)) :: Γ
      have ev := natEq (Prf.andE₁ (Prf.hyp0 : C₁ ⊢[PRAAx] _))
      refine sq_dvd_tool hg.wk (dvd_of_eq' hgg.wk (w := half (quo a (gcd a b)) * quo b (gcd a b)) ?_)
      refine mul_cancel two_pos ?_
      have x := natEq (hR.wk : C₁ ⊢[PRAAx] _); have y := natEq (eA.wk : C₁ ⊢[PRAAx] _)
      have z := natEq (eB.wk : C₁ ⊢[PRAAx] _)
      apply deriveNat; ipra_simps
      linear_combination -x + 𝔞 b * y + 𝔞 (gcd a b) * 𝔞 (quo a (gcd a b)) * z +
        𝔞 (gcd a b) * 𝔞 (gcd a b) * 𝔞 (quo b (gcd a b)) * ev
    · let C₁ := ((quo a (gcd a b) ≐ two * half (quo a (gcd a b)) + one) ⋏
        (quo b (gcd a b) ≐ two * half (quo b (gcd a b)))) :: Γ
      have ev := natEq (Prf.andE₂ (Prf.hyp0 : C₁ ⊢[PRAAx] _))
      refine sq_dvd_tool hg.wk (dvd_of_eq' hgg.wk (w := quo a (gcd a b) * half (quo b (gcd a b))) ?_)
      refine mul_cancel two_pos ?_
      have x := natEq (hR.wk : C₁ ⊢[PRAAx] _); have y := natEq (eA.wk : C₁ ⊢[PRAAx] _)
      have z := natEq (eB.wk : C₁ ⊢[PRAAx] _)
      apply deriveNat; ipra_simps
      linear_combination -x + 𝔞 b * y + 𝔞 (gcd a b) * 𝔞 (quo a (gcd a b)) * z +
        𝔞 (gcd a b) * 𝔞 (gcd a b) * 𝔞 (quo a (gcd a b)) * ev
  have eS := eq_of_dvd' hg hgs
  have pS := pos_of_eq_mul hs eS
  have area : Γ ⊢[PRAAx] quo a (gcd a b) * quo b (gcd a b) ≐ two * (quo s (gcd a b) * quo s (gcd a b)) := by
    refine mul_cancel hgg ?_
    have x := natEq hR; have y := natEq eA; have z := natEq eB; have w := natEq eS
    apply deriveNat; ipra_simps
    linear_combination x - 𝔞 b * y - 𝔞 (gcd a b) * 𝔞 (quo a (gcd a b)) * z +
      2 * (𝔞 s + 𝔞 (gcd a b) * 𝔞 (quo s (gcd a b))) * w
  have small : Γ ⊢[PRAAx] le (quo c (gcd a b)) c := by
    refine le_of_eq_add (d := pred (gcd a b) * quo c (gcd a b)) ?_
    have w := natEq eC; have k := natEq hg
    apply deriveNat; ipra_simps
    linear_combination w + 𝔞 (quo c (gcd a b)) * k
  exact .andI pA (.andI pB (.andI pC (.andI pS (.andI pyth (.andI area (.andI cop small))))))

end LeanProofs.IPRA.DiophantineNumberTheory.TriangleNormalize
