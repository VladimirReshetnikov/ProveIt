import IPRADerivations.DiophantineNumberTheory.DescentTools

/-!
# All integer right triangles are multiples of primitive ones

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/diophantine.tex`, Corollary
`dio:all-triples`: every positive integer right triangle is a positive integer multiple of exactly one primitive
triple; the scale is the gcd of the two legs.

For positive `a, b, c` with `a² + b² = c²`, `g = gcd(a, b)`, `A = a/g`, `B = b/g`, `C = c/g`:

* **`triple_normalize`**: `a = g A`, `b = g B`, `c = g C`, `A² + B² = C²` and `gcd(A, B) = 1`
  (`g² ∣ c²` gives `g ∣ c` by `DescentTools.sq_dvd_tool`);
* `triple_scale`: conversely scaling preserves the equation;
* **`scale_unique`**: if `a = k A'`, `b = k B'` with `k ≥ 1` and `gcd(A', B') = 1`, then `k = gcd(a, b)`.

The primitive triples themselves are parametrized in `DescentTools` (`pyth_param`, `pyth_unique`).
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.PythagoreanScaling

open_ipra exports
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.DescentTools (sq_dvd_tool)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Existence -/

theorem sq_alg {a b c g A B : PTm n} (hE : Γ ⊢[PRAAx] a * a + b * b ≐ c * c) (eA : Γ ⊢[PRAAx] a ≐ g * A)
    (eB : Γ ⊢[PRAAx] b ≐ g * B) : Γ ⊢[PRAAx] c * c ≐ (g * g) * (A * A + B * B) := by
  ipra_lc -natEq hE + (𝔞 a + 𝔞 g * 𝔞 A) * natEq eA + (𝔞 b + 𝔞 g * 𝔞 B) * natEq eB

theorem pyth_alg {a b c g A B C : PTm n} (hE : Γ ⊢[PRAAx] a * a + b * b ≐ c * c)
    (eA : Γ ⊢[PRAAx] a ≐ g * A) (eB : Γ ⊢[PRAAx] b ≐ g * B) (eC : Γ ⊢[PRAAx] c ≐ g * C) :
    Γ ⊢[PRAAx] (g * g) * (A * A + B * B) ≐ (g * g) * (C * C) := by
  ipra_lc natEq hE - (𝔞 a + 𝔞 g * 𝔞 A) * natEq eA - (𝔞 b + 𝔞 g * 𝔞 B) * natEq eB + (𝔞 c + 𝔞 g * 𝔞 C) * natEq eC

/-- **Every right triangle is `gcd(a, b)` times a primitive one**. -/
theorem triple_normalize {a b c : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (hE : Γ ⊢[PRAAx] a * a + b * b ≐ c * c) :
    Γ ⊢[PRAAx]
      (a ≐ gcd a b * quo a (gcd a b)) ⋏ ((b ≐ gcd a b * quo b (gcd a b)) ⋏
      ((c ≐ gcd a b * quo c (gcd a b)) ⋏
      ((quo a (gcd a b) * quo a (gcd a b) + quo b (gcd a b) * quo b (gcd a b) ≐
          quo c (gcd a b) * quo c (gcd a b)) ⋏
      (gcd (quo a (gcd a b)) (quo b (gcd a b)) ≐ one)))) := by
  have hg := gcd_pos (B := b) ha
  have hgg := pos_mul hg hg
  have hd := gcd_dvd' (b := b) ha
  have eA := eq_of_dvd' hg (Prf.andE₁ hd)
  have eB := eq_of_dvd' hg (Prf.andE₂ hd)
  have cop := coprime_quotients (c := b) ha
  have hgc : Γ ⊢[PRAAx] dvd (gcd a b) c := sq_dvd_tool hg (dvd_of_eq' hgg (sq_alg hE eA eB))
  have eC := eq_of_dvd' hg hgc
  have pyth := mul_cancel hgg (pyth_alg hE eA eB eC)
  exact .andI eA (.andI eB (.andI eC (.andI pyth cop)))

/-- Scaling preserves the equation. -/
theorem triple_scale {g A B C : PTm n} (h : Γ ⊢[PRAAx] A * A + B * B ≐ C * C) :
    Γ ⊢[PRAAx] (g * A) * (g * A) + (g * B) * (g * B) ≐ (g * C) * (g * C) := by
  ipra_lc 𝔞 g * 𝔞 g * natEq h

/-! ## The scale is the gcd -/

theorem cancel_alg {a k A g h q : PTm n} (ea : Γ ⊢[PRAAx] a ≐ k * A) (e1 : Γ ⊢[PRAAx] a ≐ g * q)
    (eg : Γ ⊢[PRAAx] g ≐ k * h) : Γ ⊢[PRAAx] k * A ≐ k * (h * q) := by
  ipra_lc -natEq ea + natEq e1 + 𝔞 q * natEq eg

theorem one_alg {g k h : PTm n} (eg : Γ ⊢[PRAAx] g ≐ k * h) (h1 : Γ ⊢[PRAAx] h ≐ one) :
    Γ ⊢[PRAAx] k ≐ g := by
  ipra_lc -natEq eg - 𝔞 k * natEq h1

/-- **The scale is forced**: `a = k A'`, `b = k B'`, `gcd(A', B') = 1` give `k = gcd(a, b)`. -/
theorem scale_unique {a b k A B : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (pred k))
    (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (ea : Γ ⊢[PRAAx] a ≐ k * A) (eb : Γ ⊢[PRAAx] b ≐ k * B)
    (hc : Γ ⊢[PRAAx] gcd A B ≐ one) : Γ ⊢[PRAAx] k ≐ gcd a b := by
  have hg := gcd_pos (B := b) ha
  have hd := gcd_dvd' (b := b) ha
  have e1 := eq_of_dvd' hg (Prf.andE₁ hd)
  have e2 := eq_of_dvd' hg (Prf.andE₂ hd)
  have dk : Γ ⊢[PRAAx] dvd k (gcd a b) := gcd_greatest' hk (dvd_of_eq' hk ea) (dvd_of_eq' hk eb)
  have eg := eq_of_dvd' hk dk
  have hh := pos_of_eq_mul hg eg
  have dA : Γ ⊢[PRAAx] dvd (quo (gcd a b) k) A := dvd_of_eq' hh (mul_cancel hk (cancel_alg ea e1 eg))
  have dB : Γ ⊢[PRAAx] dvd (quo (gcd a b) k) B := dvd_of_eq' hh (mul_cancel hk (cancel_alg eb e2 eg))
  have d1 : Γ ⊢[PRAAx] dvd (quo (gcd a b) k) one := dvd_congr hc (gcd_greatest' hh dA dB)
  exact one_alg eg (eq_one_of_dvd_one hh d1)

end LeanProofs.IPRA.DiophantineNumberTheory.PythagoreanScaling
