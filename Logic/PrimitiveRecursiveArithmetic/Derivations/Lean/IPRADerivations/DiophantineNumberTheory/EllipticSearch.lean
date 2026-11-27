import IPRADerivations.DiophantineNumberTheory.ConicNonzero
import IPRADerivations.DiophantineNumberTheory.DirichletReal

/-!
# The bounded search for rational points of small height on an elliptic curve

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Theorem `thm:elliptic-search`: the points of
`E_{A,B} : y² = x³ + Ax + B` with `Ht(x) ≤ T` are `(a/d², ±b₀/d³)` for `1 ≤ d ≤ ⌊√T⌋`, `|a| ≤ T`, `gcd(a, d) = 1`,
`W = a³ + A a d⁴ + B d⁶ = b₀²`.

* `es_coprime`: "Coprimality of `a, d` ... also forces `gcd(b₀, d) = 1`: a common [divisor] would divide `a³` after
  reducing `eq:elliptic-integral` modulo [it], and hence would divide `a`, a contradiction." A common divisor
  `g ≥ 1` of `b` and `d` with `gcd(d, a) = 1` and `a³ + Y = Z` where `g` divides `Y`, `Z` (the remaining terms of
  `b² = a³ + A a d⁴ + B d⁶`, sorted by sign) is `1`;
* `es_bound`: "`0 ≤ W ≤ (1 + |A| + |B|) T³`": for `|a| ≤ T`, `d² ≤ T`, `|A| ≤ A'`, `|B| ≤ B'`, the absolute value of
  `W` is at most `(1 + A' + B') T³`;
* `es_sqrt_bound`: "its square root is at most `CT²`, since `CT³ ≤ C²T⁴`" (`b² ≤ CT³` gives `b ≤ CT²`);
* `es_infinity`: "At infinity, `Z = 0` forces `X = 0`": `Y²Z = X³ + AXZ² + BZ³` with `Z = 0` gives `X = 0`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.EllipticSearch

open_ipra exports
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
  (coprime_dvd_left coprime_mul eq_one_of_coprime_dvd dvd_add' dvd_sub' dvd_mul' le_of_sq_le)
open LeanProofs.IPRA.DiophantineNumberTheory.ConicNonzero (zt_dec zt_sq_zero)
open LeanProofs.IPRA.Analysis.PolynomialRemainder (AbsLe abs_add abs_mul abs_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- A common divisor of `b` and `d` is `1` when `gcd(d, a) = 1` and it divides `a³` through the curve equation. -/
theorem es_coprime {g a d b Y Z : PTm n} (hg : Γ ⊢[PRAAx] g ≐ succ (pred g)) (hgd : Γ ⊢[PRAAx] dvd g d)
    (hcop : Γ ⊢[PRAAx] gcd d a ≐ one) (heq : Γ ⊢[PRAAx] a * a * a + Y ≐ Z)
    (hY : Γ ⊢[PRAAx] dvd g Y) (hZ : Γ ⊢[PRAAx] dvd g Z) : Γ ⊢[PRAAx] g ≐ one := by
  have h1 := coprime_dvd_left hg hgd hcop
  have h3 := coprime_mul hg (coprime_mul hg h1 h1) h1
  have ha3 : Γ ⊢[PRAAx] dvd g (a * a * a) := dvd_sub' hg (dvd_congr heq.eqSymm hZ) hY
  exact eq_one_of_coprime_dvd hg h3 ha3

/-- The square-root search bound: `|W| ≤ (1 + A' + B') T³`. -/
theorem es_bound {a A B : ZT n} {d T A' B' : PTm n} (ha : Γ ⊢[PRAAx] AbsLe a T) (hA : Γ ⊢[PRAAx] AbsLe A A')
    (hB : Γ ⊢[PRAAx] AbsLe B B') (hd : Γ ⊢[PRAAx] le (d * d) T) :
    Γ ⊢[PRAAx] AbsLe (a * a * a + A * a * ((ZT.ofNat d * ZT.ofNat d) * (ZT.ofNat d * ZT.ofNat d)) +
        B * ((ZT.ofNat d * ZT.ofNat d) * (ZT.ofNat d * ZT.ofNat d) * (ZT.ofNat d * ZT.ofNat d)))
      ((one + A' + B') * (T * T * T)) := by
  have hD : Γ ⊢[PRAAx] AbsLe (ZT.ofNat d * ZT.ofNat d) (d * d) := abs_mul (abs_nat d) (abs_nat d)
  have h4 : Γ ⊢[PRAAx] le (d * d * (d * d)) (T * T) := by ipra_le (𝔟 T + 𝔟 (d * d)) * sl hd
  have h6 : Γ ⊢[PRAAx] le (d * d * (d * d) * (d * d)) (T * T * T) := by
    ipra_le (𝔟 T * 𝔟 T + 𝔟 T * 𝔟 (d * d) + 𝔟 (d * d) * 𝔟 (d * d)) * sl hd
  have t1 := abs_mul (abs_mul ha ha) ha
  have t2 := abs_mul (abs_mul hA ha) (abs_mono h4 (abs_mul hD hD))
  have t3 := abs_mul hB (abs_mono h6 (abs_mul (abs_mul hD hD) hD))
  refine abs_mono ?_ (abs_add (abs_add t1 t2) t3)
  ipra_le 0

/-- `b² ≤ C T³` with `C, T ≥ 1` gives `b ≤ C T²`. -/
theorem es_sqrt_bound {b C T : PTm n} (hC : Γ ⊢[PRAAx] le one C) (hT : Γ ⊢[PRAAx] le one T)
    (hb : Γ ⊢[PRAAx] le (b * b) (C * (T * T * T))) : Γ ⊢[PRAAx] le b (C * (T * T)) := by
  refine le_of_sq_le ?_
  ipra_le sl hb + 𝔟 C * 𝔟 T ^ 3 * (sl hC + sl hT + sl hC * sl hT)

/-- At infinity: `Y²Z = X³ + AXZ² + BZ³` and `Z = 0` give `X = 0`. -/
theorem es_infinity {X Y Z A B : ZT n}
    (h : Γ ⊢[PRAAx] ZT.eq (Y * Y * Z) (X * X * X + A * X * Z * Z + B * Z * Z * Z))
    (hz : Γ ⊢[PRAAx] ZT.eq Z (ZT.natLit 0)) : Γ ⊢[PRAAx] ZT.eq X (ZT.natLit 0) := by
  have e := ZT.toZ_eq h
  have ez := ZT.toZ_eq hz
  have h3 : Γ ⊢[PRAAx] ZT.eq (X * (X * X)) (ZT.natLit 0) := by
    refine ZT.derive ?_
    simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit] at e ez ⊢
    rw [ez] at e
    push_cast at e ⊢
    linear_combination -e
  exact .orE (zt_dec X) Prf.hyp0 (zt_sq_zero (zt_no_zero_div Prf.hyp0 h3.wk))

end LeanProofs.IPRA.DiophantineNumberTheory.EllipticSearch
