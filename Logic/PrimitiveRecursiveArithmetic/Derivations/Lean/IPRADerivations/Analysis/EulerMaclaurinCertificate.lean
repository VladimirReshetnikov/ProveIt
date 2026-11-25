import IPRADerivations.DiophantineNumberTheory.RungeProduct
import IPRADerivations.AnalyticNumberTheory.PhiLower
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.CertificateTactics

/-!
# The rational Euler–Maclaurin certificate

Packet: `analysis/calculus_ipra`, `report.tex`, Section "A fully rational Euler–Maclaurin certificate":
with sampled derivative data `f̂_j`, Bernoulli polynomials `P_j`, fine step `h`, the quadratures `Q_j`, the
boundary terms `b_1` (trapezoidal sum) and `b_j = c_j (f̂_{j−1}(b) − f̂_{j−1}(a))`, and the defects
`E_j = b_j − Q_{j−1} − Q_j`:

* `local_defect` (`eq:localdefect`): with `ΔP = P(t + h) − P(t)` and `ΔF = F(t + h) − F(t)`,
  `Δ(P F) − h (P f' + p F) = P (ΔF − h f') + F (ΔP − h p) + ΔP ΔF`, an identity of signed integer terms
  (numerators over a common denominator);
* `defect_bound`: the three products are bounded by the products of the bounds of their factors, so the
  absolute value of the defect is at most `C U + K V + W₁ W₂`;
* `constant_compare`: the comparison of the constants,
  `19 C + 16 (M + 1) r² C + 16 (M + 3) r C ≤ 16 C (M + 1) (r + 1)²` for `M ≥ 1`, which is the paper's
  `(19/16) C + (M + 1) D₂ + (M + 3) D₁ ≤ D` with `C = 2^r`, `D₁ = r 2^r`, `D₂ = r² 2^r`,
  `D = 2^r (M + 1)(r + 1)²` after multiplication by 16 (the remainder is `C (16 r (M − 1) + 16 (M − 1) + 13)`);
* `em_identity` (`eq:finiteEMidentity`): for every order `r = s + 1`,
  `b_1 = Q_0 + ∑_{j=2}^r (−1)^j b_j + (−1)^{r+1} Q_r + ∑_{j=1}^r (−1)^{j+1} E_j`, the interior quadratures
  cancelling;
* `em_bound` (`eq:finiteEMbound`): if every `|E_j| ≤ B`, then
  `|b_1 − Q_0 − ∑_{j=2}^r (−1)^j b_j − (−1)^{r+1} Q_r| ≤ r B`.

The order `r` is a fixed numeral (a meta-level natural), as in the paper's schema "for a fixed order";
`Q_j`, `b_j` are arbitrary signed integer terms. The telescoping of the fine cells, the bounds on the
Bernoulli polynomials and the passage to the represented integrals are not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.EulerMaclaurinCertificate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.RungeProduct (za D_congr D_neg D_add_le D_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## One fine cell -/

/-- `eq:localdefect`: the product rule defect of one fine cell. -/
theorem local_defect (P₀ P₁ F₀ F₁ p g h : ZT n) :
    Γ ⊢[PRAAx] ZT.eq ((P₁ * F₁ - P₀ * F₀) - h * (P₀ * g + p * F₀))
      (P₀ * ((F₁ - F₀) - h * g) + F₀ * ((P₁ - P₀) - h * p) + (P₁ - P₀) * (F₁ - F₀)) := by
  ipra_lc

/-- The absolute value of `x u + y v + z w` is at most `C U + K V + W₁ W₂` when the factors are. -/
theorem three_products {x u y v z w : ZT n} {C U K V W₁ W₂ : PTm n}
    (hx : Γ ⊢[PRAAx] le (za x) C) (hu : Γ ⊢[PRAAx] le (za u) U)
    (hy : Γ ⊢[PRAAx] le (za y) K) (hv : Γ ⊢[PRAAx] le (za v) V)
    (hz : Γ ⊢[PRAAx] le (za z) W₁) (hw : Γ ⊢[PRAAx] le (za w) W₂) :
    Γ ⊢[PRAAx] le (za (x * u + y * v + z * w)) (C * U + K * V + W₁ * W₂) := by
  have h₁ := D_add_le (Γ := Γ) (x * u + y * v) (z * w)
  have h₂ := D_add_le (Γ := Γ) (x * u) (y * v)
  have m₁ := natEq (D_mul (Γ := Γ) x u)
  have m₂ := natEq (D_mul (Γ := Γ) y v)
  have m₃ := natEq (D_mul (Γ := Γ) z w)
  have b₁ := le_mul_mono hx hu
  have b₂ := le_mul_mono hy hv
  have b₃ := le_mul_mono hz hw
  ipra_le sl h₁ + sl h₂ + sl b₁ + sl b₂ + sl b₃ using linear_combination -m₁ - m₂ - m₃

/-- The defect of one fine cell is at most `C U + K V + W₁ W₂` in absolute value. -/
theorem defect_bound {P₀ P₁ F₀ F₁ p g h : ZT n} {C U K V W₁ W₂ : PTm n}
    (hP : Γ ⊢[PRAAx] le (za P₀) C) (hu : Γ ⊢[PRAAx] le (za ((F₁ - F₀) - h * g)) U)
    (hF : Γ ⊢[PRAAx] le (za F₀) K) (hv : Γ ⊢[PRAAx] le (za ((P₁ - P₀) - h * p)) V)
    (hΔP : Γ ⊢[PRAAx] le (za (P₁ - P₀)) W₁) (hΔF : Γ ⊢[PRAAx] le (za (F₁ - F₀)) W₂) :
    Γ ⊢[PRAAx] le (za ((P₁ * F₁ - P₀ * F₀) - h * (P₀ * g + p * F₀))) (C * U + K * V + W₁ * W₂) :=
  le_congr (D_congr (local_defect P₀ P₁ F₀ F₁ p g h)).eqSymm (.eqRefl _)
    (three_products hP hu hF hv hΔP hΔF)

/-- The comparison of the constants, multiplied by 16: for `M ≥ 1`,
`19 C + 16 (M + 1) r² C + 16 (M + 3) r C ≤ 16 C (M + 1) (r + 1)²`. -/
theorem constant_compare (C M r : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] le (num 19 * C + num 16 * (M + one) * (r * r) * C + num 16 * (M + num 3) * r * C)
      (num 16 * C * (M + one) * (succ r * succ r)) := by
  ipra_le 𝔟 C * (16 * 𝔟 r * sl hM + 16 * sl hM + 13)

/-! ## The alternating telescoping over the orders -/

/-- `zs f k = ∑_{i<k} f i`, a signed sum of fixed length `k`. -/
def zs (f : ℕ → ZT n) : ℕ → ZT n
  | 0 => ZT.ofNat zero
  | k + 1 => zs f k + f k

/-- `alt j x = (−1)^j x`. -/
def alt : ℕ → ZT n → ZT n
  | 0, x => x
  | j + 1, x => -(alt j x)

theorem toZ_zs (f : ℕ → ZT n) (k : ℕ) :
    ZT.toZ Γ (zs f k) = ∑ i ∈ Finset.range k, ZT.toZ Γ (f i) := by
  induction k with
  | zero => simp [zs, ZT.toZ_ofNat, Q.mk_zero]
  | succ k ih => rw [zs, ZT.toZ_add, ih, Finset.sum_range_succ]

theorem toZ_alt (j : ℕ) (x : ZT n) : ZT.toZ Γ (alt j x) = (-1) ^ j * ZT.toZ Γ x := by
  induction j with
  | zero => simp [alt]
  | succ j ih => rw [alt, ZT.toZ_neg, ih]; ring

/-- The ring identity behind `eq:finiteEMidentity`. -/
theorem em_ring {R : Type*} [CommRing R] (Q b : ℕ → R) (s : ℕ) :
    b 1 = Q 0 + ∑ i ∈ Finset.range s, (-1) ^ (i + 2) * b (i + 2) + (-1) ^ (s + 2) * Q (s + 1) +
      ∑ i ∈ Finset.range (s + 1), (-1) ^ (i + 2) * (b (i + 1) - Q i - Q (i + 1)) := by
  induction s with
  | zero => simp only [Finset.sum_range_succ, Finset.sum_range_zero]; ring
  | succ s ih =>
    rw [Finset.sum_range_succ (fun i => (-1) ^ (i + 2) * b (i + 2)) s,
      Finset.sum_range_succ (fun i => (-1) ^ (i + 2) * (b (i + 1) - Q i - Q (i + 1))) (s + 1)]
    linear_combination ih

/-- The main part `Q_0 + ∑_{j=2}^r (−1)^j b_j + (−1)^{r+1} Q_r` for the order `r = s + 1`. -/
abbrev mainPart (Q b : ℕ → ZT n) (s : ℕ) : ZT n :=
  Q 0 + zs (fun i => alt (i + 2) (b (i + 2))) s + alt (s + 2) (Q (s + 1))

/-- The signed defects `(−1)^{j+1} E_j`, `j = i + 1`. -/
abbrev sE (Q b : ℕ → ZT n) (i : ℕ) : ZT n := alt (i + 2) (b (i + 1) - Q i - Q (i + 1))

/-- `eq:finiteEMidentity`, for the order `r = s + 1`. -/
theorem em_identity (Q b : ℕ → ZT n) (s : ℕ) :
    Γ ⊢[PRAAx] ZT.eq (b 1) (mainPart Q b s + zs (sE Q b) (s + 1)) := by
  apply ZT.derive
  simp only [mainPart, sE, ZT.toZ_add, ZT.toZ_sub, toZ_zs, toZ_alt]
  exact em_ring (fun i => ZT.toZ Γ (Q i)) (fun i => ZT.toZ Γ (b i)) s

theorem za_alt (j : ℕ) (x : ZT n) : Γ ⊢[PRAAx] za (alt j x) ≐ za x := by
  induction j with
  | zero => exact .eqRefl _
  | succ j ih => exact (D_neg (alt j x)).eqTrans ih

/-- A signed sum of `k` terms of absolute value at most `B` is at most `k B` in absolute value. -/
theorem zs_bound (f : ℕ → ZT n) (B : PTm n) (k : ℕ)
    (hf : ∀ i, i < k → (Γ ⊢[PRAAx] le (za (f i)) B)) :
    Γ ⊢[PRAAx] le (za (zs f k)) (num k * B) := by
  induction k with
  | zero =>
    have m := natEq (monus_self (Γ := Γ) (zero : PTm n))
    show Γ ⊢[PRAAx] le (monus zero zero + monus zero zero) (num 0 * B)
    ipra_le 0 using linear_combination (-2 : Groth (Q Γ)) * m
  | succ k ih =>
    have ih' := ih (fun i hi => hf i (Nat.lt_succ_of_lt hi))
    have hk := hf k (Nat.lt_succ_self k)
    have h₁ := D_add_le (Γ := Γ) (zs f k) (f k)
    show Γ ⊢[PRAAx] le (za (zs f k + f k)) (num (k + 1) * B)
    ipra_le sl h₁ + sl ih' + sl hk using push_cast; ring

/-- `eq:finiteEMbound`: if every `|E_j| ≤ B` for `1 ≤ j ≤ r = s + 1`, the deviation of `b_1` from the main
part is at most `r B`. -/
theorem em_bound (Q b : ℕ → ZT n) (B : PTm n) (s : ℕ)
    (hE : ∀ i, i < s + 1 → (Γ ⊢[PRAAx] le (za (b (i + 1) - Q i - Q (i + 1))) B)) :
    Γ ⊢[PRAAx] le (za (b 1 - mainPart Q b s)) (num (s + 1) * B) := by
  have e : Γ ⊢[PRAAx] ZT.eq (b 1 - mainPart Q b s) (zs (sE Q b) (s + 1)) := by
    apply ZT.derive
    have i := ZT.toZ_eq (em_identity (Γ := Γ) Q b s)
    rw [ZT.toZ_add] at i
    rw [ZT.toZ_sub, i, add_sub_cancel_left]
  refine le_congr (D_congr e).eqSymm (.eqRefl _) (zs_bound _ B (s + 1) fun i hi => ?_)
  exact le_congr (za_alt _ _).eqSymm (.eqRefl _) (hE i hi)

end LeanProofs.IPRA.Analysis.EulerMaclaurinCertificate
