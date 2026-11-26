import IPRADerivations.DiophantineNumberTheory.Coprime
import IPRADerivations.Foundations.ChineseRemainder
import IPRADerivations.Combinatorics.LegendreDigits
import IPRADerivations.Combinatorics.BinomialIdentities
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas
import IPRADerivations.Core.Header

/-!
# Two pairs of equal norm give a Pell solution

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/diophantine.tex`, the collision step of
`dio:pell-existence`: "A collision among the `K + 1` pairs gives `i < j` with common nonzero norm `m` and matching
residues modulo `|m|`. Define `x = (p_i p_j − D q_i q_j)/m`, `y = (p_i q_j − p_j q_i)/m` … both quotients are
integers, also for `m < 0`. Expansion gives `(p_i p_j − D q_i q_j)² − D(p_i q_j − p_j q_i)² = m²`, so their norm is
`1`. Positivity needs checking, especially for negative common norm."

With natural numbers the sign of the common norm `m = ±a` (`a ≥ 1`) is a case:

* `m = a` (`p_k² = D q_k² + a`): `D q_i q_j ≤ p_i p_j` and `p_j q_i ≤ p_i q_j`; with `N₁ = p_i p_j − D q_i q_j` and
  `N₂ = p_i q_j − p_j q_i` (`collision_pos`);
* `m = −a` (`D q_k² = p_k² + a`): the opposite orders, `N₁ = D q_i q_j − p_i p_j`, `N₂ = p_j q_i − p_i q_j`
  (`collision_neg`).

In both cases `a ∣ N₁`, `a ∣ N₂` (an explicit ring certificate from `p_j ≡ p_i`, `q_j ≡ q_i (mod a)`),
`N₁² = D N₂² + a²` (Brahmagupta), so `x = N₁/a`, `y = N₂/a` satisfy `x² = D y² + 1`; `y ≥ 1` because `q_i < q_j`,
and `x ≤ N₁`, `y ≤ N₂`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.PellCollision

open_ipra
open LeanProofs.IPRA.Foundations.ChineseRemainder (rem_eq_of_eq)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (dm)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (le_of_sq_le eq_of_dvd' pos_of_eq_mul one_le_of_pos)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Common tools -/

/-- `N = a k₂ − a k₁` as a divisibility: `N + a k₁ = a k₂` gives `a ∣ N`. -/
theorem dvd_of_cert {a N k₁ k₂ : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (h : Γ ⊢[PRAAx] N + a * k₁ ≐ zero + a * k₂) :
    Γ ⊢[PRAAx] dvd a N :=
  (rem_eq_of_eq ha h).eqTrans (rem_zero a)

/-- From `N₁ = a x`, `N₂ = a y` and `N₁² = D N₂² + a²`: `x² = D y² + 1`. -/
theorem norm_one {a N₁ N₂ D x y : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (e1 : Γ ⊢[PRAAx] N₁ ≐ a * x)
    (e2 : Γ ⊢[PRAAx] N₂ ≐ a * y) (h : Γ ⊢[PRAAx] N₁ * N₁ ≐ D * (N₂ * N₂) + a * a) :
    Γ ⊢[PRAAx] x * x ≐ D * (y * y) + one := by
  have x1 := natEq e1; have x2 := natEq e2; have x3 := natEq h
  refine mul_cancel (pos_mul ha ha) ?_
  ipra_lc x3 - (𝔞 N₁ + 𝔞 a * 𝔞 x) * x1 + 𝔞 D * (𝔞 N₂ + 𝔞 a * 𝔞 y) * x2

/-- `y ≥ 1` once `N₂ = a y` is nonzero. -/
theorem y_pos {a N y : PTm n} (e : Γ ⊢[PRAAx] N ≐ a * y) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] le one y :=
  one_le_of_pos (pos_of_eq_mul hN e)

/-- `x ≤ N` when `N = a x`, `a ≥ 1`. -/
theorem le_of_mul {a N x : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (e : Γ ⊢[PRAAx] N ≐ a * x) :
    Γ ⊢[PRAAx] le x N := by
  have x1 := natEq e; have x2 := natEq ha
  ipra_le 𝔞 (pred a) * 𝔞 x with x1 + 𝔞 x * x2

alias monus_le' := Common.monus_le_self

/-- `q_i < q_j` and `a ≥ 1` contradict `a (q_j² − q_i²) = (u + w)(u − w)` with `u = w`. -/
theorem q_absurd {a qi qj W : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hlt : Γ ⊢[PRAAx] lt qi qj)
    (h : Γ ⊢[PRAAx] a * (qj * qj) ≐ a * (qi * qi) + W) (hW : Γ ⊢[PRAAx] W ≐ zero) : Γ ⊢[PRAAx] le one zero := by
  have x := natEq h; have y := natEq hW; have z := natEq ha
  ipra_le 2 * 𝔞 a * 𝔞 qi + 𝔞 (pred a) + 𝔞 a * (2 * sl hlt * (𝔞 qi + 1) + sl hlt * sl hlt) with
    -x - y + z

/-- The end of both sign cases: `a ∣ N₁`, `a ∣ N₂`, Brahmagupta's identity `N₁² = D N₂² + a²` and a relation
`a (q_j² − q_i²) = c N₂` (which excludes `N₂ = 0` when `q_i < q_j`) give `x = N₁/a`, `y = N₂/a` with
`x² = D y² + 1`, `y ≥ 1`, `x ≤ N₁` and `y ≤ N₂`. -/
theorem collision_end {D a qi qj c N₁ N₂ U₁ U₂ : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (hlt : Γ ⊢[PRAAx] lt qi qj) (d1 : Γ ⊢[PRAAx] dvd a N₁) (d2 : Γ ⊢[PRAAx] dvd a N₂)
    (hB : Γ ⊢[PRAAx] N₁ * N₁ ≐ D * (N₂ * N₂) + a * a) (b1 : Γ ⊢[PRAAx] le N₁ U₁) (b2 : Γ ⊢[PRAAx] le N₂ U₂)
    (W : Γ ⊢[PRAAx] a * (qj * qj) ≐ a * (qi * qi) + c * N₂) :
    Γ ⊢[PRAAx] (quo N₁ a * quo N₁ a ≐ D * (quo N₂ a * quo N₂ a) + one) ⋏
      (le one (quo N₂ a) ⋏ (le (quo N₁ a) U₁ ⋏ le (quo N₂ a) U₂)) := by
  have f1 := eq_of_dvd' ha d1
  have f2 := eq_of_dvd' ha d2
  have hN2 : Γ ⊢[PRAAx] N₂ ≐ succ (pred N₂) := .orE (zero_or_succ N₂) (.botE _ (lt_zero_absurd _
    (q_absurd ha.wk hlt.wk W.wk ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _))))) Prf.hyp0
  exact .andI (norm_one ha f1 f2 hB) (.andI (y_pos f2 hN2)
    (.andI (le_trans (le_of_mul ha f1) b1) (le_trans (le_of_mul ha f2) b2)))

/-! ## Positive common norm -/

/-- `N₁ = p_i p_j − D q_i q_j`. -/
abbrev N1p (D pi pj qi qj : PTm n) : PTm n := monus (pi * pj) (D * (qi * qj))
/-- `N₂ = p_i q_j − p_j q_i`. -/
abbrev N2p (pi pj qi qj : PTm n) : PTm n := monus (pi * qj) (pj * qi)

theorem pos_order1 {D a pi pj qi qj : PTm n} (hi : Γ ⊢[PRAAx] pi * pi ≐ D * (qi * qi) + a)
    (hj : Γ ⊢[PRAAx] pj * pj ≐ D * (qj * qj) + a) : Γ ⊢[PRAAx] le (D * (qi * qj)) (pi * pj) := by
  have x := natEq hi; have y := natEq hj
  refine le_of_sq_le ?_
  ipra_le 𝔞 a * 𝔞 D * (𝔞 qi * 𝔞 qi + 𝔞 qj * 𝔞 qj) + 𝔞 a * 𝔞 a with
    (𝔞 D * 𝔞 qj * 𝔞 qj + 𝔞 a) * x + (𝔞 D * 𝔞 qi * 𝔞 qi + 𝔞 a) * y +
      (𝔞 pi * 𝔞 pi - 𝔞 D * 𝔞 qi * 𝔞 qi - 𝔞 a) * y

theorem pos_order2 {D a pi pj qi qj : PTm n} (hi : Γ ⊢[PRAAx] pi * pi ≐ D * (qi * qi) + a)
    (hj : Γ ⊢[PRAAx] pj * pj ≐ D * (qj * qj) + a) (hle : Γ ⊢[PRAAx] le qi qj) :
    Γ ⊢[PRAAx] le (pj * qi) (pi * qj) := by
  have x := natEq hi; have y := natEq hj
  refine le_of_sq_le ?_
  ipra_le 𝔞 a * (𝔞 qj + 𝔞 qi) * sl hle with 𝔞 qj * 𝔞 qj * x - 𝔞 qi * 𝔞 qi * y

/-- **Positive common norm**: `p_k² = D q_k² + a` for `k = i, j`, equal residues modulo `a`, `q_i < q_j`. Then
`x = N₁/a`, `y = N₂/a` satisfy `x² = D y² + 1`, `y ≥ 1`, `x ≤ p_i p_j` and `y ≤ p_i q_j`. -/
theorem collision_pos {D a pi pj qi qj : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (hi : Γ ⊢[PRAAx] pi * pi ≐ D * (qi * qi) + a) (hj : Γ ⊢[PRAAx] pj * pj ≐ D * (qj * qj) + a)
    (hp : Γ ⊢[PRAAx] rem pi a ≐ rem pj a) (hq : Γ ⊢[PRAAx] rem qi a ≐ rem qj a) (hlt : Γ ⊢[PRAAx] lt qi qj) :
    Γ ⊢[PRAAx] (quo (N1p D pi pj qi qj) a * quo (N1p D pi pj qi qj) a ≐
        D * (quo (N2p pi pj qi qj) a * quo (N2p pi pj qi qj) a) + one) ⋏
      (le one (quo (N2p pi pj qi qj) a) ⋏
        (le (quo (N1p D pi pj qi qj) a) (pi * pj) ⋏ le (quo (N2p pi pj qi qj) a) (pi * qj))) := by
  have o1 := pos_order1 hi hj
  have o2 := pos_order2 hi hj (le_trans (le_succ_self _) hlt)
  have E1 := eq_add_of_le o1
  have E2 := eq_add_of_le o2
  have e1 := natEq E1; have e2 := natEq E2; have xi := natEq hi; have xj := natEq hj
  have Pi := natEq (Prf.andE₁ (dm ha pi)); have Pj := natEq (Prf.andE₁ (dm ha pj))
  have Qi := natEq (Prf.andE₁ (dm ha qi)); have Qj := natEq (Prf.andE₁ (dm ha qj))
  have R := natEq hp; have T := natEq hq
  have d1 : Γ ⊢[PRAAx] dvd a (N1p D pi pj qi qj) :=
    dvd_of_cert ha (k₁ := pi * quo pi a + D * (qi * quo qj a)) (k₂ := one + pi * quo pj a + D * (qi * quo qi a)) (by
      ipra_lc -e1 + 𝔞 pi * Pj - 𝔞 pi * R - 𝔞 pi * Pi - 𝔞 D * 𝔞 qi * Qj + 𝔞 D * 𝔞 qi * T + 𝔞 D * 𝔞 qi * Qi + xi)
  have d2 : Γ ⊢[PRAAx] dvd a (N2p pi pj qi qj) :=
    dvd_of_cert ha (k₁ := a * (quo pj a * quo qi a) + rem pi a * quo qi a + rem qi a * quo pj a)
      (k₂ := a * (quo pi a * quo qj a) + rem pi a * quo qj a + rem qi a * quo pi a) (by
      ipra_lc -e2 + 𝔞 qj * Pi + (𝔞 a * 𝔞 (quo pi a) + 𝔞 (rem pi a)) * (Qj - T) - 𝔞 qi * (Pj - R) -
        (𝔞 a * 𝔞 (quo pj a) + 𝔞 (rem pi a)) * Qi)
  have hB : Γ ⊢[PRAAx] N1p D pi pj qi qj * N1p D pi pj qi qj ≐
      D * (N2p pi pj qi qj * N2p pi pj qi qj) + a * a := by
    ipra_lc (𝔞 pi * 𝔞 pi - 𝔞 D * 𝔞 qi * 𝔞 qi - 𝔞 a) * xj + 𝔞 a * xi + 𝔞 a * xj -
      2 * (𝔞 pi * 𝔞 pj - 𝔞 D * (𝔞 qi * 𝔞 qj)) * e1 +
      (𝔞 pi * 𝔞 pj - 𝔞 D * (𝔞 qi * 𝔞 qj) - 𝔞 (N1p D pi pj qi qj)) * e1 + 2 * 𝔞 D * (𝔞 pi * 𝔞 qj - 𝔞 pj * 𝔞 qi) * e2 -
      𝔞 D * (𝔞 pi * 𝔞 qj - 𝔞 pj * 𝔞 qi - 𝔞 (N2p pi pj qi qj)) * e2
  exact collision_end ha hlt d1 d2 hB (monus_le' _ _) (monus_le' _ _) (c := pi * qj + pj * qi) (by
    ipra_lc (𝔞 pi * 𝔞 qj + 𝔞 pj * 𝔞 qi) * e2 - 𝔞 qj * 𝔞 qj * xi + 𝔞 qi * 𝔞 qi * xj)

/-! ## Negative common norm -/

/-- `N₁' = D q_i q_j − p_i p_j`. -/
abbrev N1n (D pi pj qi qj : PTm n) : PTm n := monus (D * (qi * qj)) (pi * pj)
/-- `N₂' = p_j q_i − p_i q_j`. -/
abbrev N2n (pi pj qi qj : PTm n) : PTm n := monus (pj * qi) (pi * qj)

theorem neg_order1 {D a pi pj qi qj : PTm n} (hi : Γ ⊢[PRAAx] D * (qi * qi) ≐ pi * pi + a)
    (hj : Γ ⊢[PRAAx] D * (qj * qj) ≐ pj * pj + a) : Γ ⊢[PRAAx] le (pi * pj) (D * (qi * qj)) := by
  have x := natEq hi; have y := natEq hj
  refine le_of_sq_le ?_
  ipra_le 𝔞 a * (𝔞 pi * 𝔞 pi + 𝔞 D * 𝔞 qj * 𝔞 qj) with
    𝔞 D * 𝔞 qj * 𝔞 qj * x + (𝔞 D * 𝔞 qi * 𝔞 qi - 𝔞 a) * y -
      (𝔞 D * 𝔞 qi * 𝔞 qi - 𝔞 pi * 𝔞 pi - 𝔞 a) * y

theorem neg_order2 {D a pi pj qi qj : PTm n} (hi : Γ ⊢[PRAAx] D * (qi * qi) ≐ pi * pi + a)
    (hj : Γ ⊢[PRAAx] D * (qj * qj) ≐ pj * pj + a) (hle : Γ ⊢[PRAAx] le qi qj) :
    Γ ⊢[PRAAx] le (pi * qj) (pj * qi) := by
  have x := natEq hi; have y := natEq hj
  refine le_of_sq_le ?_
  ipra_le 𝔞 a * (𝔞 qj + 𝔞 qi) * sl hle with 𝔞 qj * 𝔞 qj * x - 𝔞 qi * 𝔞 qi * y

/-- **Negative common norm**: `D q_k² = p_k² + a` for `k = i, j`, equal residues modulo `a`, `q_i < q_j`. Then
`x = N₁'/a`, `y = N₂'/a` satisfy `x² = D y² + 1`, `y ≥ 1`, `x ≤ D q_i q_j` and `y ≤ p_j q_i`. -/
theorem collision_neg {D a pi pj qi qj : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (hi : Γ ⊢[PRAAx] D * (qi * qi) ≐ pi * pi + a) (hj : Γ ⊢[PRAAx] D * (qj * qj) ≐ pj * pj + a)
    (hp : Γ ⊢[PRAAx] rem pi a ≐ rem pj a) (hq : Γ ⊢[PRAAx] rem qi a ≐ rem qj a) (hlt : Γ ⊢[PRAAx] lt qi qj) :
    Γ ⊢[PRAAx] (quo (N1n D pi pj qi qj) a * quo (N1n D pi pj qi qj) a ≐
        D * (quo (N2n pi pj qi qj) a * quo (N2n pi pj qi qj) a) + one) ⋏
      (le one (quo (N2n pi pj qi qj) a) ⋏
        (le (quo (N1n D pi pj qi qj) a) (D * (qi * qj)) ⋏ le (quo (N2n pi pj qi qj) a) (pj * qi))) := by
  have o1 := neg_order1 hi hj
  have o2 := neg_order2 hi hj (le_trans (le_succ_self _) hlt)
  have E1 := eq_add_of_le o1
  have E2 := eq_add_of_le o2
  have e1 := natEq E1; have e2 := natEq E2; have xi := natEq hi; have xj := natEq hj
  have Pi := natEq (Prf.andE₁ (dm ha pi)); have Pj := natEq (Prf.andE₁ (dm ha pj))
  have Qi := natEq (Prf.andE₁ (dm ha qi)); have Qj := natEq (Prf.andE₁ (dm ha qj))
  have R := natEq hp; have T := natEq hq
  have d1 : Γ ⊢[PRAAx] dvd a (N1n D pi pj qi qj) :=
    dvd_of_cert ha (k₁ := pi * quo pj a + D * (qi * quo qi a)) (k₂ := one + pi * quo pi a + D * (qi * quo qj a)) (by
      ipra_lc -e1 + 𝔞 D * 𝔞 qi * (Qj - T - Qi) + 𝔞 pi * (R + Pi - Pj) + xi)
  have d2 : Γ ⊢[PRAAx] dvd a (N2n pi pj qi qj) :=
    dvd_of_cert ha (k₁ := a * (quo pi a * quo qj a) + rem pi a * quo qj a + rem qi a * quo pi a)
      (k₂ := a * (quo pj a * quo qi a) + rem pi a * quo qi a + rem qi a * quo pj a) (by
      ipra_lc -e2 -
        (𝔞 qj * Pi + (𝔞 a * 𝔞 (quo pi a) + 𝔞 (rem pi a)) * (Qj - T) - 𝔞 qi * (Pj - R) - (𝔞 a * 𝔞 (quo pj a) + 𝔞 (rem pi a)) * Qi))
  have hB : Γ ⊢[PRAAx] N1n D pi pj qi qj * N1n D pi pj qi qj ≐
      D * (N2n pi pj qi qj * N2n pi pj qi qj) + a * a := by
    ipra_lc (𝔞 D * 𝔞 qi * 𝔞 qi - 𝔞 pi * 𝔞 pi - 𝔞 a) * xj + 𝔞 a * xi + 𝔞 a * xj +
      2 * (𝔞 pi * 𝔞 pj - 𝔞 D * (𝔞 qi * 𝔞 qj)) * e1 +
      (𝔞 D * (𝔞 qi * 𝔞 qj) - 𝔞 pi * 𝔞 pj - 𝔞 (N1n D pi pj qi qj)) * e1 - 2 * 𝔞 D * (𝔞 pi * 𝔞 qj - 𝔞 pj * 𝔞 qi) * e2 -
      𝔞 D * (𝔞 pj * 𝔞 qi - 𝔞 pi * 𝔞 qj - 𝔞 (N2n pi pj qi qj)) * e2
  exact collision_end ha hlt d1 d2 hB (monus_le' _ _) (monus_le' _ _) (c := pi * qj + pj * qi) (by
    ipra_lc (𝔞 pi * 𝔞 qj + 𝔞 pj * 𝔞 qi) * e2 - 𝔞 qj * 𝔞 qj * xi + 𝔞 qi * 𝔞 qi * xj)

end LeanProofs.IPRA.DiophantineNumberTheory.PellCollision
