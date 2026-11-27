import IPRADerivations.DiophantineNumberTheory.AperyFloor
import IPRADerivations.DiophantineNumberTheory.AperyMultibound

/-!
# The Legendre terms of the Apéry multinomial

Packet: `diophantine-number-theory/apery_ipra`, Lemma `lem:lcm-div` ("The divisibility step": `d_{42m}` divides
`d_m M_m`), the termwise part of its proof: with `q = p^e` and `J = ⌊42m/q⌋`, the `e`-th Legendre term of
`v_p(M_m)` is `⌊42m/q⌋ − ⌊21m/q⌋ − ⌊14m/q⌋ − ⌊6m/q⌋ − ⌊m/q⌋ = w(J)` (`lem:floor`), which is `≥ 0`, and `≥ 1` when
`q > m` and `q ≤ 42m`.

* `floor_comp`: `⌊⌊cY/q⌋/c⌋ = ⌊Y/q⌋` for `c, q ≥ 1` (with `cY = qJ + r`, `J = cA + s`:
  `c (Y − qA) = qs + r < cq`);
* `terms_le`: `⌊21m/q⌋ + ⌊14m/q⌋ + ⌊6m/q⌋ + ⌊m/q⌋ ≤ ⌊42m/q⌋` (`AperyFloor.floor_sum_le` at `J`);
* `terms_lt`: if `m < q` and `1 ≤ ⌊42m/q⌋`, the inequality is strict (`J ≤ 41`, `AperyFloor.floor_sum_lt`).
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.AperyLcmTerms

open_ipra exports
open LeanProofs.IPRA.DiophantineNumberTheory.AperyFloor (floors floor_sum_le floor_sum_lt)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-- `⌊⌊cY/q⌋/c⌋ = ⌊Y/q⌋` for `c = c' + 1`, `q = q' + 1`. -/
theorem floor_comp (c' Y q' : PTm k) :
    Γ ⊢[PRAAx] quo (quo (succ c' * Y) (succ q')) (succ c') ≐ quo Y (succ q') := by
  let c := succ c'
  let q := succ q'
  have hc : Γ ⊢[PRAAx] c ≐ succ c' := .eqRefl _
  have hq : Γ ⊢[PRAAx] q ≐ succ q' := .eqRefl _
  have lower : Γ ⊢[PRAAx] le (c * quo Y q) (quo (c * Y) q) :=
    Division.le_quo_of_mul_le hq
      (le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_left c (Division.mul_quo_le hq)))
  have upper : Γ ⊢[PRAAx] lt (quo (c * Y) q) (c * succ (quo Y q)) :=
    Division.quo_lt_of_lt_mul hq (lt_congr (.eqRefl _) (by ipra_ring)
      (Order.mul_lt_mul_left (zero_lt_succ c') (Division.lt_mul_succ_quo hq)))
  exact le_antisymm (Order.le_of_lt_succ (Division.quo_lt_of_lt_mul hc upper)) (Division.le_quo_of_mul_le hc lower)

/-- `⌊⌊X/q⌋/c⌋ = ⌊Y/q⌋` when `X = cY`. -/
theorem comp42 (c' : PTm k) {Y X q' : PTm k} (hX : Γ ⊢[PRAAx] X ≐ succ c' * Y) :
    Γ ⊢[PRAAx] quo (quo X (succ q')) (succ c') ≐ quo Y (succ q') :=
  (congrAp2 quoF (congrAp2 quoF hX (.eqRefl _)) (.eqRefl _)).eqTrans (floor_comp c' Y q')

/-- `⌊21m/q⌋ + ⌊14m/q⌋ + ⌊6m/q⌋ + ⌊m/q⌋ ≤ ⌊42m/q⌋`. -/
theorem terms_le (m q' : PTm k) :
    Γ ⊢[PRAAx] le (quo (num 21 * m) (succ q') + quo (num 14 * m) (succ q') + quo (num 6 * m) (succ q') +
      quo m (succ q')) (quo (num 42 * m) (succ q')) := by
  have c2 := comp42 (Γ := Γ) (num 1) (Y := num 21 * m) (X := num 42 * m) (q' := q')
    (by ipra_ring)
  have c3 := comp42 (Γ := Γ) (num 2) (Y := num 14 * m) (X := num 42 * m) (q' := q')
    (by ipra_ring)
  have c7 := comp42 (Γ := Γ) (num 6) (Y := num 6 * m) (X := num 42 * m) (q' := q')
    (by ipra_ring)
  have c42 := comp42 (Γ := Γ) (num 41) (Y := m) (X := num 42 * m) (q' := q')
    (by ipra_ring)
  exact le_congr (congrAdd (congrAdd (congrAdd c2 c3) c7) c42) (.eqRefl _)
    (floor_sum_le (quo (num 42 * m) (succ q')))

/-- If `m < q` and `1 ≤ ⌊42m/q⌋`, the inequality of `terms_le` is strict. -/
theorem terms_lt {m q' : PTm k} (hm : Γ ⊢[PRAAx] lt m (succ q'))
    (hJ : Γ ⊢[PRAAx] le one (quo (num 42 * m) (succ q'))) :
    Γ ⊢[PRAAx] lt (quo (num 21 * m) (succ q') + quo (num 14 * m) (succ q') + quo (num 6 * m) (succ q') +
      quo m (succ q')) (quo (num 42 * m) (succ q')) := by
  have c2 := comp42 (Γ := Γ) (num 1) (Y := num 21 * m) (X := num 42 * m) (q' := q')
    (by ipra_ring)
  have c3 := comp42 (Γ := Γ) (num 2) (Y := num 14 * m) (X := num 42 * m) (q' := q')
    (by ipra_ring)
  have c7 := comp42 (Γ := Γ) (num 6) (Y := num 6 * m) (X := num 42 * m) (q' := q')
    (by ipra_ring)
  have c42 := comp42 (Γ := Γ) (num 41) (Y := m) (X := num 42 * m) (q' := q')
    (by ipra_ring)
  -- `J ≤ 41`
  have hsmall : Γ ⊢[PRAAx] lt (num 42 * m) (succ q' * num 42) :=
    lt_congr (.eqRefl _) (mul_comm _ _)
      (Order.mul_lt_mul_left (by ipra_le 41 : Γ ⊢[PRAAx] le one (num 42)) hm)
  have h41 := Order.le_of_lt_succ (Division.quo_lt_of_lt_mul (.eqRefl (succ q')) hsmall)
  exact lt_congr (congrAdd (congrAdd (congrAdd c2 c3) c7) c42) (.eqRefl _)
    (floor_sum_lt hJ h41)

end LeanProofs.IPRA.DiophantineNumberTheory.AperyLcmTerms
