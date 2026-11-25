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

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.AperyLcmTerms

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.AperyFloor (floors floor_sum_le floor_sum_lt)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `⌊⌊cY/q⌋/c⌋ = ⌊Y/q⌋` for `c = c' + 1`, `q = q' + 1`. -/
theorem floor_comp (c' Y q' : PTm k) :
    Γ ⊢[PRAAx] quo (quo (succ c' * Y) (succ q')) (succ c') ≐ quo Y (succ q') := by
  have d1 := div_mod (Γ := Γ) (succ c' * Y) q'
  have d2 := div_mod (Γ := Γ) (quo (succ c' * Y) (succ q')) c'
  have e1 := natEq (Prf.andE₁ d1)
  have e2 := natEq (Prf.andE₁ d2)
  have hr : Γ ⊢[PRAAx] le (succ (rem (succ c' * Y) (succ q'))) (succ q') := Prf.andE₂ d1
  have hs : Γ ⊢[PRAAx] le (succ (rem (quo (succ c' * Y) (succ q')) (succ c'))) (succ c') := Prf.andE₂ d2
  -- abbreviations for the certificate atoms
  -- `q A ≤ Y`
  have hqA : Γ ⊢[PRAAx] le (succ q' * quo (quo (succ c' * Y) (succ q')) (succ c')) Y := by
    refine mul_le_cancel (d' := c') ?_
    ipra_le (𝔞 q' + 1) * 𝔞 (rem (quo (succ c' * Y) (succ q')) (succ c')) + 𝔞 (rem (succ c' * Y) (succ q')) using
      linear_combination e1 + (𝔞 q' + 1) * e2
  have et := natEq (eq_add_of_le hqA)
  -- `t < q`
  have ht : Γ ⊢[PRAAx] lt (monus Y (succ q' * quo (quo (succ c' * Y) (succ q')) (succ c'))) (succ q') := by
    refine .orE (lt_or_le (monus Y (succ q' * quo (quo (succ c' * Y) (succ q')) (succ c'))) (succ q'))
      Prf.hyp0 ?_
    have hge : (le (succ q') (monus Y (succ q' * quo (quo (succ c' * Y) (succ q')) (succ c'))) :: Γ) ⊢[PRAAx]
        le (succ q') (monus Y (succ q' * quo (quo (succ c' * Y) (succ q')) (succ c'))) := Prf.hyp0
    have hr' := hr.wk (ψ := le (succ q') (monus Y (succ q' * quo (quo (succ c' * Y) (succ q')) (succ c'))))
    have hs' := hs.wk (ψ := le (succ q') (monus Y (succ q' * quo (quo (succ c' * Y) (succ q')) (succ c'))))
    have e1' := natEq ((Prf.andE₁ d1).wk (ψ := le (succ q') (monus Y (succ q' * quo (quo (succ c' * Y) (succ q')) (succ c')))))
    have e2' := natEq ((Prf.andE₁ d2).wk (ψ := le (succ q') (monus Y (succ q' * quo (quo (succ c' * Y) (succ q')) (succ c')))))
    have et' := natEq ((eq_add_of_le hqA).wk (ψ := le (succ q') (monus Y (succ q' * quo (quo (succ c' * Y) (succ q')) (succ c')))))
    have c : (le (succ q') (monus Y (succ q' * quo (quo (succ c' * Y) (succ q')) (succ c'))) :: Γ) ⊢[PRAAx]
        le (succ zero) zero := by
      ipra_le (𝔞 c' + 1) * sl hge + sl hr' + (𝔞 q' + 1) * sl hs' using
        linear_combination -e1' - (𝔞 q' + 1) * e2' + (𝔞 c' + 1) * et'
    exact not_succ_le_self zero _ c
  exact (Prf.andE₁ (div_mod_unique (Γ := Γ) (z := Y)
    (q := quo (quo (succ c' * Y) (succ q')) (succ c'))
    (r := monus Y (succ q' * quo (quo (succ c' * Y) (succ q')) (succ c'))) (K' := q') (eq_add_of_le hqA) ht)).eqSymm

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
  have h41 : Γ ⊢[PRAAx] le (quo (num 42 * m) (succ q')) (num 41) := by
    have d := div_mod (Γ := Γ) (num 42 * m) q'
    refine .orE (lt_or_le (num 41) (quo (num 42 * m) (succ q'))) ?_ ?_
    · have hbig : (lt (num 41) (quo (num 42 * m) (succ q')) :: Γ) ⊢[PRAAx]
          le (num 42) (quo (num 42 * m) (succ q')) := Prf.hyp0
      have e := natEq ((Prf.andE₁ d).wk (ψ := lt (num 41) (quo (num 42 * m) (succ q'))))
      have hm' : (lt (num 41) (quo (num 42 * m) (succ q')) :: Γ) ⊢[PRAAx] le (succ m) (succ q') := hm.wk
      have c : (lt (num 41) (quo (num 42 * m) (succ q')) :: Γ) ⊢[PRAAx] le (succ zero) zero := by
        ipra_le (𝔞 q' + 1) * sl hbig + 42 * sl hm' + 41 + 𝔞 (rem (num 42 * m) (succ q')) using
          linear_combination e
      exact not_succ_le_self zero _ c
    · exact Prf.hyp0
  exact lt_congr (congrAdd (congrAdd (congrAdd c2 c3) c7) c42) (.eqRefl _)
    (floor_sum_lt hJ h41)

end LeanProofs.IPRA.DiophantineNumberTheory.AperyLcmTerms
