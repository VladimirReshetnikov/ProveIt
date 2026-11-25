import IPRADerivations.Core.Division
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.Gcd

/-!
# The floor certificate of the lcm bound

Packet: `diophantine-number-theory/apery_ipra`, `apery_ipra.tex`, Lemma `lem:floor` ("A floor certificate"):
for `w(j) = j − ⌊j/2⌋ − ⌊j/3⌋ − ⌊j/7⌋ − ⌊j/42⌋`, `w(j) ≥ 0` for all `j`, and `w(j) ≥ 1` when `1 ≤ j ≤ 41`.
"The identity `1/2 + 1/3 + 1/7 + 1/42 = 1` shows that the sum of the four floors is at most `j`. If
`1 ≤ j ≤ 41`, the last floor is zero and the other three sum to at most `41j/42 < j`."

The floors are the quotients `quo j a` of `Core/Division` (`j = a ⌊j/a⌋ + (j mod a)`):

* `floor_sum_le`: `⌊j/2⌋ + ⌊j/3⌋ + ⌊j/7⌋ + ⌊j/42⌋ ≤ j` (`42 · sum + 21 r₂ + 14 r₃ + 6 r₇ + r₄₂ = 42 j`, then
  the factor `42` is cancelled);
* `floor_sum_lt`: for `1 ≤ j ≤ 41`, `⌊j/2⌋ + ⌊j/3⌋ + ⌊j/7⌋ + ⌊j/42⌋ < j` (here `⌊j/42⌋ = 0`,
  `j mod 42 = j`, so `42 · sum ≤ 41 j`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.AperyFloor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

set_option hygiene false in
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

/-- The four floors `⌊j/2⌋ + ⌊j/3⌋ + ⌊j/7⌋ + ⌊j/42⌋`. -/
abbrev floors (j : PTm k) : PTm k :=
  quo j (num 2) + quo j (num 3) + quo j (num 7) + quo j (num 42)

theorem floor_sum_le (j : PTm k) : Γ ⊢[PRAAx] le (floors j) j := by
  have d2 := div_mod (Γ := Γ) j (num 1)
  have d3 := div_mod (Γ := Γ) j (num 2)
  have d7 := div_mod (Γ := Γ) j (num 6)
  have d42 := div_mod (Γ := Γ) j (num 41)
  have e2 := natEq (Prf.andE₁ d2)
  have e3 := natEq (Prf.andE₁ d3)
  have e7 := natEq (Prf.andE₁ d7)
  have e42 := natEq (Prf.andE₁ d42)
  refine mul_le_cancel (d' := num 41) ?_
  change Γ ⊢[PRAAx] le (succ (num 41) * (quo j (succ (num 1)) + quo j (succ (num 2)) + quo j (succ (num 6)) +
    quo j (succ (num 41)))) (succ (num 41) * j)
  ipra_le 21 * 𝔞 (rem j (succ (num 1))) + 14 * 𝔞 (rem j (succ (num 2))) + 6 * 𝔞 (rem j (succ (num 6))) +
      𝔞 (rem j (succ (num 41))) using
    linear_combination 21 * e2 + 14 * e3 + 6 * e7 + e42

theorem floor_sum_lt {j : PTm k} (h1 : Γ ⊢[PRAAx] le one j) (h41 : Γ ⊢[PRAAx] le j (num 41)) :
    Γ ⊢[PRAAx] lt (floors j) j := by
  have d2 := div_mod (Γ := Γ) j (num 1)
  have d3 := div_mod (Γ := Γ) j (num 2)
  have d7 := div_mod (Γ := Γ) j (num 6)
  have u := div_mod_unique (Γ := Γ) (z := j) (q := zero) (r := j) (K' := num 41)
    (by ipra_ring) (by
      show Γ ⊢[PRAAx] le (succ j) (succ (num 41))
      ipra_le sl h41)
  have e2 := natEq (Prf.andE₁ d2)
  have e3 := natEq (Prf.andE₁ d3)
  have e7 := natEq (Prf.andE₁ d7)
  have q0 := natEq (Prf.andE₁ u)
  -- `42 · floors + j ≤ 42 j`
  have hb : Γ ⊢[PRAAx] le (succ (num 41) * floors j + j) (succ (num 41) * j) := by
    change Γ ⊢[PRAAx] le (succ (num 41) * (quo j (succ (num 1)) + quo j (succ (num 2)) + quo j (succ (num 6)) +
      quo j (succ (num 41))) + j) (succ (num 41) * j)
    ipra_le 21 * 𝔞 (rem j (succ (num 1))) + 14 * 𝔞 (rem j (succ (num 2))) + 6 * 𝔞 (rem j (succ (num 6))) using
      linear_combination 21 * e2 + 14 * e3 + 6 * e7 - 42 * q0
  refine .orE (lt_or_le (floors j) j) Prf.hyp0 ?_
  have hle : (le j (floors j) :: Γ) ⊢[PRAAx] le j (floors j) := Prf.hyp0
  have c : (le j (floors j) :: Γ) ⊢[PRAAx] le (succ zero) zero := by
    have hb' := hb.wk (ψ := le j (floors j))
    have h1' := h1.wk (ψ := le j (floors j))
    ipra_le sl hb' + 42 * sl hle + sl h1'
  exact not_succ_le_self zero _ c

end LeanProofs.IPRA.DiophantineNumberTheory.AperyFloor
