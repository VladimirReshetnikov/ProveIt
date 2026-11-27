import IPRADerivations.DiophantineNumberTheory.AperySparse
import IPRADerivations.DiophantineNumberTheory.AperyGrowth

/-!
# The explicit index of the Apéry argument

Packet: `diophantine-number-theory/apery_ipra`, Lemma `lem:index` ("The chosen index is large enough"): for
`q ≥ 1` and `n = 42^{q+1}`, `n ≥ 48` and `q d_n^3 / a_n < 1/8`, i.e. `8 q d_n^3 < a_n` after clearing the
positive denominator.

"Put `C = 32^48 = 2^240`. Equations `eq:grow32` and `eq:sparse` give `q d_n^3 / a_n ≤ q C (7/8)^n` ...
`n ≥ 1764q ≥ 6(q + 243)` ... `8^6 = 262144 > 235298 = 2 · 7^6` yields `(8/7)^n ≥ (8/7)^{6(q+243)} > 2^{q+243}`
... `q C (7/8)^n < q 2^240 / 2^{q+243} = q / (8 · 2^q) ≤ 1/8`."

* `key`: if `6(q + 243) ≤ N` then `8 q 28^N 2^240 < 32^N` (with `28 = 4 · 7`, `32 = 4 · 8`, the split
  `N = 6(q + 243) + r`, `2 · 7^6 ≤ 8^6`, `7 ≤ 8` and `q < 2^q`);
* `index`: `lem:index` for `q + 1`: `48 ≤ n` and `8 (q + 1) d_n^3 < a_n` for `n = 42^{q+2}`
  (`AperySparse.sparse`, `AperyGrowth.grow_pow`).
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.AperyIndex

open_ipra exports
open LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound (pw_num num_lt)
open LeanProofs.IPRA.DiophantineNumberTheory.AperyMultinomial (base_split)
open LeanProofs.IPRA.DiophantineNumberTheory.AperySparse (sparse)
open LeanProofs.IPRA.DiophantineNumberTheory.AperyGrowth (grow_pow congrApery)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-- `8 q 28^N 2^240 < 32^N` when `6(q + 243) ≤ N`. -/
theorem key {q N : PTm k} (hN : Γ ⊢[PRAAx] le (num 6 * (q + num 243)) N) :
    Γ ⊢[PRAAx] lt (num 8 * q * pw (num 28) N * num (2 ^ 240)) (pw (num 32) N) := by
  have eN : Γ ⊢[PRAAx] N ≐ num 6 * (q + num 243) + monus N (num 6 * (q + num 243)) := eq_add_of_le hN
  have e8 : Γ ⊢[PRAAx] pw (num 8) N ≐
      pw (num (8 ^ 6)) (q + num 243) * pw (num 8) (monus N (num 6 * (q + num 243))) :=
    (congrPw (.eqRefl _) eN).eqTrans ((pw_add _ _ _).eqTrans
      (congrMul ((pw_mul _ _ _).eqSymm.eqTrans (congrPw (pw_num 8 6) (.eqRefl _))) (.eqRefl _)))
  have e7 : Γ ⊢[PRAAx] pw (num 7) N ≐
      pw (num (7 ^ 6)) (q + num 243) * pw (num 7) (monus N (num 6 * (q + num 243))) :=
    (congrPw (.eqRefl _) eN).eqTrans ((pw_add _ _ _).eqTrans
      (congrMul ((pw_mul _ _ _).eqSymm.eqTrans (congrPw (pw_num 7 6) (.eqRefl _))) (.eqRefl _)))
  have e2 := base_split (Γ := Γ) (a := 2 * 7 ^ 6) (b := 2) (c := 7 ^ 6) rfl (q + num 243)
  have m1 : Γ ⊢[PRAAx] le (pw (num (2 * 7 ^ 6)) (q + num 243)) (pw (num (8 ^ 6)) (q + num 243)) :=
    pw_le_pw _ (le_of_lt (num_lt _ _ (by norm_num)))
  have m2 : Γ ⊢[PRAAx] le (pw (num 7) (monus N (num 6 * (q + num 243))))
      (pw (num 8) (monus N (num 6 * (q + num 243)))) :=
    pw_le_pw _ (le_of_lt (num_lt 7 8 (by norm_num)))
  have es : Γ ⊢[PRAAx] pw (num 2) (q + num 243) ≐ pw (num 2) q * num (2 ^ 243) :=
    (pw_add _ _ _).eqTrans (congrMul (.eqRefl _) (pw_num 2 243))
  have e28 := base_split (Γ := Γ) (a := 28) (b := 4) (c := 7) rfl N
  have e32 := base_split (Γ := Γ) (a := 32) (b := 4) (c := 8) rfl N
  have h2 : Γ ⊢[PRAAx] le two (num 2) := le_of_eq_add (d := zero) (by ipra_ring)
  have hq := lt_pw h2 q
  have hq' : Γ ⊢[PRAAx] le (succ q) (pw (num 2) q) := hq
  have h4 : Γ ⊢[PRAAx] (num 4 : PTm k) ≐ succ (pred (num 4)) :=
    show Γ ⊢[PRAAx] succ (num 3) ≐ succ (pred (succ (num 3))) from congrSucc (pred_succ _).eqSymm
  have h7 : Γ ⊢[PRAAx] (num 7 : PTm k) ≐ succ (pred (num 7)) :=
    show Γ ⊢[PRAAx] succ (num 6) ≐ succ (pred (succ (num 6))) from congrSucc (pred_succ _).eqSymm
  have pp := pos_mul (pw_pos' h4 N) (pw_pos' h7 N)
  have hpos : Γ ⊢[PRAAx] le one (pw (num 4) N * pw (num 7) N) :=
    le_congr (.eqRefl _) pp.eqSymm (by ipra_le 𝔞 (pred (pw (num 4) N * pw (num 7) N)))
  have a8 := natEq e8; have a7 := natEq e7; have a2 := natEq e2; have as := natEq es
  have a28 := natEq e28; have a32 := natEq e32
  show Γ ⊢[PRAAx] le (succ (num 8 * q * pw (num 28) N * num (2 ^ 240))) (pw (num 32) N)
  ipra_le 𝔞 (pw (num 4) N) * (𝔞 (pw (num (8 ^ 6)) (q + num 243)) * sl m2 +
      𝔞 (pw (num 7) (monus N (num 6 * (q + num 243)))) * sl m1) +
    2 ^ 243 * 𝔞 (pw (num 4) N) * 𝔞 (pw (num 7) N) * sl hq' +
    14134776518227074636666380005943348126619871175004951664972849610340958207 * 𝔞 (pw (num 4) N) * 𝔞 (pw (num 7) N) + sl hpos using
    linear_combination a32 - 2 ^ 243 * 𝔞 q * a28 + 𝔞 (pw (num 4) N) * a8 -
      2 ^ 243 * 𝔞 (pw (num 2) q) * 𝔞 (pw (num 4) N) * a7 +
      𝔞 (pw (num 4) N) * 𝔞 (pw (num 7) (monus N (num 6 * (q + num 243)))) * a2 +
      𝔞 (pw (num 4) N) * 𝔞 (pw (num 7) (monus N (num 6 * (q + num 243)))) *
        𝔞 (pw (num (7 ^ 6)) (q + num 243)) * as

/-- The index `n = 42^{q+2}` (for the denominator `q + 1 ≥ 1`). -/
abbrev nq (q : PTm k) : PTm k := pw (num 42) (succ (succ q))

/-- `lem:index` for the denominator `q + 1`: `48 ≤ n` and `8 (q + 1) d_n^3 < a_n`, `n = 42^{q+2}`. -/
theorem index (q : PTm k) :
    Γ ⊢[PRAAx] le (num 48) (nq q) ⋏ lt (num 8 * succ q * pw (lcmu (nq q)) (num 3)) (apery (nq q)) := by
  have p1 := natEq (pw_succ (Γ := Γ) (num 42) (succ q))
  have p2 := natEq (pw_succ (Γ := Γ) (num 42) q)
  have h42 : Γ ⊢[PRAAx] (num 42 : PTm k) ≐ succ (pred (num 42)) :=
    show Γ ⊢[PRAAx] succ (num 41) ≐ succ (pred (succ (num 41))) from congrSucc (pred_succ _).eqSymm
  have p0 := natEq (pw_pos' h42 q)
  have h2 : Γ ⊢[PRAAx] le two (num 42) := le_of_eq_add (d := num 40) (by ipra_ring)
  have hl : Γ ⊢[PRAAx] le (succ (succ q)) (pw (num 42) (succ q)) := lt_pw h2 (succ q)
  have n48 : Γ ⊢[PRAAx] le (num 48) (nq q) := by
    ipra_le 1764 * 𝔞 (pred (pw (num 42) q)) + 1716 using linear_combination p1 + 42 * p2 + 1764 * p0
  have hN : Γ ⊢[PRAAx] le (num 6 * (succ q + num 243)) (nq q) := by
    ipra_le 6 * sl hl + 1512 * 𝔞 (pred (pw (num 42) q)) + 60 using linear_combination p1 + 36 * p2 + 1512 * p0
  have sp := sparse (Γ := Γ) (succ (succ q))
  have ea : Γ ⊢[PRAAx] nq q ≐ num 48 + monus (nq q) (num 48) := eq_add_of_le n48
  have ga : Γ ⊢[PRAAx] le (pw (num 32) (monus (nq q) (num 48))) (apery (nq q)) :=
    le_congr (.eqRefl _) (congrApery ea.eqSymm) (grow_pow (monus (nq q) (num 48)))
  have e32 : Γ ⊢[PRAAx] pw (num 32) (nq q) ≐ num (32 ^ 48) * pw (num 32) (monus (nq q) (num 48)) :=
    (congrPw (.eqRefl _) ea).eqTrans ((pw_add _ _ _).eqTrans (congrMul (pw_num 32 48) (.eqRefl _)))
  have kk := key (Γ := Γ) hN
  refine Prf.andI n48 ?_
  refine .orE (lt_or_le (num 8 * succ q * pw (lcmu (nq q)) (num 3)) (apery (nq q))) Prf.hyp0 ?_
  let Δ := le (apery (nq q)) (num 8 * succ q * pw (lcmu (nq q)) (num 3)) :: Γ
  have hle : Δ ⊢[PRAAx] le (apery (nq q)) (num 8 * succ q * pw (lcmu (nq q)) (num 3)) := Prf.hyp0
  have hd : Δ ⊢[PRAAx] le (pw (lcmu (nq q)) (num 3)) (pw (num 28) (nq q)) := sp.wk
  have kk' : Δ ⊢[PRAAx] le (succ (num 8 * succ q * pw (num 28) (nq q) * num (2 ^ 240))) (pw (num 32) (nq q)) := kk.wk
  have ga' : Δ ⊢[PRAAx] le (pw (num 32) (monus (nq q) (num 48))) (apery (nq q)) := ga.wk
  have e := natEq (e32.wk : Δ ⊢[PRAAx] _)
  have c : Δ ⊢[PRAAx] le (succ zero) zero := by
    ipra_le 2 ^ 240 * sl hle + 8 * 2 ^ 240 * (𝔞 q + 1) * sl hd + sl kk' + 2 ^ 240 * sl ga' using
      linear_combination -e
  exact not_succ_le_self zero _ c

end LeanProofs.IPRA.DiophantineNumberTheory.AperyIndex
