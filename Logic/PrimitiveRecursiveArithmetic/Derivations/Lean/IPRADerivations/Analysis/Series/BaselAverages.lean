import IPRADerivations.Analysis.Series.BaselSquares
import IPRADerivations.Combinatorics.BellDobinski
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas

/-!
# Tail averages of the Basel packet

Packet: `analysis/basel_ipra`, `paper/basel_ipra.tex`, Section `sec:difference`: for `1 ≤ d < N`,
`b_d = (H_N − H_{N−d})/d` and `E_N = ∑_{d=1}^{N−1} (−1)^{d−1} b_d`, with `H_N = ∑_{j<N} 1/(2j+1)`.

Denominators are cleared by `F = L!` with `2N ≤ L`, so that `g_j = F/(2j+1)` and `F/d` are exact:
`H(M) = ∑_{j<M} g_j = F H_M`, `C(d) = H(N) ∸ H(N ∸ d) = F (H_N − H_{N−d})` and
`b(d) = (F/d) C(d) = F² b_d`.

* `C_split`, `C_succ`, `C_le`: `H(N) = H(N − d) + C(d)`, `C(d + 1) = C(d) + g_{N−d−1}` and
  `C(d) ≤ d g_{N−d}` (each of the `d` summands has denominator at least `2(N − d) + 1`);
* `average` (`lem:average`): `b(d) ≤ b(d + 1)` for `1 ≤ d`, `d + 1 ≤ N`: multiplied by `d (d + 1)` it reads
  `(d + 1) F C(d) ≤ d F (C(d) + g_{N−d−1})`, i.e. `C(d) ≤ d g_{N−d−1}`;
* `last_bound`: `N b(N − 1) ≤ F H(N)`, i.e. `b_{N−1} = (H_N − 1)/(N − 1) ≤ H_N/N`, which after multiplying by
  `N − 1` is `H(N) ≤ N F`;
* `boundary_E` (`lem:E`, `eq:E`): for `N ≥ 2`, with the alternating sum `∑_{i ≤ N−2} (−1)^i b(i + 1)` kept as its
  even and odd parts `E`, `O` (`BaselFinite`), `N E ≤ N O + F H(N)` and `N O ≤ N E + F H(N)`, i.e.
  `|E_N| ≤ H_N/N`, by `lem:increasing`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.BaselAverages

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.BaselFinite (odd_pos tB inst2_t T block_up Ev Od Inc alt_increasing)
open LeanProofs.IPRA.Analysis.BaselSquares (fact_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (quo_anti)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Combinatorics.BellDobinski (monus_of_eq)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Definitions -/

/-- `g_j = L!/(2j+1)`. -/
abbrev g (j L : PTm n) : PTm n := quo (fact L) (succ (two * j))
/-- `H(M) = ∑_{j<M} g_j`. -/
abbrev H (M L : PTm n) : PTm n := T M (fact L)
/-- `C(d) = H(N) ∸ H(N ∸ d)`. -/
abbrev C (d N L : PTm n) : PTm n := monus (H N L) (H (monus N d) L)
/-- `b(d) = (L!/d) C(d)`. -/
abbrev b (d N L : PTm n) : PTm n := quo (fact L) d * C d N L

theorem H_succ (M L : PTm n) : Γ ⊢[PRAAx] H (succ M) L ≐ H M L + g M L := by
  have h := sum_succ' (Γ := Γ) tB M (fact L)
  rw [inst2_t] at h
  exact h

theorem H_le (P d L : PTm n) : Γ ⊢[PRAAx] le (H P L) (H (P + d) L) :=
  le_congr (.eqRefl _) (sum_split tB P d (fact L)).eqSymm (le_add_right _ _)

theorem H_le' {P N L : PTm n} (h : Γ ⊢[PRAAx] le P N) : Γ ⊢[PRAAx] le (H P L) (H N L) :=
  le_congr (.eqRefl _) (congrAp2 (sumF tB) (eq_add_of_le h).eqSymm (.eqRefl _)) (H_le P (monus N P) L)

/-! ## The tails `C(d)` -/

alias monus_le_self := Common.monus_le_self

theorem C_split (d N L : PTm n) : Γ ⊢[PRAAx] H N L ≐ H (monus N d) L + C d N L :=
  eq_add_of_le (H_le' (monus_le_self N d))

/-- `N ∸ d = (N ∸ (d + 1)) + 1` for `d + 1 ≤ N`. -/
theorem monus_succ_eq {d N : PTm n} (h : Γ ⊢[PRAAx] le (succ d) N) :
    Γ ⊢[PRAAx] monus N d ≐ succ (monus N (succ d)) :=
  monus_of_eq ((eq_add_of_le h).eqTrans (by ipra_ring))

theorem C_succ {d N L : PTm n} (h : Γ ⊢[PRAAx] le (succ d) N) :
    Γ ⊢[PRAAx] C (succ d) N L ≐ C d N L + g (monus N (succ d)) L := by
  have a := natEq (C_split (Γ := Γ) d N L); have a' := natEq (C_split (Γ := Γ) (succ d) N L)
  have e := natEq ((congrAp2 (sumF tB) (monus_succ_eq h) (.eqRefl (fact L))).eqTrans
    (H_succ (Γ := Γ) (monus N (succ d)) L))
  apply deriveNat; ipra_simps
  linear_combination a - a' + e

/-- `C(d) ≤ d g_{N−d}` for `d ≤ N`. -/
theorem C_le {d N L : PTm n} (h : Γ ⊢[PRAAx] le d N) :
    Γ ⊢[PRAAx] le (C d N L) (d * g (monus N d) L) := by
  have bu := block_up (Γ := Γ) (monus N d) d (fact L)
  have e : Γ ⊢[PRAAx] monus N d + d ≐ N := ((eq_add_of_le h).eqTrans (add_comm _ _)).eqSymm
  have bu' := natEq (eq_add_of_le (le_congr (congrAp2 (sumF tB) e (.eqRefl _)) (.eqRefl _) bu))
  refine le_of_eq_add (d := monus (H (monus N d) L + d * g (monus N d) L) (H N L)) ?_
  ipra_lc bu' + natEq (C_split (Γ := Γ) d N L)

/-! ## Increasing averages -/

/-- `lem:average`, cleared: `b(d) ≤ b(d + 1)` for `d = d₀ + 1`, `d + 1 ≤ N`, `d + 1 ≤ L`. -/
theorem average {d₀ N L : PTm n} (hN : Γ ⊢[PRAAx] le (succ (succ d₀)) N) (hL : Γ ⊢[PRAAx] le (succ (succ d₀)) L) :
    Γ ⊢[PRAAx] le (b (succ d₀) N L) (b (succ (succ d₀)) N L) := by
  have cl := C_le (L := L) (le_trans (le_succ_self _) hN)
  have hq := quo_anti (Γ := Γ) (F := fact L) (odd_pos (two * monus N (succ (succ d₀))))
    (le_of_eq_add (d := two) ((congrSucc (congrMul (.eqRefl two) (monus_succ_eq hN))).eqTrans
      (by ipra_ring)))
  refine mul_le_cancel (d' := d₀) (mul_le_cancel (d' := succ d₀) ?_)
  refine le_of_eq_add (d := fact L * monus (succ d₀ * g (monus N (succ (succ d₀))) L) (C (succ d₀) N L)) ?_
  ipra_lc 𝔞 (fact L) * natEq (eq_add_of_le (le_trans cl (le_mul_mono (le_refl (succ d₀)) hq))) +
    (𝔞 d₀ + 1) * 𝔞 (fact L) * natEq (C_succ (L := L) hN) -
    (𝔞 d₀ + 1) * 𝔞 (C (succ (succ d₀)) N L) * natEq (fact_eq hL) +
    (𝔞 d₀ + 2) * 𝔞 (C (succ d₀) N L) * natEq (fact_eq (le_trans (le_succ_self _) hL))

/-! ## The last average and the boundary term -/

theorem quo_one' (F : PTm n) : Γ ⊢[PRAAx] quo F (succ (two * zero)) ≐ F :=
  LeanProofs.IPRA.AnalyticNumberTheory.Totient.quo_eq (q := F) (r := zero) (odd_pos _) (by ipra_ring)
    (le_of_eq_add (d := two * zero) (by ipra_ring))

/-- `H(N) ≤ N F`: every `g_j ≤ F`. -/
theorem H_le_N (N L : PTm n) : Γ ⊢[PRAAx] le (H N L) (N * fact L) := by
  have bu := block_up (Γ := Γ) zero N (fact L)
  refine le_of_eq_add (d := monus (T zero (fact L) + N * quo (fact L) (succ (two * zero))) (T (zero + N) (fact L))) ?_
  ipra_lc natEq (eq_add_of_le bu) + natEq (congrAp2 (sumF tB) (zero_add N) (.eqRefl (fact L)) (Γ := Γ)) -
    natEq (sum_zero (Γ := Γ) tB (fact L)) - 𝔞 N * natEq (quo_one' (Γ := Γ) (fact L))

/-- `N b(N − 1) ≤ F H(N)` for `N = m + 2 ≤ L`, i.e. `b_{N−1} = (H_N − 1)/(N − 1) ≤ H_N/N`. -/
theorem last_bound {m N L : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (succ m)) (hL : Γ ⊢[PRAAx] le N L) :
    Γ ⊢[PRAAx] le (N * b (succ m) N L) (fact L * H N L) := by
  have hL' : Γ ⊢[PRAAx] le (succ m) L :=
    le_trans (le_succ_self _) (le_congr hN (.eqRefl _) hL)
  have e1 : Γ ⊢[PRAAx] monus N (succ m) ≐ succ zero :=
    monus_of_eq (hN.eqTrans (by ipra_ring))
  have h1 := natEq ((congrAp2 (sumF tB) e1 (.eqRefl (fact L))).eqTrans ((H_succ (Γ := Γ) zero L).eqTrans
    ((congrAdd (sum_zero _ _) (quo_one' _)).eqTrans (zero_add _))))
  refine mul_le_cancel (d' := m) ?_
  refine le_of_eq_add (d := fact L * monus (N * fact L) (H N L)) ?_
  ipra_lc 𝔞 (fact L) * natEq (eq_add_of_le (H_le_N (Γ := Γ) N L)) - 𝔞 (fact L) * 𝔞 (H N L) * natEq hN +
    𝔞 N * 𝔞 (fact L) * h1 + 𝔞 N * 𝔞 (fact L) * natEq (C_split (Γ := Γ) (succ m) N L) +
    𝔞 N * 𝔞 (C (succ m) N L) * natEq (fact_eq hL')

/-- The weight `b(i + 1)` over `0 = i`, `1 = ⟨N, L⟩`. -/
abbrev wB : PTm 2 := quo (fact (sndT (var 1))) (succ (var 0)) *
  monus (T (fstT (var 1)) (fact (sndT (var 1)))) (T (monus (fstT (var 1)) (succ (var 0))) (fact (sndT (var 1))))

theorem inst2_w (i x : PTm n) : inst2 wB i x = b (succ i) (fstT x) (sndT x) := by simp [inst2]

theorem shift_le {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift a) (Syn.shift b) := by
  have e := h.shift
  simp only [Fm.shift, subst_le] at e
  exact e

/-- The weights `b(i + 1)`, `i ≤ m`, increase for `N = m + 2 ≤ L` (`lem:average`). -/
theorem inc_w {m L : PTm n} (hL : Γ ⊢[PRAAx] le (succ (succ m)) L) :
    Γ ⊢[PRAAx] Inc wB (succ m) (pairT (succ (succ m)) L) := by
  refine .allI (.impI ?_)
  rw [inst2_w, inst2_w, shift_pairT]
  have es : Syn.shift (succ (succ m)) = succ (succ (Syn.shift m)) := by simp [Syn.shift]
  have es1 : Syn.shift (succ m) = succ (Syn.shift m) := by simp [Syn.shift]
  rw [es]
  have h0 : (lt (succ (var 0)) (Syn.shift (succ m)) :: Γ.map Fm.shift) ⊢[PRAAx]
      le (succ (succ (var 0))) (succ (Syn.shift m)) := by
    have h := (Prf.hyp0 : (lt (succ (var 0)) (Syn.shift (succ m)) :: Γ.map Fm.shift) ⊢[PRAAx] _)
    rw [es1] at h
    exact h
  have hN : (lt (succ (var 0)) (Syn.shift (succ m)) :: Γ.map Fm.shift) ⊢[PRAAx]
      le (succ (succ (var 0))) (succ (succ (Syn.shift m))) := le_trans h0 (le_succ_self _)
  have hLs := (shift_le hL).wk (ψ := lt (succ (var 0)) (Syn.shift (succ m)))
  rw [es] at hLs
  exact average (le_congr (.eqRefl _) (fst_pair _ _).eqSymm hN)
    (le_congr (.eqRefl _) (snd_pair _ _).eqSymm (le_trans hN hLs))

/-- `lem:E` (`eq:E`), cleared by `F = L!`: for `N = m + 2 ≤ L`, the even and odd parts `E`, `O` of
`∑_{i ≤ N−2} (−1)^i b(i + 1)` satisfy `N E ≤ N O + F H(N)` and `N O ≤ N E + F H(N)`, i.e. `|E_N| ≤ H_N/N`. -/
theorem boundary_E {m L : PTm n} (hL : Γ ⊢[PRAAx] le (succ (succ m)) L) :
    Γ ⊢[PRAAx] le (succ (succ m) * Ev wB (succ m) (pairT (succ (succ m)) L))
        (succ (succ m) * Od wB (succ m) (pairT (succ (succ m)) L) + fact L * H (succ (succ m)) L) ⋏
      le (succ (succ m) * Od wB (succ m) (pairT (succ (succ m)) L))
        (succ (succ m) * Ev wB (succ m) (pairT (succ (succ m)) L) + fact L * H (succ (succ m)) L) := by
  have a := alt_increasing wB (inc_w hL)
  rw [inst2_w] at a
  have lb := last_bound (m := m) (N := fstT (pairT (succ (succ m)) L)) (L := sndT (pairT (succ (succ m)) L))
    (fst_pair _ _) (le_congr (fst_pair _ _).eqSymm (snd_pair _ _).eqSymm hL)
  have efh := natEq (congrMul (congrAp2 factF (snd_pair (Γ := Γ) (succ (succ m)) L) (.eqRefl zero))
    (congrAp2 (sumF tB) (fst_pair (Γ := Γ) (succ (succ m)) L)
      (congrAp2 factF (snd_pair (Γ := Γ) (succ (succ m)) L) (.eqRefl zero))))
  have j1 := natEq (eq_add_of_le (Prf.andE₁ a)); have j2 := natEq (eq_add_of_le (Prf.andE₂ a))
  refine .andI (le_of_eq_add (d := succ (succ m) * monus (Od wB (succ m) (pairT (succ (succ m)) L) +
      b (succ m) (fstT (pairT (succ (succ m)) L)) (sndT (pairT (succ (succ m)) L)))
      (Ev wB (succ m) (pairT (succ (succ m)) L)) +
    monus (fact (sndT (pairT (succ (succ m)) L)) * H (fstT (pairT (succ (succ m)) L)) (sndT (pairT (succ (succ m)) L)))
      (fstT (pairT (succ (succ m)) L) * b (succ m) (fstT (pairT (succ (succ m)) L)) (sndT (pairT (succ (succ m)) L))))
    ?_)
    (le_of_eq_add (d := succ (succ m) * monus (Ev wB (succ m) (pairT (succ (succ m)) L) +
      b (succ m) (fstT (pairT (succ (succ m)) L)) (sndT (pairT (succ (succ m)) L)))
      (Od wB (succ m) (pairT (succ (succ m)) L)) +
    monus (fact (sndT (pairT (succ (succ m)) L)) * H (fstT (pairT (succ (succ m)) L)) (sndT (pairT (succ (succ m)) L)))
      (fstT (pairT (succ (succ m)) L) * b (succ m) (fstT (pairT (succ (succ m)) L)) (sndT (pairT (succ (succ m)) L))))
    ?_)
  · ipra_lc (𝔞 m + 2) * j1 + natEq (eq_add_of_le lb) - efh +
      𝔞 (quo (fact (sndT (pairT (succ (succ m)) L))) (succ m)) * 𝔞 (C (succ m) (fstT (pairT (succ (succ m)) L)) (sndT (pairT (succ (succ m)) L))) * natEq (fst_pair (Γ := Γ) (succ (succ m)) L)
  · ipra_lc (𝔞 m + 2) * j2 + natEq (eq_add_of_le lb) - efh +
      𝔞 (quo (fact (sndT (pairT (succ (succ m)) L))) (succ m)) * 𝔞 (C (succ m) (fstT (pairT (succ (succ m)) L)) (sndT (pairT (succ (succ m)) L))) * natEq (fst_pair (Γ := Γ) (succ (succ m)) L)

end LeanProofs.IPRA.Analysis.BaselAverages
