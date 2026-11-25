import IPRADerivations.AnalyticNumberTheory.HarmonicMertensLower
import IPRADerivations.Core.LinearCombination

/-!
# The logarithmic sum for the harmonic logarithm (`pnt_ipra_constructive_2026-11-14`, `sb:log-sum`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, Lemma `sb:harmonic-finite`,
inequality `sb:log-sum`: `|P_1(y) − (y log y − y)| ≤ log y + 1` for `P_1(y) = Σ_{n≤y} log n`. With the packet's
rational logarithm `λ_K(n) = H_{Kn} − H_K` and a common denominator `F = L!` (`KN ≤ L`), write
`P(N) = Σ_{n≤N} S(Kn, F)`, so that `F P_1(N) = P(N) − N S(K)` and `F λ_K(N) = S(KN) − S(K)`:

* `inc_lower`: `λ_K(n+1) − λ_K(n) ≥ 1/(n+1)` exactly — `S(Kn) + ⌊F/(n+1)⌋ ≤ S(K(n+1))`, from
  `LogElementary.log_lower` (each of the `K` new harmonic terms is at least `1/(K(n+1))`);
* `log_sum`: `Nλ_K(N) − N ≤ P_1(N) ≤ Nλ_K(N) − N + H_N`, i.e. `N S(KN) ≤ P(N) + NF` and
  `P(N) + NF ≤ N S(KN) + S(N)` — one QF induction on `N` with `inc_lower` and
  `HarmonicMertensLower.delta_le` (`n(λ_K(n+1) − λ_K(n)) ≤ 1`).

Since `H_N ≤ λ_K(N) + 1 + 1/K`-type bounds hold (`HarmonicLogPow2`, `LogRefinement`), this is the packet's
`|P_1(y) − (y log y − y)| ≤ log y + 1` at integer `y`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSum

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB inst2_h)
open LeanProofs.IPRA.AnalyticNumberTheory.LogElementary (log_lower)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertensLower (delta_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (dvd_fact)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd')
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (pos_of_lt_zero)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `(N + 1) ⌊F/(N+1)⌋ = F` for `F = L!`, `N + 1 ≤ L`. -/
theorem fact_quo {N L : PTm n} (h : Γ ⊢[PRAAx] le (succ N) L) :
    Γ ⊢[PRAAx] fact L ≐ succ N * quo (fact L) (succ N) :=
  eq_of_dvd' (congrSucc (pred_succ _).eqSymm) (dvd_fact h)

/-- `λ_K(N+1) − λ_K(N) ≥ 1/(N+1)`: `S(KN) + ⌊F/(N+1)⌋ ≤ S(K(N+1))` for `F = L!`, `K(N+1) ≤ L`. -/
theorem inc_lower {K N L : PTm n} (hK : Γ ⊢[PRAAx] K ≐ succ (pred K)) (hL : Γ ⊢[PRAAx] le (K * succ N) L) :
    Γ ⊢[PRAAx] le (S (K * N) (fact L) + quo (fact L) (succ N)) (S (K * succ N) (fact L)) := by
  have hX : Γ ⊢[PRAAx] K * succ N ≐ succ (pred (K * succ N)) := by
    refine pos_of_lt_zero (le_of_eq_add (d := K * N + pred K) ?_)
    ipra_lc natEq hK
  have dv := dvd_congr_left hX.eqSymm (dvd_fact (le_congr hX (.eqRefl _) hL))
  have hF : Γ ⊢[PRAAx] fact L ≐ (K * N + K) * quo (fact L) (K * succ N) := by
    ipra_lc natEq (eq_of_dvd' hX dv)
  have ll := log_lower (K * N) K hF
  have hNL : Γ ⊢[PRAAx] le (succ N) L := by
    refine le_trans (le_of_eq_add (d := pred K * succ N) ?_) hL
    ipra_lc (𝔞 N + 1) * natEq hK
  have eq := natEq (fact_quo hNL)
  have q : Γ ⊢[PRAAx] K * succ N ≐ K * N + K := by ipra_ring
  have eS := natEq (congrAp2 (Γ := Γ) (sumF hB) q (.eqRefl (fact L)))
  refine mul_le_cancel (d' := pred (K * succ N)) ?_
  have c : Γ ⊢[PRAAx] le (K * succ N * (S (K * N) (fact L) + quo (fact L) (succ N)))
      (K * succ N * S (K * succ N) (fact L)) := by
    ipra_le sl ll with -(𝔞 K) * eq - (𝔞 K * 𝔞 N + 𝔞 K) * eS
  exact le_congr (congrMul hX (.eqRefl _)) (congrMul hX (.eqRefl _)) c

/-! ## The sum `P(N) = Σ_{n≤N} S(Kn)` -/

/-- `S(K(k+1), F)` with parameter `z = (K, F)`. -/
abbrev PB : PTm 2 := S (fstT (var 1) * succ (var 0)) (sndT (var 1))

theorem inst2_PB (k z : PTm n) : inst2 PB k z = S (fstT z * succ k) (sndT z) := by simp [inst2]

abbrev P (N K F : PTm n) : PTm n := ap2 (sumF PB) N (pairT K F)

theorem P_succ (N K F : PTm n) : Γ ⊢[PRAAx] P (succ N) K F ≐ P N K F + S (K * succ N) F := by
  refine (sum_succ' PB N (pairT K F)).eqTrans (congrAdd (.eqRefl _) ?_)
  rw [inst2_PB]
  exact congrAp2 (sumF hB) (congrMul (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)

/-- The two invariants: `N S(KN) ≤ P(N) + NF` and `P(N) + NF ≤ N S(KN) + S(N)`. -/
abbrev I2 (N K L : PTm n) : Fm PTm n :=
  le (N * S (K * N) (fact L)) (P N K (fact L) + N * fact L) ⋏
    le (P N K (fact L) + N * fact L) (N * S (K * N) (fact L) + S N (fact L))

abbrev Hl (k K L N0 : PTm n) : Fm PTm n := le one K ⋏ (le (K * N0) L ⋏ le k N0)

theorem i_zero (K L : PTm n) : Γ ⊢[PRAAx] I2 zero K L := by
  have p0 := natEq (sum_zero (Γ := Γ) PB (pairT K (fact L)))
  have s0 := natEq (sum_zero (Γ := Γ) hB (fact L))
  exact .andI (by ipra_le 0 with -p0) (by ipra_le 0 with p0 - s0)

theorem i_step {k K L N0 : PTm n} (h : Γ ⊢[PRAAx] Hl (succ k) K L N0) (ih : Γ ⊢[PRAAx] I2 k K L) :
    Γ ⊢[PRAAx] I2 (succ k) K L := by
  have hK := Prf.andE₁ h
  have hL := Prf.andE₁ (Prf.andE₂ h)
  have hk := Prf.andE₂ (Prf.andE₂ h)
  have hKp := pos_of_lt_zero hK
  have hKL : Γ ⊢[PRAAx] le (K * succ k) L := le_trans (le_scale K hk) hL
  have eP := natEq (P_succ (Γ := Γ) k K (fact L))
  have dl := delta_le (Γ := Γ) k (fact L) hKp
  have inc := le_scale k (inc_lower hKp hKL)
  have hNL : Γ ⊢[PRAAx] le (succ k) L := by
    refine le_trans (le_of_eq_add (d := pred K * succ k) ?_) hKL
    ipra_lc (𝔞 k + 1) * natEq hKp
  have eF := natEq (fact_quo hNL)
  have sS : Γ ⊢[PRAAx] S (succ k) (fact L) ≐ S k (fact L) + quo (fact L) (succ k) := by
    have s := sum_succ' (Γ := Γ) hB k (fact L)
    rw [inst2_h] at s
    exact s
  have eSs := natEq sS
  exact .andI (by ipra_le sl (Prf.andE₁ ih) + sl dl with -eP)
    (by ipra_le sl (Prf.andE₂ ih) + sl inc with eP + eF - eSs)

/-- Variables: `0 = k`, `1 = K`, `2 = L`, `3 = N0`. -/
private abbrev sumF' : Fm PTm 4 := Hl (var 0) (var 1) (var 2) (var 3) ⟶ I2 (var 0) (var 1) (var 2)

private theorem sum₀ : ([] : List (Fm PTm 4)) ⊢[PRAAx] sumF' := by
  refine ind _ ⟨⟨le_QF _ _, le_QF _ _, le_QF _ _⟩, le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_and, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, subst_pairT,
      Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two, inst_three,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (i_zero _ _)
  · simp only [Fm.subst_imp, Fm.subst_and, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, subst_pairT,
      Syn.subst_var, Syn.repl_zero, repl_one, repl_two, repl_three,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine .impI ?_
    have h := (Prf.hyp0 : (Hl (succ (var 0)) (var 1) (var 2) (var 3) :: [sumF']) ⊢[PRAAx]
      Hl (succ (var 0)) (var 1) (var 2) (var 3))
    have h' : (Hl (succ (var 0)) (var 1) (var 2) (var 3) :: [sumF']) ⊢[PRAAx] Hl (var 0) (var 1) (var 2) (var 3) :=
      .andI (Prf.andE₁ h) (.andI (Prf.andE₁ (Prf.andE₂ h)) (le_trans (le_succ_self _) (Prf.andE₂ (Prf.andE₂ h))))
    exact i_step h (Prf.impE Prf.hyp1 h')

/-- `sb:log-sum` for the harmonic logarithm: `Nλ_K(N) − N ≤ P_1(N) ≤ Nλ_K(N) − N + H_N`, i.e.
`N S(KN) ≤ P(N) + NF` and `P(N) + NF ≤ N S(KN) + S(N)`, for `K ≥ 1`, `KN ≤ L`, `F = L!`. -/
theorem log_sum {N K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hL : Γ ⊢[PRAAx] le (K * N) L) :
    Γ ⊢[PRAAx] I2 N K L := by
  have i := inst (Γ := Γ) sum₀ (![N, K, L, N] : Fin 4 → PTm n)
  simp at i
  exact Prf.impE i (.andI hK (.andI hL (le_refl N)))

end LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSum
