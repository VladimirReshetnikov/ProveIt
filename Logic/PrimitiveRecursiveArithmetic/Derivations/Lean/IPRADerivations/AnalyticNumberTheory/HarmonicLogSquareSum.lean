import IPRADerivations.AnalyticNumberTheory.HarmonicLogSum
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.InductionTactic
import IPRADerivations.Core.Header

/-!
# The square-logarithm sum for the harmonic logarithm (`pnt_ipra_constructive_2026-11-14`, `sb:log-square-sum`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, Lemma `sb:harmonic-finite`,
inequality `sb:log-square-sum`: `|P_2(y) − y((log y)² − 2 log y + 2)| ≤ (log y)² + 2` for
`P_2(y) = Σ_{n≤y} (log n)²`. With the packet's rational logarithm `λ_K(n) = H_{Kn} − H_K`, a common denominator
`F = L!` and `u_n = F λ_K(n) = S(Kn) ∸ S(K)` (`F²`-units), write `Q(N) = Σ_{n≤N} u_n²` and
`G(N) = N(u_N² − 2F u_N + 2F²)` (`F² · y((log y)² − 2 log y + 2)`):

* `log_square_sum`: for `N ≥ 1`, `−2F S(N) ≤ Q(N) − G(N) ≤ F u_N + 2 u_N S(N)`, i.e.
  `−2H_N ≤ P_2(N) − N(λ² − 2λ + 2) ≤ λ + 2λH_N` (`λ = λ_K(N)`), the packet's bound with `H_N ≤ λ + 1 + ⋯`.

One QF induction on `N = k + 1` (the step `0 → 1` is excluded: `λ(0)` is meaningless). The increment of
`G` is `G(N+1) − G(N) − u_{N+1}² = −Fδ − ε(u + u' − 2F)` with `δ = u' − u` and `ε = F − Nδ`; the step uses
`HarmonicLogSum.inc_lower` (`δ ≥ ⌊F/(N+1)⌋ = q`) and `HarmonicMertensLower.delta_le` (`Nδ ≤ F`, i.e.
`0 ≤ ε ≤ q`). The step certificates were found by exact polynomial residuals (`(N+1)q = F`,
`Q(N+1) = Q(N) + u'²`, `S(N+1) = S(N) + q`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB inst2_h)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (S_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertensLower (delta_le)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSum (inc_lower fact_quo)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (quo_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (pos_of_lt_zero)
open LeanProofs.IPRA.Analysis.Products (fact)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `u_N = F λ_K(N) = S(KN) ∸ S(K)`. -/
abbrev U (N K F : PTm n) : PTm n := monus (S (K * N) F) (S K F)

/-- `u_{k+1}` with parameter `z = (K, F)`. -/
abbrev uB : PTm 2 := monus (S (fstT (var 1) * succ (var 0)) (sndT (var 1))) (S (fstT (var 1)) (sndT (var 1)))
abbrev QB : PTm 2 := uB * uB

theorem inst2_QB (k z : PTm n) : inst2 QB k z =
    monus (S (fstT z * succ k) (sndT z)) (S (fstT z) (sndT z)) *
      monus (S (fstT z * succ k) (sndT z)) (S (fstT z) (sndT z)) := by simp [inst2]

/-- `Q(N) = Σ_{n≤N} u_n²`. -/
abbrev Qs (N K F : PTm n) : PTm n := ap2 (sumF QB) N (pairT K F)

theorem Q_succ (N K F : PTm n) : Γ ⊢[PRAAx] Qs (succ N) K F ≐ Qs N K F + U (succ N) K F * U (succ N) K F := by
  refine (sum_succ' QB N (pairT K F)).eqTrans (congrAdd (.eqRefl _) ?_)
  rw [inst2_QB]
  have e : Γ ⊢[PRAAx] monus (S (fstT (pairT K F) * succ N) (sndT (pairT K F))) (S (fstT (pairT K F)) (sndT (pairT K F)))
      ≐ U (succ N) K F :=
    congrMonus (congrAp2 (sumF hB) (congrMul (fst_pair _ _) (.eqRefl _)) (snd_pair _ _))
      (congrAp2 (sumF hB) (fst_pair _ _) (snd_pair _ _))
  exact congrMul e e

theorem S_succ (N F : PTm n) : Γ ⊢[PRAAx] S (succ N) F ≐ S N F + quo F (succ N) := by
  have s := sum_succ' (Γ := Γ) hB N F
  rw [inst2_h] at s
  exact s

/-- The invariant at `N = k + 1`: upper and lower bounds for `Q(N) − G(N)`. -/
abbrev J (k K L : PTm n) : Fm PTm n :=
  le (Qs (succ k) K (fact L) + two * (succ k * (fact L * U (succ k) K (fact L))))
      (succ k * (U (succ k) K (fact L) * U (succ k) K (fact L)) + two * (succ k * (fact L * fact L)) +
        fact L * U (succ k) K (fact L) + two * (U (succ k) K (fact L) * S (succ k) (fact L))) ⋏
    le (succ k * (U (succ k) K (fact L) * U (succ k) K (fact L)) + two * (succ k * (fact L * fact L)))
      (Qs (succ k) K (fact L) + two * (succ k * (fact L * U (succ k) K (fact L))) +
        two * (fact L * S (succ k) (fact L)))

abbrev Hq (k K L N0 : PTm n) : Fm PTm n := le one K ⋏ (le (K * N0) L ⋏ le (succ k) N0)

theorem j_zero (K L : PTm n) : Γ ⊢[PRAAx] J zero K L := by
  have q1 : Γ ⊢[PRAAx] K * succ zero ≐ K := by ipra_ring
  have eu := natEq ((congrMonus (congrAp2 (sumF hB) q1 (.eqRefl (fact L))) (.eqRefl _)).eqTrans
    (le_refl (S K (fact L))) : Γ ⊢[PRAAx] U (succ zero) K (fact L) ≐ zero)
  have eQs := natEq (Q_succ (Γ := Γ) zero K (fact L))
  have eQ0 := natEq (sum_zero (Γ := Γ) QB (pairT K (fact L)))
  have eS1 := natEq (S_succ (Γ := Γ) zero (fact L))
  have eS0 := natEq (sum_zero (Γ := Γ) hB (fact L))
  have eq1 := natEq (quo_eq (congrSucc (pred_succ _).eqSymm) (q := fact L) (r := zero)
    (by ipra_ring) (le_refl _) : Γ ⊢[PRAAx] quo (fact L) (succ zero) ≐ fact L)
  refine .andI ?_ ?_
  · ipra_le 2 * 𝔞 (fact L) * 𝔞 (fact L) with eQs + eQ0 + 𝔞 (fact L) * eu -
      2 * 𝔞 (S (succ zero) (fact L)) * eu
  · ipra_le 0 with -(eQs + eQ0) - 2 * 𝔞 (fact L) * eu - 2 * 𝔞 (fact L) * (eS1 + eS0 + eq1)

theorem j_step {k K L N0 : PTm n} (h : Γ ⊢[PRAAx] Hq (succ k) K L N0) (ih : Γ ⊢[PRAAx] J k K L) :
    Γ ⊢[PRAAx] J (succ k) K L := by
  have hK := Prf.andE₁ h
  have hL := Prf.andE₁ (Prf.andE₂ h)
  have hk := Prf.andE₂ (Prf.andE₂ h)
  have hKp := pos_of_lt_zero hK
  have hKL : Γ ⊢[PRAAx] le (K * succ (succ k)) L := le_trans (le_scale K hk) hL
  have hNL : Γ ⊢[PRAAx] le (succ (succ k)) L := by
    refine le_trans (le_of_eq_add (d := pred K * succ (succ k)) ?_) hKL
    ipra_lc (𝔞 k + 2) * natEq hKp
  have inc := inc_lower hKp hKL
  have dl := delta_le (Γ := Γ) (succ k) (fact L) hKp
  have m1 : Γ ⊢[PRAAx] le (S K (fact L)) (S (K * succ k) (fact L)) :=
    S_mono (fact L) (le_of_eq_add (d := K * k) (by ipra_ring))
  have m2 : Γ ⊢[PRAAx] le (S K (fact L)) (S (K * succ (succ k)) (fact L)) :=
    S_mono (fact L) (le_of_eq_add (d := K * succ k) (by ipra_ring))
  have ex := natEq (eq_add_of_le m1)
  have ex' := natEq (eq_add_of_le m2)
  have f2 : Γ ⊢[PRAAx] le (U (succ k) K (fact L) + quo (fact L) (succ (succ k))) (U (succ (succ k)) K (fact L)) := by
    ipra_le sl inc with ex' - ex
  have f3 : Γ ⊢[PRAAx] le (succ k * U (succ (succ k)) K (fact L)) (succ k * U (succ k) K (fact L) + fact L) := by
    ipra_le sl dl with (𝔞 k + 1) * (ex - ex')
  have eQ := natEq (Q_succ (Γ := Γ) (succ k) K (fact L))
  have eS := natEq (S_succ (Γ := Γ) (succ k) (fact L))
  have eF := natEq (fact_quo hNL)
  have a1 := le_scale (succ k * (U (succ k) K (fact L) + U (succ (succ k)) K (fact L))) f2
  have a2 := le_scale (quo (fact L) (succ (succ k))) f2
  have a3 := le_scale (two * fact L) f3
  have a4 := le_scale (two * S (succ k) (fact L)) f2
  have b1 := le_scale (fact L) f2
  have b2 := le_scale (U (succ k) K (fact L) + U (succ (succ k)) K (fact L)) f3
  have b3 := le_scale (two * (fact L * succ k)) f2
  refine .andI ?_ ?_
  · ipra_le sl (Prf.andE₁ ih) + sl a1 + sl a2 +
        𝔞 (quo (fact L) (succ (succ k))) * 𝔞 (quo (fact L) (succ (succ k))) + sl a3 + sl a4 +
        2 * 𝔞 (quo (fact L) (succ (succ k))) * 𝔞 (S (succ k) (fact L)) with
      eQ - 2 * 𝔞 (U (succ (succ k)) K (fact L)) * eS +
        (𝔞 (U (succ k) K (fact L)) + 𝔞 (U (succ (succ k)) K (fact L))) * eF
  · ipra_le sl (Prf.andE₂ ih) + sl b1 + 𝔞 (fact L) * 𝔞 (quo (fact L) (succ (succ k))) + sl b2 + sl b3 with
      -eQ - 2 * 𝔞 (fact L) * eS + 2 * 𝔞 (fact L) * eF

/-- Variables: `0 = k`, `1 = K`, `2 = L`, `3 = N0`. -/
private abbrev sqF : Fm PTm 4 := Hq (var 0) (var 1) (var 2) (var 3) ⟶ J (var 0) (var 1) (var 2)

private theorem sq₀ : ([] : List (Fm PTm 4)) ⊢[PRAAx] sqF := by
  ipra_ind (⟨⟨le_QF _ _, le_QF _ _, le_QF _ _⟩, le_QF _ _, le_QF _ _⟩) [subst_le, subst_ap2, subst_pairT]
  · exact .impI (j_zero _ _)
  · refine .impI ?_
    have h := (Prf.hyp0 : (Hq (succ (var 0)) (var 1) (var 2) (var 3) :: [sqF]) ⊢[PRAAx]
      Hq (succ (var 0)) (var 1) (var 2) (var 3))
    have h' : (Hq (succ (var 0)) (var 1) (var 2) (var 3) :: [sqF]) ⊢[PRAAx] Hq (var 0) (var 1) (var 2) (var 3) :=
      .andI (Prf.andE₁ h) (.andI (Prf.andE₁ (Prf.andE₂ h)) (le_trans (le_succ_self _) (Prf.andE₂ (Prf.andE₂ h))))
    exact j_step h (Prf.impE Prf.hyp1 h')

/-- `sb:log-square-sum` for the harmonic logarithm at `N = k + 1`:
`−2F S(N) ≤ Q(N) − G(N) ≤ F u_N + 2 u_N S(N)` for `K ≥ 1`, `KN ≤ L`, `F = L!`. -/
theorem log_square_sum {k K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hL : Γ ⊢[PRAAx] le (K * succ k) L) :
    Γ ⊢[PRAAx] J k K L := by
  have i := inst (Γ := Γ) sq₀ (![k, K, L, succ k] : Fin 4 → PTm n)
  simp at i
  exact Prf.impE i (.andI hK (.andI hL (le_refl _)))

end LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum
