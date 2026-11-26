import IPRADerivations.DiophantineNumberTheory.KhinchinMoment
import IPRADerivations.DiophantineNumberTheory.FractionCount
import IPRADerivations.AnalyticNumberTheory.SumReindex
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.SubstCommand

/-!
# The per-pair and geometric estimates of the Khinchin block (`hurwitz_khinchin_ipra`, (K9)–(K11))

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, (K9)–(K10): "Sum this over the disjoint
intervals of `E_k(J)` … We used only `2Σ_{k<ℓ} t_k t_ℓ ≤ S²` and the finite geometric sum
`Σ_{k<ℓ} 4^{k−ℓ} ≤ 1/3`."

* `s_facts`: the separation `s = ⌊T/Q²⌋` of a scale with `Q² ≤ T` satisfies `Q²s ≤ T ≤ 2Q²s`, `s ≥ 1`, and
  `4w ≤ s` when `4Q²w ≤ T` (`t ≤ 1`);
* `pair_arith`: from `KhinchinOverlap.overlap_bound` (`I ≤ w_ℓ(⌊(w_k + w_ℓ)/s⌋ + 1) N_k`) and the (K3) count
  `βN_k ≤ 2DQ_k²`: `3βT I ≤ 12D u_k u_ℓ + 15D u_ℓ Q_k² s` (`u = Q²w`), one `ipra_le` certificate;
* `geo2`: for `Q_k = 2^{K₀+k}`, `3 Σ_{k<J} Q_k² + Q_0² = Q_J²`, so `3 Σ_{k<ℓ} Q_k² ≤ Q_ℓ²`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlockGeo

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (le_quo_of_mul_le)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The separation `s = ⌊T/Q²⌋`: `Q²s ≤ T ≤ 2Q²s` and `s ≥ 1` for `1 ≤ Q² ≤ T`. -/
theorem s_facts {Q T : PTm n} (hQ : Γ ⊢[PRAAx] Q * Q ≐ succ (pred (Q * Q))) (hT : Γ ⊢[PRAAx] le (Q * Q) T) :
    Γ ⊢[PRAAx] le (Q * Q * quo T (Q * Q)) T ⋏
      (le T (two * (Q * Q) * quo T (Q * Q)) ⋏ (quo T (Q * Q) ≐ succ (pred (quo T (Q * Q))))) := by
  have dm := div_mod_at (Γ := Γ) (x := T) hQ
  have e := natEq (Prf.andE₁ dm)
  have hr : Γ ⊢[PRAAx] lt (rem T (Q * Q)) (Q * Q) := Prf.andE₂ dm
  have hs1 : Γ ⊢[PRAAx] le one (quo T (Q * Q)) := le_quo_of_mul_le hQ (by ipra_le sl hT)
  have hpos := FractionCount.pos_of_le_one hs1
  refine .andI (by ipra_le 𝔞 (rem T (Q * Q)) with e) (.andI ?_ hpos)
  ipra_le sl hr + 𝔞 (Q * Q) * sl hs1 + 1 with e

/-- `4Q²w ≤ T` gives `4w ≤ ⌊T/Q²⌋`. -/
theorem w_le_s {Q T w : PTm n} (hQ : Γ ⊢[PRAAx] Q * Q ≐ succ (pred (Q * Q)))
    (hw : Γ ⊢[PRAAx] le (num 4 * (Q * Q) * w) T) : Γ ⊢[PRAAx] le (num 4 * w) (quo T (Q * Q)) :=
  le_quo_of_mul_le hQ (by ipra_le sl hw)

/-- One ordered pair `k < ℓ`: `3βT I ≤ 12D u_k u_ℓ + 15D u_ℓ Q_k² s`. -/
theorem pair_arith {I wk wl fl s N D β T Qk Ql : PTm n}
    (ho : Γ ⊢[PRAAx] le I (wl * succ fl * N)) (hfl : Γ ⊢[PRAAx] le (s * fl) (wk + wl))
    (hN : Γ ⊢[PRAAx] le (β * N) (num 2 * D * (Qk * Qk))) (hws : Γ ⊢[PRAAx] le (num 4 * wl) s)
    (hTs : Γ ⊢[PRAAx] le T (two * (Ql * Ql) * s)) :
    Γ ⊢[PRAAx] le (num 3 * β * T * I)
      (num 12 * D * (Qk * Qk * wk) * (Ql * Ql * wl) + num 15 * D * (Ql * Ql * wl) * (Qk * Qk) * s) := by
  ipra_le 3 * 𝔞 D * 𝔞 Qk * 𝔞 Qk * 𝔞 Ql * 𝔞 Ql * 𝔞 wl * sl hws +
    12 * 𝔞 D * 𝔞 Qk * 𝔞 Qk * 𝔞 Ql * 𝔞 Ql * 𝔞 wl * sl hfl +
    6 * 𝔞 D * 𝔞 Qk * 𝔞 Qk * 𝔞 wl * (𝔞 fl + 1) * sl hTs +
    3 * 𝔞 T * 𝔞 wl * (𝔞 fl + 1) * sl hN + 3 * 𝔞 β * 𝔞 T * sl ho

/-! ## The geometric sum of the squared scales -/

/-- `Q_k² = 2^{K₀+k} 2^{K₀+k}` over `0 = k`, `1 = K₀`. -/
abbrev q2B : PTm 2 := pw two (var 1 + var 0) * pw two (var 1 + var 0)

theorem inst2_q2B (k K0 : PTm n) : inst2 q2B k K0 = pw two (K0 + k) * pw two (K0 + k) := by
  simp [inst2]

theorem congrPw2 {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] pw two a ≐ pw two b := by
  ipra_congr (pw two (var 0) : PTm 1) with [h]

/-- The invariant of `geo2`. -/
def g2Inv (J K0 : PTm n) : Fm PTm n :=
  num 3 * ap2 (sumF q2B) J K0 + pw two K0 * pw two K0 ≐ pw two (K0 + J) * pw two (K0 + J)

ipra_subst g2Inv [subst_ap2]

/-- `3 Σ_{k<J} Q_k² + Q_0² = Q_J²` for `Q_k = 2^{K₀+k}`. -/
theorem geo2 (J K0 : PTm n) :
    Γ ⊢[PRAAx] num 3 * ap2 (sumF q2B) J K0 + pw two K0 * pw two K0 ≐ pw two (K0 + J) * pw two (K0 + J) := by
  have hall : Γ ⊢[PRAAx] Fm.all (g2Inv (var 0) (Syn.shift K0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · rw [subst_g2Inv]
      simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      show Γ ⊢[PRAAx] num 3 * ap2 (sumF q2B) zero K0 + pw two K0 * pw two K0 ≐ pw two (K0 + zero) * pw two (K0 + zero)
      have a := natEq (sum_zero (Γ := Γ) q2B K0)
      have hz : Γ ⊢[PRAAx] pw two (K0 + zero) ≐ pw two K0 := congrPw2 (add_zero _)
      ipra_lc 3 * a - (𝔞 (pw two (K0 + zero)) + 𝔞 (pw two K0)) * natEq hz
    · rw [subst_g2Inv]
      simp only [Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      let Δ : List (Fm PTm (n + 1)) := g2Inv (var 0) (Syn.shift K0) :: Γ.map Fm.shift
      have e0 := natEq (Prf.hyp0 : Δ ⊢[PRAAx] num 3 * ap2 (sumF q2B) (var 0) (Syn.shift K0) +
        pw two (Syn.shift K0) * pw two (Syn.shift K0) ≐ pw two (Syn.shift K0 + var 0) * pw two (Syn.shift K0 + var 0))
      have e1 := natEq (sum_succ' (Γ := Δ) q2B (var 0) (Syn.shift K0))
      rw [inst2_q2B] at e1
      have hs : Δ ⊢[PRAAx] Syn.shift K0 + succ (var 0) ≐ succ (Syn.shift K0 + var 0) := by
        ipra_ring
      show Δ ⊢[PRAAx] num 3 * ap2 (sumF q2B) (succ (var 0)) (Syn.shift K0) + pw two (Syn.shift K0) * pw two (Syn.shift K0) ≐
        pw two (Syn.shift K0 + succ (var 0)) * pw two (Syn.shift K0 + succ (var 0))
      ipra_lc e0 + 3 * e1 -
        (𝔞 (pw two (Syn.shift K0 + succ (var 0))) + 2 * 𝔞 (pw two (Syn.shift K0 + var 0))) * natEq ((congrPw2 hs).eqTrans (pw_succ (Γ := Δ) two (Syn.shift K0 + var 0)))
  have a := Prf.allE J hall
  rw [subst_g2Inv] at a
  simp only [Syn.subst_inst_shift] at a
  exact a

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlockGeo
