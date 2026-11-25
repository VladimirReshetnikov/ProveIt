import IPRADerivations.Foundations.ShiftedInduction
import IPRADerivations.Combinatorics.BinomialSigned
import IPRADerivations.Analysis.Pochhammer
import IPRADerivations.Foundations.HurwitzProduct
import IPRADerivations.Core.CertificateTactics

/-!
# The Chu–Vandermonde summation

Packet: `analysis/hypergeometric_ipra_2026-11-16`, Theorem `thm:vandermonde` ("Chu–Vandermonde"):
"For `m ∈ ℕ`, under the finite denominator guards, `₂F₁(−m, b; c; 1) = (c − b)_m / (c)_m`. This is a
[finite] theorem: no convergence or gamma function is involved", proved by induction on `m` "uniformly in
`b, c`" from `S_{m+1}(b, c) = S_m(b, c) − (b/c) S_m(b + 1, c + 1)`.

For natural parameters `b` and `c = b + d`, multiplied by `(c)_m = (c)_k (c + k)_{m−k}` and with
`(−m)_k / k! = (−1)^k C(m, k)` (`Analysis/TerminatingSeries`), the statement is

`∑_{k ≤ m} (−1)^k C(m, k) (b)_k (b + d + k)_{m−k} = (d)_m`.

The signed sum is kept as its even and odd parts.

* `vE`, `vO`: the bodies `[k even] (b)_k (b + d + k)_{M−k}` and `[k odd] …` with the parameter
  `⟨M, ⟨b, d⟩⟩`; `TE m b d`, `TO m b d`: the two parts of the sum at level `M = m`;
* `poch_top`: `(c + k)_{m+1−k} = (c + k)_{m−k} (c + m)` for `k ≤ m`;
* `raise_pt`, `index_pt`: the two termwise identities, raising the level and shifting the index (which
  moves `b` to `b + 1` and exchanges the parities);
* `TE_succ`, `TO_succ`: `T⁺_{m+1}(b) = (b + d + m) T⁺_m(b) + b T⁻_m(b + 1)` and its mirror, i.e. the
  paper's recurrence multiplied by `(c)_{m+1}`, from the Pascal step of `Combinatorics/BinomialSigned`;
* `chu_vandermonde`: `T⁺_m(b, d) = T⁻_m(b, d) + (d)_m` for all `m`, `b`, `d`.

The step uses the hypothesis at `b + 1`, so the induction is `shifted_induction` of
`Foundations/ShiftedInduction`. The division by `(c)_m` and the hypergeometric notation are the reading
of the statement.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.ChuVandermonde

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_zero')
open LeanProofs.IPRA.Combinatorics.BinomialSigned (cB cS cB_at cS_at pascal_sum)
open LeanProofs.IPRA.Analysis.Pochhammer (poch poch_zero poch_succ poch_shift')
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (zero_ne_one' congrEqb')
open LeanProofs.IPRA.Foundations.HurwitzProduct (succ_monus_of_le)
open LeanProofs.IPRA.Foundations.ShiftedInduction (shifted_induction)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem congrPoch {x x' m m' : PTm n} (h₁ : Γ ⊢[PRAAx] x ≐ x') (h₂ : Γ ⊢[PRAAx] m ≐ m') :
    Γ ⊢[PRAAx] poch x m ≐ poch x' m' := by
  have h := Prf.eqCongr (Γ := Γ) (poch (var 0) (var 1) : PTm 2) (σ := ![x, m]) (σ' := ![x', m'])
    (fun j => by fin_cases j <;> assumption)
  simpa using h

/-! ## The terms -/

/-- `(b)_k (b + d + k)_{M−k}`; variables `0 = k`, `1 = y = ⟨M, ⟨b, d⟩⟩`. -/
def vB : PTm 2 :=
  poch (fstT (sndT (var 1))) (var 0) *
    poch (fstT (sndT (var 1)) + sndT (sndT (var 1)) + var 0) (monus (fstT (var 1)) (var 0))

/-- `[k even] (b)_k (b + d + k)_{M−k}`. -/
def vE : PTm 2 := eqb (rem (var 0) two) zero * vB
/-- `[k odd] (b)_k (b + d + k)_{M−k}`. -/
def vO : PTm 2 := eqb (rem (var 0) two) one * vB

theorem inst2_vB (k y : PTm n) :
    inst2 vB k y = poch (fstT (sndT y)) k *
      poch (fstT (sndT y) + sndT (sndT y) + k) (monus (fstT y) k) := by
  simp [inst2, vB]

theorem inst2_vE (k y : PTm n) : inst2 vE k y = eqb (rem k two) zero * inst2 vB k y := by
  simp [inst2, vE]

theorem inst2_vO (k y : PTm n) : inst2 vO k y = eqb (rem k two) one * inst2 vB k y := by
  simp [inst2, vO]

theorem vB_at (k M b d : PTm n) :
    Γ ⊢[PRAAx] inst2 vB k (pairT M (pairT b d)) ≐ poch b k * poch (b + d + k) (monus M k) := by
  rw [inst2_vB]
  have hb : Γ ⊢[PRAAx] fstT (sndT (pairT M (pairT b d))) ≐ b :=
    (congrFst (snd_pair M (pairT b d))).eqTrans (fst_pair b d)
  have hd : Γ ⊢[PRAAx] sndT (sndT (pairT M (pairT b d))) ≐ d :=
    (congrSnd (snd_pair M (pairT b d))).eqTrans (snd_pair b d)
  exact congrMul (congrPoch hb (.eqRefl k))
    (congrPoch (congrAdd (congrAdd hb hd) (.eqRefl k)) (congrMonus (fst_pair M _) (.eqRefl k)))

/-- `(c + k)_{m+1−k} = (c + k)_{m−k} (c + m)` for `k ≤ m`. -/
theorem poch_top {k m c : PTm n} (h : Γ ⊢[PRAAx] le k m) :
    Γ ⊢[PRAAx] poch (c + k) (monus (succ m) k) ≐ poch (c + k) (monus m k) * (c + m) := by
  have t : Γ ⊢[PRAAx] c + k + monus m k ≐ c + m := by
    ipra_lc -natEq (eq_add_of_le h)
  exact ((congrPoch (.eqRefl (c + k)) (succ_monus_of_le h)).eqTrans (poch_succ (c + k) (monus m k))).eqTrans
    (congrMul (.eqRefl _) t)

/-- Raising the level: `v_{m+1}(k; b, d) = (b + d + m) v_m(k; b, d)` for `k ≤ m`. -/
theorem raise_vB {k m b d : PTm n} (hk : Γ ⊢[PRAAx] lt k (succ m)) :
    Γ ⊢[PRAAx] inst2 vB k (pairT (succ m) (pairT b d)) ≐
      (b + d + m) * inst2 vB k (pairT m (pairT b d)) := by
  have hk' : Γ ⊢[PRAAx] le k m := (succ_monus_succ k m).eqSymm.eqTrans hk
  ipra_lc natEq (vB_at (Γ := Γ) k (succ m) b d) - (𝔟 b + 𝔟 d + 𝔟 m) * natEq (vB_at (Γ := Γ) k m b d) +
    𝔟(poch b k) * natEq (poch_top (c := b + d) hk')

/-- Shifting the index: `v_{m+1}(k + 1; b, d) = b v_m(k; b + 1, d)`. -/
theorem index_vB (k m b d : PTm n) :
    Γ ⊢[PRAAx] inst2 vB (succ k) (pairT (succ m) (pairT b d)) ≐
      b * inst2 vB k (pairT m (pairT (succ b) d)) := by
  have s : Γ ⊢[PRAAx] b + d + succ k ≐ succ b + d + k := by
    ipra_ring
  ipra_lc natEq (vB_at (Γ := Γ) (succ k) (succ m) b d) - 𝔟 b * natEq (vB_at (Γ := Γ) k m (succ b) d) +
    𝔟(poch (b + d + succ k) (monus (succ m) (succ k))) * natEq (poch_shift' (Γ := Γ) b k) +
    𝔟 b * 𝔟(poch (succ b) k) * natEq (congrPoch s (succ_monus_succ (Γ := Γ) m k))

/-! ## The two parts of the sum -/

/-- `T⁺_m(b, d) = ∑_{k ≤ m} [k even] C(m, k) (b)_k (b + d + k)_{m−k}`. -/
abbrev TE (m b d : PTm n) : PTm n := ap2 (sumF (cB vE)) (succ m) (pairT m (pairT m (pairT b d)))
/-- `T⁻_m(b, d) = ∑_{k ≤ m} [k odd] C(m, k) (b)_k (b + d + k)_{m−k}`. -/
abbrev TO (m b d : PTm n) : PTm n := ap2 (sumF (cB vO)) (succ m) (pairT m (pairT m (pairT b d)))

theorem raise_pt_E {k m b d : PTm n} (hk : Γ ⊢[PRAAx] lt k (succ m)) :
    Γ ⊢[PRAAx] inst2 (cB vE) k (pairT m (pairT (succ m) (pairT b d))) ≐
      (b + d + m) * inst2 (cB vE) k (pairT m (pairT m (pairT b d))) := by
  have c₁ := cB_at (Γ := Γ) vE k m (pairT (succ m) (pairT b d))
  have c₀ := cB_at (Γ := Γ) vE k m (pairT m (pairT b d))
  rw [inst2_vE] at c₁ c₀
  ipra_lc natEq c₁ - (𝔟 b + 𝔟 d + 𝔟 m) * natEq c₀ +
    𝔟(binom m k) * 𝔟(eqb (rem k two) zero) * natEq (raise_vB (b := b) (d := d) hk)

theorem raise_pt_O {k m b d : PTm n} (hk : Γ ⊢[PRAAx] lt k (succ m)) :
    Γ ⊢[PRAAx] inst2 (cB vO) k (pairT m (pairT (succ m) (pairT b d))) ≐
      (b + d + m) * inst2 (cB vO) k (pairT m (pairT m (pairT b d))) := by
  have c₁ := cB_at (Γ := Γ) vO k m (pairT (succ m) (pairT b d))
  have c₀ := cB_at (Γ := Γ) vO k m (pairT m (pairT b d))
  rw [inst2_vO] at c₁ c₀
  ipra_lc natEq c₁ - (𝔟 b + 𝔟 d + 𝔟 m) * natEq c₀ +
    𝔟(binom m k) * 𝔟(eqb (rem k two) one) * natEq (raise_vB (b := b) (d := d) hk)

theorem index_pt_E (k m b d : PTm n) :
    Γ ⊢[PRAAx] inst2 (cS vE) k (pairT m (pairT (succ m) (pairT b d))) ≐
      b * inst2 (cB vO) k (pairT m (pairT m (pairT (succ b) d))) := by
  have c₁ := cS_at (Γ := Γ) vE k m (pairT (succ m) (pairT b d))
  have c₀ := cB_at (Γ := Γ) vO k m (pairT m (pairT (succ b) d))
  rw [inst2_vE] at c₁; rw [inst2_vO] at c₀
  ipra_lc natEq c₁ - 𝔟 b * natEq c₀ +
    𝔟(binom m k) * 𝔟(inst2 vB (succ k) (pairT (succ m) (pairT b d))) * natEq (Prf.andE₁ (LeanProofs.IPRA.AnalyticNumberTheory.Mobius.par_succ (Γ := Γ) k)) +
    𝔟(binom m k) * 𝔟(eqb (rem k two) one) * natEq (index_vB (Γ := Γ) k m b d)

theorem index_pt_O (k m b d : PTm n) :
    Γ ⊢[PRAAx] inst2 (cS vO) k (pairT m (pairT (succ m) (pairT b d))) ≐
      b * inst2 (cB vE) k (pairT m (pairT m (pairT (succ b) d))) := by
  have c₁ := cS_at (Γ := Γ) vO k m (pairT (succ m) (pairT b d))
  have c₀ := cB_at (Γ := Γ) vE k m (pairT m (pairT (succ b) d))
  rw [inst2_vO] at c₁; rw [inst2_vE] at c₀
  ipra_lc natEq c₁ - 𝔟 b * natEq c₀ +
    𝔟(binom m k) * 𝔟(inst2 vB (succ k) (pairT (succ m) (pairT b d))) * natEq (Prf.andE₂ (LeanProofs.IPRA.AnalyticNumberTheory.Mobius.par_succ (Γ := Γ) k)) +
    𝔟(binom m k) * 𝔟(eqb (rem k two) zero) * natEq (index_vB (Γ := Γ) k m b d)

theorem shift_params (m b d : PTm n) :
    Syn.shift (pairT m (pairT (succ m) (pairT b d))) =
        pairT (Syn.shift m) (pairT (succ (Syn.shift m)) (pairT (Syn.shift b) (Syn.shift d))) ∧
      Syn.shift (pairT m (pairT m (pairT b d))) =
        pairT (Syn.shift m) (pairT (Syn.shift m) (pairT (Syn.shift b) (Syn.shift d))) ∧
      Syn.shift (pairT m (pairT m (pairT (succ b) d))) =
        pairT (Syn.shift m) (pairT (Syn.shift m) (pairT (succ (Syn.shift b)) (Syn.shift d))) ∧
      Syn.shift (b + d + m) = Syn.shift b + Syn.shift d + Syn.shift m ∧
      Syn.shift (succ m) = succ (Syn.shift m) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Syn.shift]

/-- `T⁺_{m+1}(b) = (b + d + m) T⁺_m(b) + b T⁻_m(b + 1)`. -/
theorem TE_succ (m b d : PTm n) :
    Γ ⊢[PRAAx] TE (succ m) b d ≐ (b + d + m) * TE m b d + b * TO m (succ b) d := by
  obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := shift_params m b d
  have p := pascal_sum (Γ := Γ) vE m (pairT (succ m) (pairT b d))
  have r : Γ ⊢[PRAAx] ap2 (sumF (cB vE)) (succ m) (pairT m (pairT (succ m) (pairT b d))) ≐
      (b + d + m) * TE m b d := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [e₁, e₂, e₄, e₅]
    exact raise_pt_E Prf.hyp0
  have s : Γ ⊢[PRAAx] ap2 (sumF (cS vE)) (succ m) (pairT m (pairT (succ m) (pairT b d))) ≐
      b * TO m (succ b) d := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [e₁, e₃]
    exact index_pt_E _ _ _ _
  exact p.eqTrans (congrAdd r s)

/-- `T⁻_{m+1}(b) = (b + d + m) T⁻_m(b) + b T⁺_m(b + 1)`. -/
theorem TO_succ (m b d : PTm n) :
    Γ ⊢[PRAAx] TO (succ m) b d ≐ (b + d + m) * TO m b d + b * TE m (succ b) d := by
  obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := shift_params m b d
  have p := pascal_sum (Γ := Γ) vO m (pairT (succ m) (pairT b d))
  have r : Γ ⊢[PRAAx] ap2 (sumF (cB vO)) (succ m) (pairT m (pairT (succ m) (pairT b d))) ≐
      (b + d + m) * TO m b d := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [e₁, e₂, e₄, e₅]
    exact raise_pt_O Prf.hyp0
  have s : Γ ⊢[PRAAx] ap2 (sumF (cS vO)) (succ m) (pairT m (pairT (succ m) (pairT b d))) ≐
      b * TE m (succ b) d := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [e₁, e₃]
    exact index_pt_O _ _ _ _
  exact p.eqTrans (congrAdd r s)

/-! ## The summation -/

theorem cv_base (b d : PTm n) : Γ ⊢[PRAAx] TE zero b d ≐ TO zero b d + poch d zero := by
  have r0 : Γ ⊢[PRAAx] rem (zero : PTm n) two ≐ zero := rem_zero _
  have ev := natEq ((congrEqb' r0 (.eqRefl _)).eqTrans (eqb_of_eq (.eqRefl _)) :
    Γ ⊢[PRAAx] eqb (rem zero two) zero ≐ one)
  have od := natEq ((congrEqb' r0 (.eqRefl _)).eqTrans (eqb_of_ne zero_ne_one') :
    Γ ⊢[PRAAx] eqb (rem zero two) one ≐ zero)
  have cE := cB_at (Γ := Γ) vE zero zero (pairT zero (pairT b d))
  have cO := cB_at (Γ := Γ) vO zero zero (pairT zero (pairT b d))
  rw [inst2_vE] at cE; rw [inst2_vO] at cO
  ipra_lc natEq (sum_succ' (Γ := Γ) (cB vE) zero (pairT zero (pairT zero (pairT b d)))) +
    natEq (sum_zero (Γ := Γ) (cB vE) (pairT zero (pairT zero (pairT b d)))) + natEq cE -
    natEq (sum_succ' (Γ := Γ) (cB vO) zero (pairT zero (pairT zero (pairT b d)))) -
    natEq (sum_zero (Γ := Γ) (cB vO) (pairT zero (pairT zero (pairT b d)))) - natEq cO -
    natEq (poch_zero (Γ := Γ) d) +
    𝔟(binom (zero : PTm n) zero) * 𝔟(inst2 vB zero (pairT zero (pairT b d))) * (ev - od) +
    𝔟(inst2 vB zero (pairT zero (pairT b d))) * natEq (binom_zero' (Γ := Γ) (zero : PTm n)) +
    natEq (vB_at (Γ := Γ) zero zero b d) + 𝔟(poch (b + d + zero) (monus zero zero)) * natEq (poch_zero (Γ := Γ) b) +
    natEq ((congrPoch (.eqRefl (b + d + zero)) (monus_self (Γ := Γ) (zero : PTm n))).eqTrans (poch_zero (b + d + zero)))

theorem cv_step {m b d : PTm n}
    (h₀ : Γ ⊢[PRAAx] TE m b d ≐ TO m b d + poch d m)
    (h₁ : Γ ⊢[PRAAx] TE m (succ b) d ≐ TO m (succ b) d + poch d m) :
    Γ ⊢[PRAAx] TE (succ m) b d ≐ TO (succ m) b d + poch d (succ m) := by
  ipra_lc natEq (TE_succ (Γ := Γ) m b d) - natEq (TO_succ (Γ := Γ) m b d) - natEq (poch_succ (Γ := Γ) d m) +
    (𝔟 b + 𝔟 d + 𝔟 m) * natEq h₀ - 𝔟 b * natEq h₁

/-- The two sides as terms in `0 = m`, `1 = b`, `2 = d`. -/
def LT : PTm 3 := TE (var 0) (var 1) (var 2)
def RT : PTm 3 := TO (var 0) (var 1) (var 2) + poch (var 2) (var 0)

theorem inst3_LT (m b d : PTm n) : inst3 LT m b d = TE m b d := by
  simp [inst3, LT]

theorem inst3_RT (m b d : PTm n) : inst3 RT m b d = TO m b d + poch d m := by
  simp [inst3, RT]

/-- `thm:vandermonde`: `∑_{k ≤ m} (−1)^k C(m, k) (b)_k (b + d + k)_{m−k} = (d)_m`, i.e.
`(c)_m · ₂F₁(−m, b; c; 1) = (c − b)_m` with `c = b + d`, the signed sum by its even and odd parts. -/
theorem chu_vandermonde (m b d : PTm n) : Γ ⊢[PRAAx] TE m b d ≐ TO m b d + poch d m := by
  have h := shifted_induction (Γ := Γ) (L := LT) (R := RT)
    (by rw [inst3_LT, inst3_RT]; exact cv_base _ _)
    (by
      rw [inst3_LT, inst3_RT, inst3_LT, inst3_RT, inst3_LT, inst3_RT]
      exact .impI (.impI (cv_step Prf.hyp1 Prf.hyp0)))
    m b d
  rw [inst3_LT, inst3_RT] at h
  exact h

end LeanProofs.IPRA.Analysis.ChuVandermonde
