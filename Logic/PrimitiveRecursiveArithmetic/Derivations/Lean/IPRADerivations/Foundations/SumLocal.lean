import IPRADerivations.Foundations.AuxiliaryEnvelope
import IPRADerivations.Core.SumSplit
import IPRADerivations.Core.OrderCertificates

/-!
# Support localization of finite sums (`hurwitz_khinchin_ipra`, the (K11) count inside a gap)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`: the (K11) block constructed in a gap
covers only cells of that gap ("All added intervals are inside the gap in which they were constructed"), so its
measure over the whole grid is its measure over the gap. Generically:

* `sum_zero_of`: a sum of terms that all vanish is `0`;
* `sum_local`: if `f(c) = 0` for `c < L` and for `H ≤ c < N` (with `L ≤ H ≤ N`), then
  `Σ_{c<N} f(c) = Σ_{k<H−L} f(L + k)` — two splits (`Core.SumSplit.sum_split`) and two vanishing sums.

With `KhinchinBlockLocal.block_out` this turns `KhinchinBlock.block_cover`'s count over the whole grid into the
count over the cell's own fine cells, the hypothesis of `KhinchinRoundBits.cell_cov`.
-/

namespace LeanProofs.IPRA.Foundations.SumLocal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.AuxiliaryEnvelope (sum_le_const)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- A sum of vanishing terms vanishes. -/
theorem sum_zero_of (f : PTm 2) {N x : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ inst2 f (var 0) (Syn.shift x) ≐ zero)) :
    Γ ⊢[PRAAx] ap2 (sumF f) N x ≐ zero := by
  have s : Γ ⊢[PRAAx] le (ap2 (sumF f) N x) (N * zero) := by
    refine sum_le_const f (.allI (.impI ?_))
    rw [show Syn.shift (zero : PTm n) = zero by simp [Syn.shift]]
    exact (monus_zero _).eqTrans (Prf.impE (h.allOpen.wk (ψ := lt (var 0) (Syn.shift N))) Prf.hyp0)
  have h0 : Γ ⊢[PRAAx] le (N * zero) zero := by ipra_le 0
  exact (monus_zero _).eqSymm.eqTrans (le_trans s h0)

/-- Support localization: `f` vanishing below `L` and on `[H, N)` gives `Σ_{c<N} f = Σ_{k<H−L} f(L + k)`. -/
theorem sum_local (f : PTm 2) {L H N x : PTm n} (hLH : Γ ⊢[PRAAx] le L H) (hHN : Γ ⊢[PRAAx] le H N)
    (hlo : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift L) ⟶ inst2 f (var 0) (Syn.shift x) ≐ zero))
    (hhi : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (monus N H)) ⟶
      inst2 f (Syn.shift H + var 0) (Syn.shift x) ≐ zero)) :
    Γ ⊢[PRAAx] ap2 (sumF f) N x ≐ ap2 (sumF (offB f)) (monus H L) (pairT L x) := by
  have e1 := eq_add_of_le hLH
  have e2 := eq_add_of_le hHN
  have eN : Γ ⊢[PRAAx] N ≐ L + (monus H L + monus N H) := by
    have a := natEq e1; have b := natEq e2
    apply deriveNat; ipra_simps; linear_combination b + a
  have s1 := (congrAp2 (sumF f) eN (.eqRefl x)).eqTrans (sum_split f L (monus H L + monus N H) x)
  have s2 := sum_split (Γ := Γ) (offB f) (monus H L) (monus N H) (pairT L x)
  have z1 := sum_zero_of f hlo
  have e1s0 : Γ.map Fm.shift ⊢[PRAAx] Syn.shift H ≐ Syn.shift L + Syn.shift (monus H L) := by
    simpa [Fm.shift, Syn.shift] using e1.shift
  have z2 : Γ ⊢[PRAAx] ap2 (sumF (offB (offB f))) (monus N H) (pairT (monus H L) (pairT L x)) ≐ zero := by
    refine sum_zero_of _ (.allI (.impI ?_))
    have e1s : (lt (var 0) (Syn.shift (monus N H)) :: Γ.map Fm.shift) ⊢[PRAAx]
        Syn.shift H ≐ Syn.shift L + Syn.shift (monus H L) := e1s0.wk
    have p := Prf.impE (hhi.allOpen.wk (ψ := lt (var 0) (Syn.shift (monus N H)))) Prf.hyp0
    rw [show Syn.shift (pairT (monus H L) (pairT L x)) =
        pairT (Syn.shift (monus H L)) (pairT (Syn.shift L) (Syn.shift x)) by simp [Syn.shift],
      inst2_offB, inst2_offB]
    have ef := fst_pair (Γ := lt (var 0) (Syn.shift (monus N H)) :: Γ.map Fm.shift)
      (Syn.shift (monus H L)) (pairT (Syn.shift L) (Syn.shift x))
    have es := snd_pair (Γ := lt (var 0) (Syn.shift (monus N H)) :: Γ.map Fm.shift)
      (Syn.shift (monus H L)) (pairT (Syn.shift L) (Syn.shift x))
    have ei : (lt (var 0) (Syn.shift (monus N H)) :: Γ.map Fm.shift) ⊢[PRAAx]
        fstT (sndT (pairT (Syn.shift (monus H L)) (pairT (Syn.shift L) (Syn.shift x)))) +
            (fstT (pairT (Syn.shift (monus H L)) (pairT (Syn.shift L) (Syn.shift x))) + var 0) ≐
          Syn.shift H + var 0 := by
      have a := natEq ((congrFst es).eqTrans (fst_pair _ _))
      have b := natEq ef
      have c := natEq e1s
      apply deriveNat; ipra_simps; linear_combination a + b - c
    exact (congrInst2 f ei ((congrSnd es).eqTrans (snd_pair _ _))).eqTrans p
  have a1 := natEq s1; have a2 := natEq s2; have a3 := natEq z1; have a4 := natEq z2
  apply deriveNat; ipra_simps; linear_combination a1 + a2 + a3 + a4

end LeanProofs.IPRA.Foundations.SumLocal
