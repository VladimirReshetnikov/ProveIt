import IPRADerivations.Foundations.FrontierSoundness
import IPRADerivations.Foundations.ChainViability
import IPRADerivations.Combinatorics.CatalanConvolution
import IPRADerivations.Combinatorics.StirlingPowers
import IPRADerivations.Combinatorics.BinomialIdentities
import IPRADerivations.Core.SumReflect
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.LinearCombination

/-!
# Finite-support moment determinacy: uniqueness by back substitution

Packet: `probability/expected_value_ipra_2026-11-16`, Theorem `thm:moment-determinacy` ("Finite-support
moment determinacy"), the triangular step of its proof: with the factorial moments
`f_r = ∑_{k=r}^{B} (k)_r p_k`, "this is upper triangular, with diagonal `(r)_r = r! > 0`. Recover the
masses by back substitution".

The general statement: two sequences `P`, `Q` that satisfy the same triangular system

`∑_{i<d} c(i, ⟨d, x⟩) P(i, x) + D(d, x) P(d, x) = ∑_{i<d} c(i, ⟨d, x⟩) Q(i, x) + D(d, x) Q(d, x)`

for all `d ≤ B`, with positive diagonal `D(d, x)`, agree at every `d ≤ B`.

* `adB P Q`: the absolute difference `(P ∸ Q) + (Q ∸ P)`; the induction is on the quantifier-free
  equation `∑_{i<J} |P(i) − Q(i)| = 0`;
* `agree_pt`: that equation gives `P(i, x) = Q(i, x)` for `i < J`;
* `tB c P`: the body `c(i, y) · P(i, snd y)`; `sum_agree`: the two partial sums of the system agree;
* `back_step`: the back-substitution step, by cancelling the positive diagonal;
* `back_unique`: `P(d, x) = Q(d, x)` for `d ≤ B`.

The instance of the theorem, with the masses read from the top, `P(i) = p(B − i)`, `B = fst x`:

* `rvB p`, `fcB`, `fdB`: the reversed masses, the coefficients `(B − i)_{B − d}` and the diagonal
  `(B − d)!`;
* `moment_determinacy`: if `∑_{i<d} (B − i)_{B−d} p(B − i) + (B − d)! p(B − d)` agrees for `p` and `q`
  for every `d ≤ B` (equal factorial moments `f_{B−d}`), then `p(k, x) = q(k, x)` for all `k ≤ B`.

The passage between ordinary and factorial moments by the Stirling transformations
(`Combinatorics/StirlingPowers`) and the explicit rational recovery of the masses are not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.MomentDeterminacy

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)
open LeanProofs.IPRA.Combinatorics.StirlingPowers (ff)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Combinatorics.CatalanConvolution (monus_monus)
open LeanProofs.IPRA.Foundations.ChainViability (monus_le)
open LeanProofs.IPRA.Foundations.FrontierSoundness (rdB inst2_rdB lt_succ_of_le')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The general triangular system -/

section Triangular

variable (c D P Q : PTm 2)

/-- `|P(i, x) − Q(i, x)|` as `(P ∸ Q) + (Q ∸ P)`. -/
def adB : PTm 2 := monus P Q + monus Q P

theorem inst2_adB (i x : PTm n) :
    inst2 (adB P Q) i x = monus (inst2 P i x) (inst2 Q i x) + monus (inst2 Q i x) (inst2 P i x) := by
  simp [inst2, adB]

/-- `c(i, y) · P(i, snd y)`. -/
def tB : PTm 2 := c * rdB P

theorem inst2_tB (i y : PTm n) : inst2 (tB c P) i y = inst2 c i y * inst2 P i (sndT y) := by
  have e : inst2 (tB c P) i y = inst2 c i y * inst2 (rdB P) i y := by simp [inst2, tB]
  rw [e, inst2_rdB]

/-- A vanishing sum of absolute differences gives agreement below the bound. -/
theorem agree_pt {i J x : PTm n} (hZ : Γ ⊢[PRAAx] ap2 (sumF (adB P Q)) J x ≐ zero)
    (hi : Γ ⊢[PRAAx] lt i J) : Γ ⊢[PRAAx] inst2 P i x ≐ inst2 Q i x := by
  have z := sum_zero_elim (adB P Q) hZ hi
  rw [inst2_adB] at z
  exact le_antisymm (add_eq_zero_left z) (add_eq_zero_right z)

/-- The partial sums of the system agree when the sequences agree below `J`. -/
theorem sum_agree {J x : PTm n} (hZ : Γ ⊢[PRAAx] ap2 (sumF (adB P Q)) J x ≐ zero) :
    Γ ⊢[PRAAx] ap2 (sumF (tB c P)) J (pairT J x) ≐ ap2 (sumF (tB c Q)) J (pairT J x) := by
  refine sum_congr_bounded (tB c P) (tB c Q) (pairT J x) (pairT J x) J (.allI (.impI ?_))
  rw [inst2_tB, inst2_tB, shift_pairT]
  have hZ' := Prf.shift hZ
  have e : ((ap2 (sumF (adB P Q)) J x ≐ zero : Fm PTm n)).shift =
      (ap2 (sumF (adB P Q)) (Syn.shift J) (Syn.shift x) ≐ zero) := by
    simp [Fm.shift, Syn.shift]
  rw [e] at hZ'
  have a : (lt (var 0) (Syn.shift J) :: Γ.map Fm.shift) ⊢[PRAAx]
      inst2 P (var 0) (Syn.shift x) ≐ inst2 Q (var 0) (Syn.shift x) :=
    agree_pt P Q hZ'.wk Prf.hyp0
  have s : (lt (var 0) (Syn.shift J) :: Γ.map Fm.shift) ⊢[PRAAx]
      sndT (pairT (Syn.shift J) (Syn.shift x)) ≐ Syn.shift x := snd_pair _ _
  exact congrMul (.eqRefl _)
    (((congrInst2 P (.eqRefl _) s).eqTrans a).eqTrans (congrInst2 Q (.eqRefl _) s).eqSymm)

/-- The back-substitution step. -/
theorem back_step {J x : PTm n}
    (hE : Γ ⊢[PRAAx] ap2 (sumF (tB c P)) J (pairT J x) + inst2 D J x * inst2 P J x ≐
      ap2 (sumF (tB c Q)) J (pairT J x) + inst2 D J x * inst2 Q J x)
    (hD : Γ ⊢[PRAAx] inst2 D J x ≐ succ (pred (inst2 D J x)))
    (ih : Γ ⊢[PRAAx] ap2 (sumF (adB P Q)) J x ≐ zero) :
    Γ ⊢[PRAAx] ap2 (sumF (adB P Q)) (succ J) x ≐ zero := by
  have hPQ : Γ ⊢[PRAAx] inst2 P J x ≐ inst2 Q J x := by
    refine mul_cancel hD ?_
    ipra_lc natEq hE - natEq (sum_agree c P Q ih)
  have s := sum_succ' (Γ := Γ) (adB P Q) J x
  rw [inst2_adB] at s
  ipra_lc natEq s + natEq ih + natEq ((congrMonus hPQ (.eqRefl (inst2 Q J x))).eqTrans (monus_self _)) +
    natEq ((congrMonus (.eqRefl (inst2 Q J x)) hPQ).eqTrans (monus_self _))

theorem back_guard {J B x : PTm n}
    (hJ : Γ ⊢[PRAAx] le (succ J) (succ B))
    (hE : Γ ⊢[PRAAx] le J B ⟶
      (ap2 (sumF (tB c P)) J (pairT J x) + inst2 D J x * inst2 P J x ≐
        ap2 (sumF (tB c Q)) J (pairT J x) + inst2 D J x * inst2 Q J x))
    (hD : Γ ⊢[PRAAx] le J B ⟶ (inst2 D J x ≐ succ (pred (inst2 D J x))))
    (ih : Γ ⊢[PRAAx] le J (succ B) ⟶ (ap2 (sumF (adB P Q)) J x ≐ zero)) :
    Γ ⊢[PRAAx] ap2 (sumF (adB P Q)) (succ J) x ≐ zero := by
  have hJB : Γ ⊢[PRAAx] le J B := (succ_monus_succ J B).eqSymm.eqTrans hJ
  exact back_step c D P Q (Prf.impE hE hJB) (Prf.impE hD hJB)
    (Prf.impE ih (le_trans (le_succ_self J) hJ))

variable {c D P Q}

theorem back_all {B x : PTm n}
    (hE : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift B) ⟶
      (ap2 (sumF (tB c P)) (var 0) (pairT (var 0) (Syn.shift x)) +
          inst2 D (var 0) (Syn.shift x) * inst2 P (var 0) (Syn.shift x) ≐
        ap2 (sumF (tB c Q)) (var 0) (pairT (var 0) (Syn.shift x)) +
          inst2 D (var 0) (Syn.shift x) * inst2 Q (var 0) (Syn.shift x))))
    (hD : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift B) ⟶
      (inst2 D (var 0) (Syn.shift x) ≐ succ (pred (inst2 D (var 0) (Syn.shift x)))))) :
    Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift (succ B)) ⟶
      (ap2 (sumF (adB P Q)) (var 0) (Syn.shift x) ≐ zero)) := by
  refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
  · have e : (le (var 0) (Syn.shift (succ B)) ⟶
          (ap2 (sumF (adB P Q)) (var 0) (Syn.shift x) ≐ zero)).subst (Syn.inst zero) =
        (le zero (succ B) ⟶ (ap2 (sumF (adB P Q)) zero x ≐ zero)) := by
      simp
    rw [e]
    exact .impI (sum_zero _ _)
  · have e : (le (var 0) (Syn.shift (succ B)) ⟶
          (ap2 (sumF (adB P Q)) (var 0) (Syn.shift x) ≐ zero)).subst (Syn.repl (succ (var 0))) =
        (le (succ (var 0)) (Syn.shift (succ B)) ⟶
          (ap2 (sumF (adB P Q)) (succ (var 0)) (Syn.shift x) ≐ zero)) := by
      simp
    rw [e]
    have e' : Syn.shift (succ B) = succ (Syn.shift B) := by simp [Syn.shift]
    rw [e']
    exact .impI (back_guard c D P Q Prf.hyp0 hE.allOpen.wk.wk hD.allOpen.wk.wk Prf.hyp1)

/-- Uniqueness by back substitution: two solutions of a triangular system with positive diagonal
agree at every index `d ≤ B`. -/
theorem back_unique {B x d : PTm n}
    (hE : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift B) ⟶
      (ap2 (sumF (tB c P)) (var 0) (pairT (var 0) (Syn.shift x)) +
          inst2 D (var 0) (Syn.shift x) * inst2 P (var 0) (Syn.shift x) ≐
        ap2 (sumF (tB c Q)) (var 0) (pairT (var 0) (Syn.shift x)) +
          inst2 D (var 0) (Syn.shift x) * inst2 Q (var 0) (Syn.shift x))))
    (hD : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift B) ⟶
      (inst2 D (var 0) (Syn.shift x) ≐ succ (pred (inst2 D (var 0) (Syn.shift x))))))
    (hd : Γ ⊢[PRAAx] le d B) : Γ ⊢[PRAAx] inst2 P d x ≐ inst2 Q d x := by
  have a := Prf.allE (succ B) (back_all hE hD)
  have e : (le (var 0) (Syn.shift (succ B)) ⟶
        (ap2 (sumF (adB P Q)) (var 0) (Syn.shift x) ≐ zero)).subst (Syn.inst (succ B)) =
      (le (succ B) (succ B) ⟶ (ap2 (sumF (adB P Q)) (succ B) x ≐ zero)) := by
    simp
  rw [e] at a
  exact agree_pt P Q (Prf.impE a (le_refl (succ B))) (lt_succ_of_le' hd)

end Triangular

/-! ## Factorial moments -/

/-- The masses read from the top: `p(B − i, x)` with `B = fst x`. -/
def rvB (p : PTm 2) : PTm 2 := Syn.subst ![monus (fstT (var 1)) (var 0), var 1] p

theorem inst2_rvB (p : PTm 2) (i x : PTm n) : inst2 (rvB p) i x = inst2 p (monus (fstT x) i) x := by
  simp only [inst2, rvB, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> simp

/-- The coefficients `(B − i)_{B − d}`; variables `0 = i`, `1 = y = ⟨d, x⟩`, `B = fst x`. -/
def fcB : PTm 2 :=
  ff (monus (fstT (sndT (var 1))) (var 0)) (monus (fstT (sndT (var 1))) (fstT (var 1)))

/-- The diagonal `(B − d)_{B − d} = (B − d)!`; variables `0 = d`, `1 = x`. -/
def fdB : PTm 2 := fact (monus (fstT (var 1)) (var 0))

theorem inst2_fdB (d x : PTm n) : inst2 fdB d x = fact (monus (fstT x) d) := by
  simp [inst2, fdB]

/-- `thm:moment-determinacy`, the triangular step: laws on `{0, …, B}` with the same factorial moments
have the same masses. -/
theorem moment_determinacy {p q : PTm 2} {x k : PTm n}
    (hE : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift (fstT x)) ⟶
      (ap2 (sumF (tB fcB (rvB p))) (var 0) (pairT (var 0) (Syn.shift x)) +
          inst2 fdB (var 0) (Syn.shift x) * inst2 (rvB p) (var 0) (Syn.shift x) ≐
        ap2 (sumF (tB fcB (rvB q))) (var 0) (pairT (var 0) (Syn.shift x)) +
          inst2 fdB (var 0) (Syn.shift x) * inst2 (rvB q) (var 0) (Syn.shift x))))
    (hk : Γ ⊢[PRAAx] le k (fstT x)) : Γ ⊢[PRAAx] inst2 p k x ≐ inst2 q k x := by
  have hD : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift (fstT x)) ⟶
      (inst2 fdB (var 0) (Syn.shift x) ≐ succ (pred (inst2 fdB (var 0) (Syn.shift x))))) := by
    refine .allI (.impI ?_)
    rw [inst2_fdB]
    exact fact_pos _
  have u := back_unique hE hD (monus_le (fstT x) k)
  rw [inst2_rvB, inst2_rvB] at u
  have m := monus_monus hk
  exact ((congrInst2 p m (.eqRefl x)).eqSymm.eqTrans u).eqTrans (congrInst2 q m (.eqRefl x))

end LeanProofs.IPRA.Probability.MomentDeterminacy
