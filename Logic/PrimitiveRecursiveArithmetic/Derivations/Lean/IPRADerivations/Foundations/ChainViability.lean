import IPRADerivations.Foundations.ViableChain

/-!
# An admissible chain makes its start viable (`ipra_evidence_framework`)

Packet: `foundations/ipra_evidence_framework`, theorem "PR backward viability and certified
finite chain": the direction "an admissible chain from `(i, a)` through level `h` gives
`D = 1`" of the reverse-row invariant.

Let `I` be a finite compatibility instance (`Foundations/BackwardViability`) and let the
chain be a term `c(t, p)` (variables `0 = t`, `1 = p`) with supplied derivations
(`Admissible`), as rules at arbitrary terms and hypotheses:

* `c(t) < B(t)` and `G(t, c(t)) ≠ 0` for `t ≤ h`;
* `T(t, c(t), c(t + 1)) ≠ 0` for `t < h`.

Then `chain_viable`: `V(j, c(h ∸ j)) = 1` for every `j ≤ h`, and in particular
`start_viable`: `V(h, c(0)) = 1`. The induction is on the quantifier-free formula
`j ≤ h → V(j, c(h ∸ j)) = 1`, upwards in the number `j` of remaining levels; the base is
`V_zero` and each step is `V_fold`.

Together with `Foundations/ViableChain` (`chain_inv`, `chain_local`, `chain_edge`) this gives
both directions of the packet's equivalence for chains presented by terms. An equivalence
with a bounded existential over coded chains is not stated.
-/

namespace LeanProofs.IPRA.Foundations.ChainViability

open_ipra exports
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.Foundations.BackwardViability
open LeanProofs.IPRA.Foundations.BackwardViability.Instance
open LeanProofs.IPRA.Foundations.ViableChain

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-- `h ∸ j ≤ h`. -/
alias monus_le := Common.monus_le_self

/-- `h ∸ (j + 1) < h` for `j < h`. -/
theorem monus_succ_lt {h j : PTm k} (hj : Γ ⊢[PRAAx] lt j h) :
    Γ ⊢[PRAAx] lt (monus h (succ j)) h :=
  Common.monus_succ_lt h j hj

/-- A chain `c(t, p)` with supplied derivations of its bounds and of all local and edge
tests. -/
structure Admissible (I : Instance) (c : PTm 2) : Prop where
  bound : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {t p : PTm k},
    (Γ ⊢[PRAAx] le t (I.h p)) → (Γ ⊢[PRAAx] lt (inst2 c t p) (I.bd t p))
  local_ok : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {t p : PTm k},
    (Γ ⊢[PRAAx] le t (I.h p)) → (Γ ⊢[PRAAx] neg (I.g t (inst2 c t p) p ≐ zero))
  edge_ok : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {t p : PTm k},
    (Γ ⊢[PRAAx] lt t (I.h p)) →
      (Γ ⊢[PRAAx] neg (I.t t (inst2 c t p) (inst2 c (succ t) p) p ≐ zero))

section Converse

variable {I : Instance} {c : PTm 2}

/-- One step upwards: from `V(j, c(h ∸ j)) = 1` and `j < h`,
`V(j + 1, c(h ∸ (j + 1))) = 1`. -/
theorem viable_step (A : Admissible I c) {j p : PTm k} (hj : Γ ⊢[PRAAx] lt j (I.h p))
    (ih : Γ ⊢[PRAAx] I.V j (inst2 c (monus (I.h p) j) p) p ≐ one) :
    Γ ⊢[PRAAx] I.V (succ j) (inst2 c (monus (I.h p) (succ j)) p) p ≐ one := by
  have hlt := monus_succ_lt hj
  have e := A.edge_ok hlt
  -- `c((h ∸ (j + 1)) + 1) = c(h ∸ j)`
  have cc : Γ ⊢[PRAAx] inst2 c (succ (monus (I.h p) (succ j))) p ≐ inst2 c (monus (I.h p) j) p :=
    congrInst2 c (succ_monus hj) (.eqRefl _)
  have ht : Γ ⊢[PRAAx] neg (I.t (monus (I.h p) (succ j)) (inst2 c (monus (I.h p) (succ j)) p)
      (inst2 c (monus (I.h p) j) p) p ≐ zero) := by
    refine .impI (.impE e.wk (.eqTrans ?_ Prf.hyp0))
    exact Prf.eqCongr I.T fun l => by
      fin_cases l
      · exact .eqRefl _
      · exact .eqRefl _
      · exact cc.wk
      · exact .eqRefl _
  exact V_fold I (A.bound (monus_le _ _)) (A.local_ok (monus_le _ _)) (A.bound (monus_le _ _)) ht ih

/-- Variables: `0 = j`, `1 = p`. -/
private def viaF (I : Instance) (c : PTm 2) : Fm PTm 2 :=
  le (var 0) (I.h (var 1)) ⟶
    (I.V (var 0) (inst2 c (monus (I.h (var 1)) (var 0)) (var 1)) (var 1) ≐ one)

private theorem via₀ (A : Admissible I c) : ([] : List (Fm PTm 2)) ⊢[PRAAx] viaF I c := by
  ipra_ind (⟨trivial, trivial⟩) [viaF, subst_le, subst_V, subst_inst2, Instance.subst_h]
  · refine .impI ?_
    -- the last level: `c(h ∸ 0) = c(h)` and `V(0, a) = sg G(h, a)`
    have cz : [le zero (I.h (var 0 : PTm 1))] ⊢[PRAAx]
        inst2 c (monus (I.h (var 0)) zero) (var 0) ≐ inst2 c (I.h (var 0)) (var 0) :=
      congrInst2 c (monus_zero _) (.eqRefl _)
    have v0 : [le zero (I.h (var 0 : PTm 1))] ⊢[PRAAx]
        I.V zero (inst2 c (I.h (var 0)) (var 0)) (var 0) ≐
          sg (I.g (I.h (var 0)) (inst2 c (I.h (var 0)) (var 0)) (var 0)) :=
      V_zero I (A.bound (le_refl _))
    exact (V_congr I (.eqRefl _) cz).eqTrans (v0.eqTrans (sg_of_ne (A.local_ok (le_refl _))))
  · have ih : [viaF I c] ⊢[PRAAx] le (var 0) (I.h (var 1)) ⟶
        (I.V (var 0) (inst2 c (monus (I.h (var 1)) (var 0)) (var 1)) (var 1) ≐ one) := Prf.hyp0
    refine .impI ?_
    exact viable_step A Prf.hyp0 (.impE ih.wk (le_trans (le_succ_self _) Prf.hyp0))

/-- An admissible chain is viable at every level: `V(j, c(h ∸ j)) = 1` for `j ≤ h`. -/
theorem chain_viable (A : Admissible I c) {j p : PTm k} (hj : Γ ⊢[PRAAx] le j (I.h p)) :
    Γ ⊢[PRAAx] I.V j (inst2 c (monus (I.h p) j) p) p ≐ one := by
  have i := inst (Γ := Γ) (via₀ A) (![j, p] : Fin 2 → PTm k)
  simp [viaF] at i
  exact .impE i hj

/-- The start of an admissible chain is viable for the whole horizon: `V(h, c(0)) = 1`. -/
theorem start_viable (A : Admissible I c) (p : PTm k) :
    Γ ⊢[PRAAx] I.V (I.h p) (inst2 c zero p) p ≐ one :=
  (V_congr I (.eqRefl _) (congrInst2 c (monus_self (I.h p)) (.eqRefl _))).eqSymm.eqTrans
    (chain_viable A (le_refl _))

end Converse

end LeanProofs.IPRA.Foundations.ChainViability

export_ipra Foundations.ChainViability (monus_le)
