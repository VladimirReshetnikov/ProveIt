import IPRADerivations.Core.BoundedSums

/-! Imported from the packet `analysis/constructive_computable_analysis_ipra_2026-11-20`, `lean/PrefixObject.lean`: the namespace is placed under `LeanProofs.IPRA.Analysis` and the `#print axioms` lines are dropped (the library audits axioms in `Checks/Axioms.lean`). -/

/-! Prefix repair, expressed in the object language of first-order iPRA.
The raw value body has arguments (index, packed parameter).
The prefix of length zero has value zero. Inputs here are already clipped
nonnegative observations in integer units. -/

namespace LeanProofs.IPRA.Analysis.Observation.PrefixObject
open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open LeanProofs.ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def larger (a b : PTm n) : PTm n := monus a b + b

theorem larger_le {a b u : PTm n}
    (ha : Γ ⊢[PRAAx] le a u) (hb : Γ ⊢[PRAAx] le b u) :
    Γ ⊢[PRAAx] le (larger a b) u := by
  refine .orE (le_total a b) ?_ ?_
  · have eq := (congrAdd (show le a b :: Γ ⊢[PRAAx] monus a b ≐ zero from Prf.hyp0)
      (.eqRefl b)).eqTrans (zero_add b)
    exact le_congr eq.eqSymm (.eqRefl u) hb.wk
  · have eq := (monus_max (Γ := le b a :: Γ) a b).eqTrans
      ((congrAdd (show le b a :: Γ ⊢[PRAAx] monus b a ≐ zero from Prf.hyp0)
        (.eqRefl a)).eqTrans (zero_add a))
    exact le_congr eq.eqSymm (.eqRefl u) ha.wk

theorem le_larger_right (a b : PTm n) : Γ ⊢[PRAAx] le b (larger a b) :=
  le_add_left b (monus a b)

theorem le_larger_left (a b : PTm n) : Γ ⊢[PRAAx] le a (larger a b) :=
  le_congr (.eqRefl a) (monus_max a b).eqSymm (le_add_left a (monus b a))

def prefixCode (raw : PTm 2) : PR 2 :=
  rec2 zero (larger (var 1) (bodyStep raw))

theorem prefix_zero (raw : PTm 2) (x : PTm n) :
    Γ ⊢[PRAAx] ap2 (prefixCode raw) zero x ≐ zero := by
  simpa only [prefixCode, LeanProofs.ConciseIPRA.PTm.subst_zero] using
    rec2_zero (Γ := Γ) zero (larger (var 1) (bodyStep raw)) x

theorem prefix_step (raw : PTm 2) (i x : PTm n) :
    Γ ⊢[PRAAx] ap2 (prefixCode raw) (succ i) x ≐
      larger (ap2 (prefixCode raw) i x) (inst2 raw i x) := by
  have h := rec2_succ (Γ := Γ) zero (larger (var 1) (bodyStep raw)) i x
  have e : Syn.subst ![i, ap2 (prefixCode raw) i x, x] (bodyStep raw) = inst2 raw i x := by
    rw [bodyStep, Syn.subst_subst]
    exact congrArg (fun σ => Syn.subst σ raw) (by funext j; fin_cases j <;> rfl)
  change Γ ⊢[PRAAx] ap2 (prefixCode raw) (succ i) x ≐
    Syn.subst ![i, ap2 (prefixCode raw) i x, x] (larger (var 1) (bodyStep raw)) at h
  simpa only [larger, LeanProofs.IPRA.PTm.subst_add, LeanProofs.IPRA.PTm.subst_monus,
    Syn.subst_var, e, Matrix.cons_val_one, Matrix.cons_val_zero] using h

theorem covers_latest (raw : PTm 2) (i x : PTm n) :
    Γ ⊢[PRAAx] le (inst2 raw i x) (ap2 (prefixCode raw) (succ i) x) :=
  le_congr (.eqRefl _) (prefix_step raw i x).eqSymm (le_larger_right _ _)

theorem increasing (raw : PTm 2) (i x : PTm n) :
    Γ ⊢[PRAAx] le (ap2 (prefixCode raw) i x) (ap2 (prefixCode raw) (succ i) x) :=
  le_congr (.eqRefl _) (prefix_step raw i x).eqSymm (le_larger_left _ _)

/-- A bound just on the consumed samples suffices; the prefix length is
an object variable. The induction matrix is a quantifier-free implication. -/
theorem prefix_upper (raw : PTm 2) (x N u : PTm n)
    (samples : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 raw (var 0) (Syn.shift x)) (Syn.shift u))) :
    Γ ⊢[PRAAx] le (ap2 (prefixCode raw) N x) u := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      le (ap2 (prefixCode raw) (var 0) (Syn.shift x)) (Syn.shift u)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simpa using Prf.impI (le_congr (prefix_zero (Γ := le zero N :: Γ) raw x).eqSymm
        (.eqRefl u) (zero_le u))
    · simp only [Fm.subst_imp, subst_le, subst_ap2, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift]
      refine .impI ?_
      have hi : (le (succ (var 0)) (Syn.shift N) ::
          (le (var 0) (Syn.shift N) ⟶ le (ap2 (prefixCode raw) (var 0) (Syn.shift x)) (Syn.shift u)) ::
          Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
        le_trans (le_succ_self _) Prf.hyp0
      exact le_congr (prefix_step raw (var 0) (Syn.shift x)).eqSymm (.eqRefl _)
        (larger_le (Prf.impE Prf.hyp1 hi) (Prf.impE samples.allOpen.wk.wk Prf.hyp0))
  have h := Prf.allE N hall
  simpa using (show Γ ⊢[PRAAx] le (ap2 (prefixCode raw) N x) u from
    Prf.impE (by simpa using h) (le_refl N))

end LeanProofs.IPRA.Analysis.Observation.PrefixObject
