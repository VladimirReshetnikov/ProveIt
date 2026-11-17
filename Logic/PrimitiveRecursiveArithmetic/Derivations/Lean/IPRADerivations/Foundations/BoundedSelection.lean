import IPRADerivations.Foundations.BooleanizationCorollaries

/-!
# Canonical selection for an arbitrary binary Boolean verifier

FIBER `thm:least`, with the verifier's bit-valued contract retained as an
object-language hypothesis. The actual PR selector searches the complement
`1 ∸ v(q,c)`. All queries, exclusive bounds and earlier indices are internal.
-/

namespace LeanProofs.IPRA.Foundations.BoundedSelection

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.BooleanizationCorollaries
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Search bodies have certificate first and query second. -/
def body (v : PR 2) : PTm 2 := ap2 v (var 1) (var 0)

@[simp] theorem body_at (v : PR 2) (c q : PTm n) :
    inst2 (body v) c q = ap2 v q c := by simp [body, inst2]

def mu (v : PR 2) (q B : PTm n) : PTm n := first (body v) B q

@[simp] theorem subst_mu (v : PR 2) {m : ℕ} (σ : Fin n → PTm m) (q B : PTm n) :
    Syn.subst σ (mu v q B) = mu v (Syn.subst σ q) (Syn.subst σ B) := subst_ap2 _ _ _ _

def bits (v : PR 2) (q : PTm n) : Fm PTm n :=
  .all ((ap2 v (Syn.shift q) (var 0) ≐ zero) ⋎ (ap2 v (Syn.shift q) (var 0) ≐ one))

def existsAccepted (v : PR 2) (q B : PTm n) : Fm PTm n :=
  .ex (lt (var 0) (Syn.shift B) ⋏ (ap2 v (Syn.shift q) (var 0) ≐ one))

theorem bits_at (v : PR 2) (q c : PTm n) (h : Γ ⊢[PRAAx] bits v q) :
    Γ ⊢[PRAAx] (ap2 v q c ≐ zero) ⋎ (ap2 v q c ≐ one) := by
  simpa [bits] using Prf.allE c h

/-- Existence makes the complement search succeed below its exclusive bound. -/
theorem found_bound (v : PR 2) (q B : PTm n)
    (h : Γ ⊢[PRAAx] existsAccepted v q B) : Γ ⊢[PRAAx] lt (mu v q B) B := by
  refine .exE h ?_
  let witness := lt (var 0) (Syn.shift B) ⋏ (ap2 v (Syn.shift q) (var 0) ≐ one)
  let Δ := witness :: Γ.map Fm.shift
  have accepted : Δ ⊢[PRAAx] ap2 v (Syn.shift q) (var 0) ≐ one := Prf.andE₂ Prf.hyp0
  have complement : Δ ⊢[PRAAx] inst2 (nf (body v)) (var 0) (Syn.shift q) ≐ zero := by
    rw [inst2_nf, body_at]
    exact (congrMonus (.eqRefl _) accepted).eqTrans (monus_self one)
  have bound := Prf.andE₁ (Search.search_found complement (Prf.andE₁ (Prf.hyp0 : Δ ⊢[PRAAx] witness)))
  simpa only [Δ, witness, Fm.shift, subst_lt, subst_mu, Syn.shift, mu, first,
    Search.mu, subst_ap2] using bound

def conclusion (v : PR 2) (q B : PTm n) : Fm PTm n :=
  lt (mu v q B) B ⋏ ((ap2 v q (mu v q B) ≐ one) ⋏
    .all (lt (var 0) (Syn.shift (mu v q B)) ⟶ (ap2 v (Syn.shift q) (var 0) ≐ zero)))

/-- The complete generic one-success theorem, including literal zero at
every earlier verifier input. -/
theorem least (v : PR 2) (q B : PTm n)
    (hb : Γ ⊢[PRAAx] bits v q) (he : Γ ⊢[PRAAx] existsAccepted v q B) :
    Γ ⊢[PRAAx] conclusion v q B := by
  have bound := found_bound v q B he
  have accepted : Γ ⊢[PRAAx] ap2 v q (mu v q B) ≐ one := by
    have bit : Γ ⊢[PRAAx]
        (inst2 (body v) (first (body v) B q) q ≐ zero) ⋎
        (inst2 (body v) (first (body v) B q) q ≐ one) := by
      simpa only [body_at, mu] using bits_at v q (mu v q B) hb
    simpa only [body_at, mu] using first_found (body v) bit bound
  refine .andI bound (.andI accepted (.allI (.impI ?_)))
  let Δ := lt (var 0) (Syn.shift (mu v q B)) :: Γ.map Fm.shift
  have bit : Δ ⊢[PRAAx] (ap2 v (Syn.shift q) (var 0) ≐ zero) ⋎
      (ap2 v (Syn.shift q) (var 0) ≐ one) := hb.allOpen.wk
  have early : Δ ⊢[PRAAx] lt (var 0) (mu v (Syn.shift q) (Syn.shift B)) := by
    simpa only [Δ, Syn.shift, subst_mu] using (Prf.hyp0 : Δ ⊢[PRAAx] _)
  have bit' : Δ ⊢[PRAAx] (inst2 (body v) (var 0) (Syn.shift q) ≐ zero) ⋎
      (inst2 (body v) (var 0) (Syn.shift q) ≐ one) := by
    simpa only [body_at] using bit
  simpa only [body_at] using first_before (body v) bit' early

/-- The source sentence has internally quantified query and bound. -/
def leastFormula (v : PR 2) : Fm PTm 2 :=
  bits v (var 0) ⟶ existsAccepted v (var 0) (var 1) ⟶ conclusion v (var 0) (var 1)

theorem canonical_bounded_selection (v : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (leastFormula v) :=
  closeUniv 2 (.impI (.impI (least v (var 0) (var 1) Prf.hyp1 Prf.hyp0)))

#print axioms found_bound
#print axioms least
#print axioms canonical_bounded_selection

end LeanProofs.IPRA.Foundations.BoundedSelection
