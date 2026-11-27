import IPRADerivations.Foundations.BoundedSyntax
import IPRADerivations.Foundations.BoundedSelection

/-!
# The least even natural number in a bounded interval

The first concrete regression requested by FIBER Appendix B. The actual
two-variable source predicate is `lower ≤ candidate ∧ par(candidate)=0`.
The arity-indexed compiler constructs its PR verifier and proves its Boolean
contract. Complement search below the exclusive upper endpoint returns the
least accepted natural number, or that endpoint if the interval has no even
member. This convention includes empty and reversed intervals uniformly.

The interval predicate, verifier correctness and empty-case proof are derived
here; they are not supplied as assumptions to the generic search theorem.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Foundations.LeastEven

open_ipra exports

variable {n : ℕ} {Γ : List (Fm PTm n)}

def predicate : BoundedSyntax.BFm 2 :=
  .and (.le (var 0) (var 1)) (.eq (par (var 1)) zero)

def verifier : PR 2 := BoundedSyntax.bitF predicate

/-- The executable bounded-search program; `upper` is its failure sentinel. -/
def least (lower upper : PTm n) : PTm n := BoundedSelection.mu verifier lower upper

def accepted (lower candidate : PTm n) : Fm PTm n :=
  le lower candidate ⋏ (par candidate ≐ zero)

@[simp] theorem subst_least {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (least a b) = least (Syn.subst σ a) (Syn.subst σ b) :=
  BoundedSelection.subst_mu verifier σ a b

@[simp] theorem subst_accepted {m : ℕ} (σ : Fin n → PTm m) (a i : PTm n) :
    (accepted a i).subst σ = accepted (Syn.subst σ a) (Syn.subst σ i) := by
  ipra_ind_simp [accepted, subst_le, subst_ap1]

theorem verifier_correct (a i : PTm n) :
    Γ ⊢[PRAAx] Fm.iff (ap2 verifier a i ≐ one) (accepted a i) := by
  have program := BoundedSyntax.program_correct (Γ := Γ) predicate ![a, i]
  have reflected := BoundedSyntax.bounded_reflection (Γ := Γ) predicate ![a, i]
  have iffBit : Γ ⊢[PRAAx]
      Fm.iff (ap2 verifier a i ≐ one) (BoundedSyntax.bit predicate ![a, i] ≐ one) :=
    .iffI (.impI (program.eqSymm.wk.eqTrans Prf.hyp0))
      (.impI (program.wk.eqTrans Prf.hyp0))
  have result := iffBit.iffTrans reflected
  simpa [verifier, predicate, accepted, BoundedSyntax.formula, BoundedSyntax.BFm.le, le] using result

theorem verifier_cases (a i : PTm n) :
    Γ ⊢[PRAAx] (ap2 verifier a i ≐ zero) ⋎ (ap2 verifier a i ≐ one) := by
  have p := BoundedSyntax.program_correct (Γ := Γ) predicate ![a, i]
  exact .orE (BoundedSyntax.bit_cases predicate ![a, i])
    (.orI₁ (p.wk.eqTrans Prf.hyp0)) (.orI₂ (p.wk.eqTrans Prf.hyp0))

theorem verifier_bits (a : PTm n) : Γ ⊢[PRAAx] BoundedSelection.bits verifier a := by
  apply Prf.allI
  exact verifier_cases (Syn.shift a) (var 0)

theorem least_bound (a b : PTm n) : Γ ⊢[PRAAx] le (least a b) b :=
  BooleanizationCorollaries.first_le (BoundedSelection.body verifier) b a

theorem least_found {a b : PTm n} (h : Γ ⊢[PRAAx] lt (least a b) b) :
    Γ ⊢[PRAAx] accepted a (least a b) := by
  have bit : Γ ⊢[PRAAx]
      (inst2 (BoundedSelection.body verifier) (least a b) a ≐ zero) ⋎
      (inst2 (BoundedSelection.body verifier) (least a b) a ≐ one) := by
    simpa only [BoundedSelection.body_at] using verifier_cases (Γ := Γ) a (least a b)
  have found := BooleanizationCorollaries.first_found (BoundedSelection.body verifier) bit h
  rw [BoundedSelection.body_at] at found
  exact (verifier_correct a (least a b)).iffMp found

/-- Any actual even interval member bounds the successful least output. -/
theorem found_of_even {a b i : PTm n} (ha : Γ ⊢[PRAAx] le a i)
    (hi : Γ ⊢[PRAAx] lt i b) (he : Γ ⊢[PRAAx] par i ≐ zero) :
    Γ ⊢[PRAAx] lt (least a b) b ⋏ le (least a b) i := by
  have accepted := (verifier_correct a i).iffMpr (.andI ha he)
  have hit : Γ ⊢[PRAAx]
      inst2 (BooleanizationCorollaries.nf (BoundedSelection.body verifier)) i a ≐ zero := by
    rw [BooleanizationCorollaries.inst2_nf, BoundedSelection.body_at]
    exact (congrMonus (.eqRefl _) accepted).eqTrans (monus_self one)
  have result := Search.search_found hit hi
  exact .andI (.andE₁ result) (.andE₂ (.andE₂ result))

theorem earlier_rejected {a b i : PTm n} (h : Γ ⊢[PRAAx] lt i (least a b)) :
    Γ ⊢[PRAAx] ap2 verifier a i ≐ zero := by
  have bit : Γ ⊢[PRAAx]
      (inst2 (BoundedSelection.body verifier) i a ≐ zero) ⋎
      (inst2 (BoundedSelection.body verifier) i a ≐ one) := by
    simpa only [BoundedSelection.body_at] using verifier_cases (Γ := Γ) a i
  simpa only [BoundedSelection.body_at] using
    BooleanizationCorollaries.first_before (BoundedSelection.body verifier) bit h

theorem no_earlier_even {a b i : PTm n} (hi : Γ ⊢[PRAAx] lt i (least a b))
    (ha : Γ ⊢[PRAAx] le a i) : Γ ⊢[PRAAx] neg (par i ≐ zero) := by
  apply Prf.impI
  have accepted := (verifier_correct a i).iffMpr (.andI ha.wk Prf.hyp0)
  exact BoundedFormulas.clash Fm.bot (earlier_rejected hi).wk accepted

theorem earlier_odd {a b i : PTm n} (hi : Γ ⊢[PRAAx] lt i (least a b))
    (ha : Γ ⊢[PRAAx] le a i) : Γ ⊢[PRAAx] par i ≐ one :=
  .orE (par_cases i) (.botE _ (.impE (no_earlier_even hi ha).wk Prf.hyp0)) Prf.hyp0

/-- Successful output has an actual half witnessing evenness. -/
theorem even_witness {a b : PTm n} (h : Γ ⊢[PRAAx] lt (least a b) b) :
    Γ ⊢[PRAAx] least a b ≐ two * half (least a b) :=
  (half_par (least a b)).eqTrans
    ((congrAdd (.eqRefl _) (.andE₂ (least_found h))).eqTrans (add_zero _))

def noEven (a b : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift b) ⟶ le (Syn.shift a) (var 0) ⟶ neg (par (var 0) ≐ zero))

theorem noEven_at {a b i : PTm n} (h : Γ ⊢[PRAAx] noEven a b)
    (hi : Γ ⊢[PRAAx] lt i b) (ha : Γ ⊢[PRAAx] le a i) :
    Γ ⊢[PRAAx] neg (par i ≐ zero) := by
  have e := Prf.allE i h
  have r : Γ ⊢[PRAAx] lt i b ⟶ le a i ⟶ neg (par i ≐ zero) := by
    simpa [noEven] using e
  exact .impE (.impE r hi) ha

theorem failure_of_no_even {a b : PTm n} (h : Γ ⊢[PRAAx] noEven a b) :
    Γ ⊢[PRAAx] least a b ≐ b := by
  refine .orE (lt_or_eq_of_le (least_bound a b)) ?_ Prf.hyp0
  have found := least_found (Prf.hyp0 (Γ := Γ) (φ := lt (least a b) b))
  exact .botE _ (.impE (noEven_at h.wk Prf.hyp0 (.andE₁ found)) (.andE₂ found))

theorem no_even_of_failure {a b : PTm n} (h : Γ ⊢[PRAAx] least a b ≐ b) :
    Γ ⊢[PRAAx] noEven a b := by
  refine .allI (.impI (.impI ?_))
  have hs := h.shift
  simp only [Fm.shift, Fm.subst_eq, subst_least] at hs
  have hi : (le (Syn.shift a) (var 0) :: lt (var 0) (Syn.shift b) :: Γ.map Fm.shift) ⊢[PRAAx]
      lt (var 0) (least (Syn.shift a) (Syn.shift b)) :=
    lt_congr (.eqRefl _) hs.wk.wk.eqSymm Prf.hyp1
  exact no_earlier_even hi Prf.hyp0

theorem failure_iff (a b : PTm n) :
    Γ ⊢[PRAAx] Fm.iff (least a b ≐ b) (noEven a b) :=
  .iffI (.impI (no_even_of_failure Prf.hyp0)) (.impI (failure_of_no_even Prf.hyp0))

theorem empty_interval {a b : PTm n} (h : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] least a b ≐ b := by
  apply failure_of_no_even
  refine .allI (.impI (.impI ?_))
  have shifted : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift b) (Syn.shift a) :=
    Order.shift_le h
  exact le_lt_absurd _ (le_trans shifted.wk.wk Prf.hyp0) Prf.hyp1

/-- Full concrete interval specification, including the failure convention. -/
def specification (a b : PTm n) : Fm PTm n :=
  le (least a b) b ⋏
    ((lt (least a b) b ⟶ accepted a (least a b)) ⋏
      (.all (lt (var 0) (Syn.shift (least a b)) ⟶
        le (Syn.shift a) (var 0) ⟶ (par (var 0) ≐ one)) ⋏
        Fm.iff (least a b ≐ b) (noEven a b)))

theorem least_even (a b : PTm n) : Γ ⊢[PRAAx] specification a b := by
  refine .andI (least_bound a b) (.andI (.impI (least_found Prf.hyp0)) (.andI ?_ (failure_iff a b)))
  refine .allI (.impI (.impI ?_))
  have hi : (le (Syn.shift a) (var 0) :: lt (var 0) (Syn.shift (least a b)) :: Γ.map Fm.shift)
      ⊢[PRAAx] lt (var 0) (least (Syn.shift a) (Syn.shift b)) := by
    simpa only [Syn.shift, subst_least] using
      (Prf.hyp1 (Ax := PRAAx) (Γ := Γ.map Fm.shift)
        (φ := lt (var 0) (Syn.shift (least a b))) (ψ := le (Syn.shift a) (var 0)))
  exact earlier_odd hi Prf.hyp0

theorem least_even_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (specification (var 0) (var 1)) :=
  closeUniv 2 (least_even _ _)

#print axioms verifier_correct
#print axioms verifier_bits
#print axioms found_of_even
#print axioms least_even_closed
#print axioms even_witness
#print axioms failure_iff
#print axioms empty_interval

end LeanProofs.IPRA.Foundations.LeastEven
