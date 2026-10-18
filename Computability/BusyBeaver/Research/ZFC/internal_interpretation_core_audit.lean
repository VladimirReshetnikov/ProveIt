import ZFCinPA.InternalInterpretation

/-! The supplied seven probes are retained; the clients keep all model elements internal. -/

open LeanProofs.ZFCinPA

#print axioms InternalInterpretation.interp_neg
#print axioms InternalInterpretation.interp_shift
#print axioms InternalInterpretation.interp_subst
#print axioms InternalInterpretation.interp_free
#print axioms InternalInterpretation.derivable_iSet
#print axioms InternalInterpretation.provable_interp
#print axioms InternalInterpretation.provable_falsum_of_interp

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.InternalRelativization
open LeanProofs.ZFCinPA.InternalInterpretation
open scoped LO.FirstOrder.Arithmetic

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {P : V}

example (hd : IsSemiformula ℒₛₑₜ 1 (dom P))
    (hds : shift ℒₛₑₜ (dom P) = dom P)
    (ha : ∀ R, IsSemiformula ℒₛₑₜ 2 (atomOf P R))
    (has : ∀ R, shift ℒₛₑₜ (atomOf P R) = atomOf P R) : Good P :=
  ⟨hd, hds, ha, has⟩

example (hP : Good P) (R : V) : IsSemiformula ℒₛₑₜ 2 (atomOf P R) :=
  hP.isAtom R

example (hP : Good P) {n p : V} (hp : IsSemiformula ℒₛₑₜ n p) :
    IsSemiformula ℒₛₑₜ n (interp P p) := isSemiformula_interp hP hp

example (hP : Good P) {n p : V} (hp : IsSemiformula ℒₛₑₜ n p) :
    neg ℒₛₑₜ (interp P p) = interp P (neg ℒₛₑₜ p) := interp_neg hP hp

example (hP : Good P) {n p : V} (hp : IsSemiformula ℒₛₑₜ n p) :
    shift ℒₛₑₜ (interp P p) = interp P (shift ℒₛₑₜ p) := interp_shift hP hp

example (hP : Good P) {n a p w : V} (hp : IsSemiformula ℒₛₑₜ n p)
    (hw : IsSemitermVec ℒₛₑₜ n a w) :
    subst ℒₛₑₜ w (interp P p) = interp P (subst ℒₛₑₜ w p) := interp_subst hP hp hw

example (hP : Good P) {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p) :
    free ℒₛₑₜ (interp P p) = interp P (free ℒₛₑₜ p) := interp_free hP hp

example : interp P (^⊥ : V) = (^⊥ : V) := interp_falsum

example {s y : V} : y ∈ iSet P s ↔ ∃ x ∈ s, y = interp P x := mem_iSet_iff

variable {T U : FirstOrder.Theory ℒₛₑₜ} [T.Δ₁] [U.Δ₁]

example (hP : Good P)
    (hTerm : ∀ t : V, IsTerm ℒₛₑₜ t → ∃ j, t = ^&j)
    (hAx : ∀ p : V, IsFormula ℒₛₑₜ p → p ∈ T.Δ₁Class →
      ∃ m, Derivable U (insert (interp P p) (domSet ℒₛₑₜ (dom P) m)))
    {der : V} (h : Derivation T der) :
    ∃ m, Derivable U (iSet P (fstIdx der) ∪ domSet ℒₛₑₜ (dom P) m) :=
  derivable_iSet hP hTerm hAx h

example (hP : Good P)
    (hAx : ∀ p : V, IsFormula ℒₛₑₜ p → p ∈ T.Δ₁Class →
      ∃ m, Derivable U (insert (interp P p) (domSet ℒₛₑₜ (dom P) m)))
    {der : V} (h : Derivation T der) :
    ∃ m, Derivable U (iSet P (fstIdx der) ∪ domSet ℒₛₑₜ (dom P) m) :=
  derivable_iSet hP (fun _ ht => SetRelativization.isTerm_eq_fvar ht) hAx h

example (hP : Good P)
    (hAx : ∀ p : V, IsFormula ℒₛₑₜ p → p ∈ T.Δ₁Class →
      ∃ m, Derivable U (insert (interp P p) (domSet ℒₛₑₜ (dom P) m)))
    (hne : Provable U (^∃ (dom P))) {φ : V}
    (hφ : Provable T φ) (hs : shift ℒₛₑₜ φ = φ) : Provable U (interp P φ) :=
  provable_interp hP (fun _ ht => SetRelativization.isTerm_eq_fvar ht) hAx hne hφ hs

example (hP : Good P)
    (hAx : ∀ p : V, IsFormula ℒₛₑₜ p → p ∈ T.Δ₁Class →
      ∃ m, Derivable U (insert (interp P p) (domSet ℒₛₑₜ (dom P) m)))
    (hne : Provable U (^∃ (dom P))) (h : Provable T (^⊥ : V)) : Provable U (^⊥ : V) :=
  provable_falsum_of_interp hP (fun _ ht => SetRelativization.isTerm_eq_fvar ht) hAx hne h
