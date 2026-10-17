import BoundedPAConsistency.InternalRelativization

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.InternalRelativization
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.BoundedPAConsistency.InternalRelativization.isUFormula_relativize
#print axioms LeanProofs.BoundedPAConsistency.InternalRelativization.isSemiformula_relativize
#print axioms LeanProofs.BoundedPAConsistency.InternalRelativization.relativize_neg
#print axioms LeanProofs.BoundedPAConsistency.InternalRelativization.relativize_shift
#print axioms LeanProofs.BoundedPAConsistency.InternalRelativization.subst_eq_self_of_prefix
#print axioms LeanProofs.BoundedPAConsistency.InternalRelativization.subst_qVec_domain
#print axioms LeanProofs.BoundedPAConsistency.InternalRelativization.relativize_subst
#print axioms LeanProofs.BoundedPAConsistency.InternalRelativization.relativize_substs1
#print axioms LeanProofs.BoundedPAConsistency.InternalRelativization.relativize_free
#print axioms LeanProofs.BoundedPAConsistency.InternalRelativization.setShift_relSet
#print axioms LeanProofs.BoundedPAConsistency.InternalRelativization.derivable_relSet

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

example (d p : V) (hd : IsUFormula L d) (hp : IsUFormula L p) :
    IsUFormula L (relativize L d p) := isUFormula_relativize hd hp
example (d depth p : V) (hd : IsSemiformula L 1 d)
    (hp : IsSemiformula L depth p) :
    IsSemiformula L depth (relativize L d p) := isSemiformula_relativize hd hp
example (d p : V) (hd : IsSemiformula L 1 d) (hp : IsFormula L p) :
    IsFormula L (relativize L d p) := isSemiformula_relativize hd hp
example (d p : V) (hd : IsUFormula L d) (hp : IsUFormula L p) :
    neg L (relativize L d p) = relativize L d (neg L p) := relativize_neg hd hp
example (d p : V) (hd : IsSemiformula L 1 d) (hds : shift L d=d)
    (hp : IsUFormula L p) :
    shift L (relativize L d p) = relativize L d (shift L p) := relativize_shift hd hds hp
example (k p m a w : V) (hp : IsSemiformula L k p) (hw : IsSemitermVec L m a w)
    (hkm : k≤m) (hprefix : ∀ i<k, w.[i]=^#i) :
    subst L w p=p := subst_eq_self_of_prefix hp hw hkm hprefix
example (d n a w : V) (hd : IsSemiformula L 1 d) (hw : IsSemitermVec L n a w) :
    subst L (qVec L w) d=d := subst_qVec_domain hd hw
example (d n p a w : V) (hd : IsSemiformula L 1 d) (hp : IsSemiformula L n p)
    (hw : IsSemitermVec L n a w) :
    subst L w (relativize L d p)=relativize L d (subst L w p) := relativize_subst hd hp hw
example (d n t p : V) (hd : IsSemiformula L 1 d) (ht : IsSemiterm L n t)
    (hp : IsSemiformula L 1 p) :
    substs1 L t (relativize L d p)=relativize L d (substs1 L t p) := relativize_substs1 hd ht hp
example (d p : V) (hd : IsSemiformula L 1 d) (hds : shift L d=d)
    (hp : IsSemiformula L 1 p) :
    free L (relativize L d p)=relativize L d (free L p) := relativize_free hd hds hp
example (d s : V) (hd : IsSemiformula L 1 d) (hds : shift L d=d)
    (hs : IsFormulaSet L s) :
    setShift L (relSet L d s)=relSet L d (setShift L s) := setShift_relSet hd hds hs
example (T U : Theory L) [T.Δ₁] [U.Δ₁] (d der : V)
    (hd : IsSemiformula L 1 d) (hds : shift L d=d)
    (hTerm : ∀ t : V, IsTerm L t → ∃ j : V, t=^&j)
    (hAx : ∀ p : V, IsFormula L p → p∈T.Δ₁Class →
      ∃ m : V, Derivable U (insert (relativize L d p) (domSet L d m)))
    (hder : Derivation T der) :
    ∃ m : V, Derivable U (relSet L d (fstIdx der) ∪ domSet L d m) :=
  derivable_relSet hd hds hTerm hAx hder
