module
public import M6PA.Theory
public import M6PA.Calibration.RelationalOrderIsoClosedTransitivity
public import M6PA.Calibration.RelationalIsoInverseSymmetrySupplier
@[expose] public section

/-! Fully parameter-closed symmetry, supplied only after the inverse graph and
its finite Separation context have been discharged. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] orderIso Ordinal.domain
set_option maxHeartbeats 600000

def isoSymmetryClosed : Form :=
  closeParameter (closeParameter (inverseSymmetryStatement 1 0))

def isoSymmetryClosedSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0<lo) (hf : ∀i,f i<lo) (hz : lo+8<z)
    (hsep : lo+6+depth (∼inverseProperty 0 (1+1))≤z)
    (hadj : lo+4+lkBudget adjunctionDerivation≤z)
    (hbudget : lo+2+lkBudget (inverseSymmetryDerivation 1 0)≤z) :
    NativeCalculus.ActualBasis.Proof (code isoSymmetryClosed f lo z) := by
  apply closeParameterSupplier
  apply closeParameterSupplier
  apply inverseSymmetrySupplier 1 0 _ (lo+1+1) z (by omega)
    (shiftedLabelsBound _ _ (shiftedLabelsBound f lo hf))
    (by omega) (by omega) (by omega) (by omega)

theorem isoSymmetryClosed_eq : isoSymmetryClosed =
    ∀¹ ∀¹ ((Ordinal.domain (.bvar 1) ⋏ orderIso (.bvar 1) (.bvar 0)) 🡒
      orderIso (.bvar 0) (.bvar 1)) := by
  simp only [isoSymmetryClosed,closeParameter,inverseSymmetryStatement,
    orderIso_rew,Ordinal.domain_rew,coherenceRewNeg,Semiformula.rewAux,
    Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq]
  finishSourceSyntax

def isoSymmetryClosedAt {Γ : List Form} (a b : Nat)
    (h : ND.Proof Γ isoSymmetryClosed)
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a)))
    (hab : ND.Proof Γ (orderIso (.fvar a) (.fvar b))) :
    ND.Proof Γ (orderIso (.fvar b) (.fvar a)) := by
  rw [isoSymmetryClosed_eq] at h
  have out := allElim _ (.fvar b) (allElim _ (.fvar a) h)
  have hi : ND.Proof Γ ((Ordinal.domain (.fvar a) ⋏ orderIso (.fvar a) (.fvar b)) 🡒
      orderIso (.fvar b) (.fvar a)) := by
    convert out using 1 <;> addCoherenceSyntax
  exact mp (andIntro ha hab) hi

#print axioms isoSymmetryClosedSupplier
#print axioms isoSymmetryClosed_eq
#print axioms isoSymmetryClosedAt
end M6.PA.RelationalSource.PairGraph
