module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionTransitivitySupplier
public import M6PA.Calibration.RelationalAdditionCoherenceRules
@[expose] public section

/-! Parameter-close an already fully supplied transitivity theorem. No free
Separation premise is generalized; all three object parameters are genuinely bound. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] orderIso Ordinal.domain
set_option maxHeartbeats 600000

def isoTransitivityClosed : Form :=
  closeParameter (closeParameter (closeParameter (compositionTransitivityStatement 2 1 0)))

theorem shiftedLabelsBound (f : Nat → Nat) (lo : Nat) (hf : ∀i,f i<lo) :
    ∀i,shiftedLabels f lo i < lo+1 := by
  intro i
  cases i with
  | zero => simp [shiftedLabels]
  | succ i => simpa [shiftedLabels] using Nat.lt_trans (hf i) (Nat.lt_succ_self lo)

def isoTransitivityClosedSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0<lo) (hf : ∀i,f i<lo) (hz : lo+9<z)
    (hsep : lo+8+depth (∼compositionProperty 1 0 (2+1+1))≤z)
    (hadj : lo+5+lkBudget adjunctionDerivation≤z)
    (hbudget : lo+3+lkBudget (compositionTransitivityDerivation 2 1 0)≤z) :
    NativeCalculus.ActualBasis.Proof (code isoTransitivityClosed f lo z) := by
  apply closeParameterSupplier
  apply closeParameterSupplier
  apply closeParameterSupplier
  apply compositionTransitivitySupplier 2 1 0 _ (lo+1+1+1) z (by omega)
    (shiftedLabelsBound _ _ (shiftedLabelsBound _ _ (shiftedLabelsBound f lo hf)))
    (by omega) (by omega) (by omega) (by omega)

theorem isoTransitivityClosed_eq : isoTransitivityClosed =
    ∀¹ ∀¹ ∀¹ ((Ordinal.domain (.bvar 2) ⋏
      (orderIso (.bvar 2) (.bvar 1) ⋏ orderIso (.bvar 1) (.bvar 0))) 🡒
        orderIso (.bvar 2) (.bvar 0)) := by
  simp only [isoTransitivityClosed,closeParameter,compositionTransitivityStatement,
    orderIso_rew,Ordinal.domain_rew,coherenceRewNeg,Semiformula.rewAux,
    Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq]
  finishSourceSyntax

def isoTransitivityClosedAt {Γ : List Form} (a b c : Nat)
    (h : ND.Proof Γ isoTransitivityClosed)
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a)))
    (hab : ND.Proof Γ (orderIso (.fvar a) (.fvar b)))
    (hbc : ND.Proof Γ (orderIso (.fvar b) (.fvar c))) :
    ND.Proof Γ (orderIso (.fvar a) (.fvar c)) := by
  rw [isoTransitivityClosed_eq] at h
  have out := allElim _ (.fvar c) (allElim _ (.fvar b) (allElim _ (.fvar a) h))
  have hi : ND.Proof Γ ((Ordinal.domain (.fvar a) ⋏
      (orderIso (.fvar a) (.fvar b) ⋏ orderIso (.fvar b) (.fvar c))) 🡒
        orderIso (.fvar a) (.fvar c)) := by
    convert out using 1 <;> addCoherenceSyntax
  exact mp (andIntro ha (andIntro hab hbc)) hi

#print axioms isoTransitivityClosedSupplier
#print axioms isoTransitivityClosed_eq
#print axioms isoTransitivityClosedAt
end M6.PA.RelationalSource.PairGraph
