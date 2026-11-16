module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeInductionClosure
@[expose] public section
/-! Bounded canonical inverse recognizer for the literal PAeq induction scheme.
No existential syntax-image decidability is presumed. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def targetInductionR (p : V) : Prop :=
  ∃ m ≤ p, ∃ b ≤ p,
    p = qqAlls b m ∧ IsUFormula Presentation.language b ∧ shift Presentation.language b = b ∧ bv Presentation.language b = m
    ∧ ∃ K ≤ subst Presentation.language (fvarVec m) b,
        IsSemiformula Presentation.language 1 K ∧ subst Presentation.language (fvarVec m) b = targetIndBody K

noncomputable def targetInductionCh : 𝚫ᴬ₁.Semisentence 1 := .mkDelta
  (.mkSigma “p.
    ∃ m < p + 1, ∃ b < p + 1,
      !qqAllsDef p b m ∧ !(isUFormula Presentation.language).sigma b
      ∧ !(shiftGraph Presentation.language) b b ∧ !(bvGraph Presentation.language) m b
      ∧ ∃ fv, !fvarVecDef fv m ∧ ∃ s, !(substsGraph Presentation.language) s fv b
        ∧ ∃ K < s + 1, !(isSemiformula Presentation.language).sigma 1 K
          ∧ !targetIndBodyGraph s K”)
  (.mkPi “p.
    ∃ m < p + 1, ∃ b < p + 1,
      (∀ y, !qqAllsDef y b m → y = p) ∧ !(isUFormula Presentation.language).pi b
      ∧ (∀ y, !(shiftGraph Presentation.language) y b → y = b)
      ∧ (∀ y, !(bvGraph Presentation.language) y b → y = m)
      ∧ ∀ fv, !fvarVecDef fv m → ∀ s, !(substsGraph Presentation.language) s fv b
        → ∃ K < s + 1, !(isSemiformula Presentation.language).pi 1 K
          ∧ ∀ ib, !targetIndBodyGraph ib K → s = ib”)

instance targetInductionR_defined :
    𝚫ᴬ₁-Predicate[V] (targetInductionR : V → Prop) via targetInductionCh := .mk <| by
  constructor;
  · intro v; simp [targetInductionCh, Bounding.HierarchySymbol.Semiformula.val_sigma, eq_comm];
  · intro v;
    simp [targetInductionCh, Bounding.HierarchySymbol.Semiformula.val_sigma, targetInductionR, lt_succ_iff_le,
      eq_comm];

#print axioms targetInductionR_defined
end M6.PA.FoundationPAeqCode

