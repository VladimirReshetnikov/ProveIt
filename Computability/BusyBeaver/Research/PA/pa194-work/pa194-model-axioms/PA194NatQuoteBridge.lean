import PA194NatStructureBridge
import PA194TypedClass
import ConPAISigma1Models
set_option autoImplicit false
namespace PA194NatQuoteBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194NatStructureBridge PA194BindSource PA194ModelLogic

def canonicalSigma : letI : ORingStructure Nat := canonicalNatORing; Nat↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := by
  exact models_ISigmaOne

def inducedSigma : letI : ORingStructure Nat := inducedNatORing; Nat↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := by
  rw [induced_eq_canonical]
  exact canonicalSigma

theorem eval_bridge (q : Nat) :
    (letI : ORingStructure Nat := inducedNatORing; Nat ⊧/![q] fullSepUniform.val) ↔
    (letI : ORingStructure Nat := canonicalNatORing; Nat ⊧/![q] fullSepUniform.val) := by
  rw [induced_eq_canonical]

theorem quote_congr (A B : ORingStructure Nat) (h : A = B)
    (hA : letI : ORingStructure Nat := A; Nat↓[ℒₒᵣ] ⊧* 𝗜𝚺₁)
    (hB : letI : ORingStructure Nat := B; Nat↓[ℒₒᵣ] ⊧* 𝗜𝚺₁)
    (σ : Sentence SourceL) :
    (letI : ORingStructure Nat := A; letI := hA; (⌜σ⌝ : Nat)) =
    (letI : ORingStructure Nat := B; letI := hB; (⌜σ⌝ : Nat)) := by
  subst B
  rfl

theorem quote_bridge (σ : Sentence SourceL) :
    (letI : ORingStructure Nat := inducedNatORing; letI := inducedSigma; (⌜σ⌝ : Nat)) =
    (letI : ORingStructure Nat := canonicalNatORing; letI := canonicalSigma; (⌜σ⌝ : Nat)) :=
  quote_congr inducedNatORing canonicalNatORing induced_eq_canonical inducedSigma canonicalSigma σ

theorem semiQuote_congr (A B : ORingStructure Nat) (h : A = B)
    (hA : letI : ORingStructure Nat := A; Nat↓[ℒₒᵣ] ⊧* 𝗜𝚺₁)
    (hB : letI : ORingStructure Nat := B; Nat↓[ℒₒᵣ] ⊧* 𝗜𝚺₁)
    {n : Nat} (φ : Semiproposition SourceL n) :
    (letI : ORingStructure Nat := A; letI := hA; (⌜φ⌝ : Nat)) =
    (letI : ORingStructure Nat := B; letI := hB; (⌜φ⌝ : Nat)) := by
  subst B
  rfl

theorem semiValidity_congr (A B : ORingStructure Nat) (h : A = B)
    (hA : letI : ORingStructure Nat := A; Nat↓[ℒₒᵣ] ⊧* 𝗜𝚺₁)
    (hB : letI : ORingStructure Nat := B; Nat↓[ℒₒᵣ] ⊧* 𝗜𝚺₁)
    (n q : Nat) :
    (letI : ORingStructure Nat := A; letI := hA; IsSemiformula SourceL n q) ↔
    (letI : ORingStructure Nat := B; letI := hB; IsSemiformula SourceL n q) := by
  subst B
  rfl

#print axioms semiQuote_congr
#print axioms semiValidity_congr
#print axioms eval_bridge
#print axioms quote_bridge
end PA194NatQuoteBridge
