import PA194TypedSchema
import PA194FullSepTheoryModel
import PA194ModelStandardSourceDecode
import ConPAISigma1Models
import PA194NatQuoteBridge
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194TypedSchema
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194TypedSeparation PA194BindSource PA194ModelLogic M6.PA.RelationalSource
open PA194NatQuoteBridge PA194NatStructureBridge PA194TypedClass
open DiophantineConsistency PRALanguage PRATheory PRAModelIOpenPairing PRAAddOne PRAFiniteFunctionCodes
theorem fullSepTheory_eval_induced (σ : Sentence SourceL) :
    σ ∈ fullSepTheory ↔
      (letI : ORingStructure Nat := inducedNatORing; letI := inducedSigma;
        Nat ⊧/![(⌜σ⌝ : Nat)] fullSepUniform.val) := by
  change (letI : ORingStructure Nat := canonicalNatORing; letI := canonicalSigma;
    Nat ⊧/![(⌜σ⌝ : Nat)] fullSepUniform.val) ↔ _
  rw [← quote_bridge σ,eval_bridge]

local instance typedNatS : Structure PRALanguage.language Nat := natStructure
local instance typedNatEq : Structure.Eq PRALanguage.language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance typedNatPRA : Nat↓[PRALanguage.language] ⊧* PRA := nat_models_PRA
local notation "F" => Structure.func (L := PRALanguage.language) (M := Nat)
local instance typedNatZero : Zero Nat := ⟨F (Code.zero 0) Fin.elim0⟩
local instance typedNatOne : One Nat := ⟨F oneCode Fin.elim0⟩
local instance typedNatAdd : Add Nat := ⟨fun x y => F addCode ![x,y]⟩
local instance typedNatMul : Mul Nat := ⟨fun x y => F mulCode ![x,y]⟩
local instance typedNatLT : LT Nat := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance typedNatIOpen : Nat↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
local instance typedNatSigma : Nat↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := by
  have h := models_ISigmaOne
  rw [← nat_reduct, reduct_eq_standard] at h
  exact h

theorem standard_sourceFormula_quote_surjective_induced (x : Nat)
    (hx : IsSemiformula SourceL 1 x) :
    ∃ p : Semiproposition SourceL 1, (⌜p⌝ : Nat) = x := by
  have hc : (letI : ORingStructure Nat := canonicalNatORing; letI := canonicalSigma;
      IsSemiformula SourceL 1 x) :=
    (semiValidity_congr inducedNatORing canonicalNatORing induced_eq_canonical inducedSigma canonicalSigma 1 x).mp hx
  obtain ⟨p,hp⟩ := standard_sourceFormula_quote_surjective x 1 hc
  refine ⟨p,?_⟩
  have hq := semiQuote_congr inducedNatORing canonicalNatORing induced_eq_canonical inducedSigma canonicalSigma p
  exact hq.trans hp

theorem fullSepTheory_mem_iff_typed (σ : Sentence SourceL) :
    σ ∈ fullSepTheory ↔ ∃ p : Semiproposition SourceL 1, σ = (separationFormula p).univCl := by
  rw [fullSepTheory_eval_induced]
  change (Nat ⊧/![(⌜σ⌝ : Nat)] fullSepUniform.val) ↔ _
  rw [fullSepUniform_typed_of_surjective (⌜σ⌝ : Nat) standard_sourceFormula_quote_surjective_induced]
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨p, Sentence.quote_inj_iff.mp hp.symm⟩
  · rintro ⟨p,rfl⟩
    exact ⟨p,rfl⟩

#print axioms fullSepTheory_mem_iff_typed
end PA194TypedSchema
