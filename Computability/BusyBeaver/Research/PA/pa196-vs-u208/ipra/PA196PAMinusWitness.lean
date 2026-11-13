import DiophantineConsistency.PRAWitnessZFCAxioms
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1

/-! Positive and negative witness bounds for the finite PA-minus component
of Foundation's actual PA axiom recognizer. The induction-schema component
and the derivation-core bounds are not established here. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace PA196PAMinusWitness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes DiophantineConsistency.PRALanguage
open DiophantineConsistency.PRATheory DiophantineConsistency.PRAWitnessCalculus
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- The two bounds refer to the specified recognizer, not an arbitrary
extensionally equivalent recognizer. -/
def GoodCh {T : Theory L} (d : T.Δ₁) (M : Type) [Nonempty M] [Structure language M]
    [Structure.Eq language M] [M↓[language] ⊧* PRA] : Prop :=
  WB M d.ch.sigma.val ∧ WB M (∼d.ch.pi.val)

theorem good_singleton (φ : Sentence L) : GoodCh (Theory.Δ₁.singleton φ) M := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := DiophantineConsistency.PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  constructor
  · change WB M (HierarchySymbol.Semiformula.ofZero
      (.mkSigma “x. x = ↑(Encodable.encode φ)” : 𝚺₀.Semisentence 1) 𝚫₁).sigma.val
    simp only [HierarchySymbol.Semiformula.ofZero, HierarchySymbol.Semiformula.sigma_mkDelta,
      HierarchySymbol.Semiformula.val_mkSigma]
    wb_auto
  · change WB M (∼(HierarchySymbol.Semiformula.ofZero
      (.mkSigma “x. x = ↑(Encodable.encode φ)” : 𝚺₀.Semisentence 1) 𝚫₁).pi.val)
    simp only [HierarchySymbol.Semiformula.ofZero, HierarchySymbol.Semiformula.pi_mkDelta,
      HierarchySymbol.Semiformula.val_mkPi, HierarchySymbol.Semiformula.val_mkSigma]
    wb_auto

theorem good_empty : GoodCh (Theory.Δ₁.empty (L := L)) M := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := DiophantineConsistency.PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  constructor
  · change WB M (⊥ : 𝚫₁.Semisentence 1).sigma.val
    simp only [HierarchySymbol.Semiformula.sigma_falsum, HierarchySymbol.Semiformula.val_falsum]; wb_auto
  · change WB M (∼(⊥ : 𝚫₁.Semisentence 1).pi.val)
    simp only [HierarchySymbol.Semiformula.pi_falsum, HierarchySymbol.Semiformula.val_falsum]; wb_auto

theorem good_add {T U : Theory L} (dT : T.Δ₁) (dU : U.Δ₁)
    (hT : GoodCh dT M) (hU : GoodCh dU M) : GoodCh (Theory.Δ₁.add dT dU) M := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := DiophantineConsistency.PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := hT.1; have := hT.2; have := hU.1; have := hU.2
  constructor
  · change WB M (dT.ch ⋎ dU.ch).sigma.val
    simp only [HierarchySymbol.Semiformula.sigma_or, HierarchySymbol.Semiformula.val_or]; wb_auto
  · change WB M (∼(dT.ch ⋎ dU.ch).pi.val)
    simp only [HierarchySymbol.Semiformula.pi_or, HierarchySymbol.Semiformula.val_or]; wb_auto

theorem good_ofEq {T U : Theory L} (dT : T.Δ₁) (h : T = U) (hT : GoodCh dT M) :
    GoodCh (Theory.Δ₁.ofEq dT h) M := hT

theorem good_list : ∀ l : List (Sentence L), GoodCh (Theory.Δ₁.ofList l) M
  | [] => good_ofEq _ _ good_empty
  | φ :: l => good_ofEq _ _ (good_add _ _ (good_singleton φ) (good_list l))

theorem good_finite (T : Theory L) (h : Set.Finite T) : GoodCh (Theory.Δ₁.ofFinite T h) M :=
  good_ofEq _ _ (good_list _)

/-- This is Foundation's exact finite PA-minus Δ₁ recognizer, used as the
left disjunct of its actual PA recognizer. -/
theorem good_paMinus : GoodCh (PeanoMinus.delta1) M :=
  good_finite (𝗣𝗔⁻ : ArithmeticTheory) PeanoMinus.finite

/-- The remaining PA axiom-recognizer obligation is the unrestricted
induction-schema recognizer; PA-minus itself is already discharged. -/
theorem good_pa_of_induction
    (hind : GoodCh (InductionScheme.delta1_univ) M) :
    GoodCh PA_delta1Definable M :=
  good_add PeanoMinus.delta1 InductionScheme.delta1_univ good_paMinus hind

#print axioms good_paMinus
#print axioms good_pa_of_induction
end PA196PAMinusWitness
