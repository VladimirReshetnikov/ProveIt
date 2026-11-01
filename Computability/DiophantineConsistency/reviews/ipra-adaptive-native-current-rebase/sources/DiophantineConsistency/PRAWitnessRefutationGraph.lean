import DiophantineConsistency.PRAWitnessClosedExistential
import DiophantineConsistency.PRAWitnessArithmetic
import DiophantineConsistency.PRAHistoryTruncation

/-! Fixed provability predicates have only two outer existential witnesses;
the internal derivation graph remains the substantive bound obligation. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRAWitnessRefutationGraph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCalculus PRAWitnessArithmetic PRAWitnessClosedExistential
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
variable {L : Language} [L.Encodable] [L.LORDefinable]

theorem wb_rewAux {k n : ℕ} (ω : Rew ℒₒᵣ Empty k Empty n)
    {ψ : ArithmeticSemisentence k} (hψ : WB M ψ) :
    WB M (Semiformula.rewAux ω ψ) := wb_rew ω hψ

theorem wb_provabilityPred (T : Theory L) [T.Δ₁] (σ : Sentence L)
    (hd : WB M (derivation T).sigma.val) : WB M (provabilityPred T σ) := by
  have := wb_insertDef (M := M)
  have := wb_fstIdxDef (M := M)
  have := hd
  simp only [provabilityPred, provable, proof, derivationOf,
    HierarchySymbol.Semiformula.sigma_mkDelta, HierarchySymbol.Semiformula.val_mkSigma]
  apply wb_exs_exs_sentence
  apply wb_rewAux
  apply wb_rewAux
  wb_auto

section candidate
open PRAFiniteFunctionCodes PRALanguage PRATheory
variable {N : Type} [Nonempty N] [Structure language N] [Structure.Eq language N]
  [N↓[language] ⊧* PRA]
local instance : Zero N := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One N := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add N := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul N := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT N := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- For a fixed sentence, the two actual derivation-core bounds suffice for
the full Foundation provability predicate's witness bound. -/
theorem wb_provabilityPred_of_core (T : Theory L) [T.Δ₁] (σ : Sentence L)
    (hσ : WB N (Derivation.blueprint T).core.sigma.val)
    (hπ : WB N (∼(Derivation.blueprint T).core.pi.val)) :
    WB N (provabilityPred T σ) := by
  letI : N↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : N↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  exact wb_provabilityPred T σ (PRAHistoryTruncation.wb_fixpoint_sigma _ hσ hπ)
end candidate

end DiophantineConsistency.PRAWitnessRefutationGraph
