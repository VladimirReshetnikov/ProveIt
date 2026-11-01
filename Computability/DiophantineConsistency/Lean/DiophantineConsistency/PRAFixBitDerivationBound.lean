import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRABitFullWitnessBound
import DiophantineConsistency.PRARewritingWitnessBound
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic
/-! Bind the concrete positive bit graph into Foundation derivation. The
    bounded limSeqDef hypothesis is explicit and not supplied here. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRAFixBitDerivationBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {L : Language} [L.Encodable] [L.LORDefinable] (T : Theory L) [T.Δ₁]
noncomputable def actualBody : ArithmeticSemisentence 2 :=
  “s d. !((Derivation.blueprint T).limSeqDef) s (d+1) ∧ d ∈ s”
noncomputable def limInsideBody : ArithmeticSemisentence 2 :=
  “s d. !((Derivation.blueprint T).limSeqDef) s (d+1)”
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] bitDef

theorem body_bound (d s w : V) (hw : PRABitFullWitnessBound.bitMajorant s ≤ w)
    (hbit : bitDef.val.Evalb ![d,s])
    (hlim : (bnd (limInsideBody T)).Evalb ![s,d,w]) :
    (bnd (actualBody T)).Evalb ![s,d,w] := by
  simp [actualBody,bnd]
  constructor
  · exact hlim
  · letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
    let ω : Rew ℒₒᵣ Empty 2 Empty 2 := Rew.subst ![#1,#0]
    simpa [Semiformula.Operator.operator, operator_mem_def, Rewriting.emb] using
      (PRARewritingWitnessBound.binary_rew_bound_with bitDef.val
        (fun _ s => PRABitFullWitnessBound.bitMajorant s)
        PRABitFullWitnessBound.bit_bound ω ![s,d] w
        (by simpa [ω] using hw) (by simpa [ω, Semiformula.eval_substs] using hbit))

theorem derivation_bound_of_witness (d s w : V) (hs : s < w)
    (hw : PRABitFullWitnessBound.bitMajorant s ≤ w)
    (hbit : bitDef.val.Evalb ![d,s])
    (hlim : (bnd (limInsideBody T)).Evalb ![s,d,w]) :
    (bnd (derivation T).sigma.val).Evalb ![d,w] := by
  rw [show (derivation T).sigma.val = ∃⁰ actualBody T by
    simp [derivation, Fixpoint.Blueprint.fixpointDefΔ₁, actualBody]]
  simp only [bnd, Semiformula.eval_bexs]
  refine ⟨s,?_,body_bound T d s w hw hbit hlim⟩
  simpa [val_lastVar] using hs
noncomputable def boundedLim : ArithmeticSemisentence 3 := bnd (limInsideBody T)
noncomputable def boundedDerivation : ArithmeticSemisentence 2 := bnd (derivation T).sigma.val
noncomputable def derivationBoundBody : ArithmeticSemisentence 3 :=
  “d s w. s < w ∧ (((s⁴+1)+(s²+1)+(2*s²+1)+(s⁴+s⁴+2*s+1))+s+1) ≤ w ∧ !bitDef d s ∧ !((boundedLim T)) s d w → !((boundedDerivation T)) d w”

theorem derivationBoundBody_model (e : Fin 3 → V) : (derivationBoundBody T).Eval e Empty.elim := by
  simp [derivationBoundBody, boundedLim, boundedDerivation, Semiformula.eval_substs]
  exact derivation_bound_of_witness T (e 0) (e 1) (e 2)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

noncomputable def derivationBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding (derivationBoundBody T)

theorem candidate_proves_derivation_bound : PRA ⊢ derivationBoundSentence T := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact derivationBoundBody_model T e
end DiophantineConsistency.PRAFixBitDerivationBound
