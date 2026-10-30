import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRAFormulaSetWitnessBound
/-! At arity zero the semiformula sigma graph has BV witness zero.
    The bounded isUFormula and BV graph premises remain explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRASemiFormulaSigmaBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] isUFormula bvGraph

noncomputable def uInside : ArithmeticSemisentence 2 := “n p. !(isUFormula L).sigma p”
noncomputable def bvInside : ArithmeticSemisentence 3 := “b n p. !(bvGraph L) b p”

theorem semiformula_sigma_zero_bound (p w : V) (hw : 0 < w)
    (hU : (bnd (uInside (L := L))).Evalb ![0,p,w])
    (hBV : (bnd (bvInside (L := L))).Evalb ![0,0,p,w]) :
    (bnd (isSemiformula L).sigma.val).Evalb ![0,p,w] := by
  simp [isSemiformula,bnd,bnd_open]
  exact ⟨hU,hw,hBV⟩
noncomputable def boundedUInside : ArithmeticSemisentence 3 := bnd (uInside (L := L))
noncomputable def boundedBvInside : ArithmeticSemisentence 4 := bnd (bvInside (L := L))
noncomputable def boundedSemiSigma : ArithmeticSemisentence 3 := bnd (isSemiformula L).sigma.val
noncomputable def semiSigmaZeroBody : ArithmeticSemisentence 2 :=
  “p w. 0 < w ∧ !((boundedUInside (L := L))) 0 p w ∧ !((boundedBvInside (L := L))) 0 0 p w → !((boundedSemiSigma (L := L))) 0 p w”

theorem semiSigmaZeroBody_model (e : Fin 2 → V) : (semiSigmaZeroBody (L := L)).Eval e Empty.elim := by
  simp [semiSigmaZeroBody, boundedUInside, boundedBvInside, boundedSemiSigma, Semiformula.eval_substs]
  exact semiformula_sigma_zero_bound (e 0) (e 1)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

noncomputable def semiSigmaZeroSentence : Sentence language := ∀⁰* Semiformula.lMap embedding (semiSigmaZeroBody (L := L))

theorem candidate_proves_semiSigmaZero_bound : PRA ⊢ semiSigmaZeroSentence (L := L) := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact semiSigmaZeroBody_model e
end DiophantineConsistency.PRASemiFormulaSigmaBound
