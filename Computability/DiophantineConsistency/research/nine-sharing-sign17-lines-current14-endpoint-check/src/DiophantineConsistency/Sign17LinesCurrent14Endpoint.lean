import DiophantineConsistency.Sign17LiteralPorts
import DiophantineConsistency.Sign17LinesKernel
import DiophantineConsistency.IPRAStandardCurrentEndpoint

/-! SOURCE ONLY. The current 14-variable iPRA endpoint at numeral-derived K. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17LinesCurrent14Endpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRANoZeroUnary FoundationHANoZero
open ObjectCurrentEquation2011 IPRAStandardTheory IPRACurrentNativeZFC
open IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat

def linePorts : Fin 4 → ℤ := ![
  (CurrentMasks2011.beta : ℤ), (Sign17LinesKernel.lineK : ℤ),
  (CurrentMasks2011.lowPort : ℤ), ((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : ℤ)]

theorem linePorts_eq : linePorts = CurrentWindowCarry2011.ports := by
  unfold linePorts
  rw [Sign17LinesKernel.lineK_eq]
  rfl

theorem linePorts_recipes :
    linePorts 0 = Current14LiteralPortsMF.beta ∧
    (linePorts 1 : ℚ) = Current14LiteralPortsMF.K ∧
    linePorts 2 = Current14LiteralPortsMF.mu ∧
    linePorts 3 = Current14LiteralPortsMF.omega := by
  rw [linePorts_eq]
  exact Current14LiteralPortsMF.all_ports

def noZeroAt (p : Fin 4 → ℤ) : Sentenceᵢ language :=
  let e := positiveShift (expressionAt p)
  ∀⁰* (∼(Semiformulaᵢ.rel Language.ORing.Rel.eq
    ![Semiterm.lMap embedding (sourceTerm 14 (ArithmeticExpression.term Fin.val e.splitNatural.1)),
      Semiterm.lMap embedding (sourceTerm 14 (ArithmeticExpression.term Fin.val e.splitNatural.2))]))

theorem line_endpoint :
    standardTheory ⊢ noZeroAt linePorts 🡘 ∼mappedNativeRefutation embedding := by
  rw [linePorts_eq]
  change standardTheory ⊢ noZero14 🡘 ∼mappedNativeRefutation embedding
  exact IPRAStandardCurrentEndpoint.ipra_current_iff_consistency

theorem line_endpoint_translated :
    standardTheory ⊢ noZeroAt linePorts 🡘 (Semiformula.lMap embedding sourceSentence)ᴺ := by
  rw [linePorts_eq]
  change standardTheory ⊢ noZero14 🡘 (Semiformula.lMap embedding sourceSentence)ᴺ
  exact IPRAStandardCurrentEndpoint.ipra_current_iff_translated_consistency

end DiophantineConsistency.Sign17LinesCurrent14Endpoint
#print axioms DiophantineConsistency.Sign17LinesCurrent14Endpoint.linePorts_eq
#print axioms DiophantineConsistency.Sign17LinesCurrent14Endpoint.linePorts_recipes
#print axioms DiophantineConsistency.Sign17LinesCurrent14Endpoint.line_endpoint
#print axioms DiophantineConsistency.Sign17LinesCurrent14Endpoint.line_endpoint_translated
