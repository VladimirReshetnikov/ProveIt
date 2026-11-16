module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqBinaryCoherenceSyntax
public import M6PA.Calibration.NumericPAeqValueCoherencePairwiseCode
public import M6PA.Calibration.RelationalClosedCertificateCoherenceSupply
public import M6PA.Calibration.RelationalPredicateBinaryTemplates
@[expose] public section
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem binaryRelation_addition_quote : binaryRelation (domain (V:=V)) addition isoPredicate=
    ⌜RelationalSource.PairGraph.addCoherenceStatement⌝ := by
  change binaryRelation (domain (V:=V)) addition isoPredicate=⌜∀¹
    (RelationalSource.Ordinal.domain (.bvar 0) 🡒 ∀¹ ∀¹ ∀¹ ∀¹ ∀¹
      ((RelationalSource.Ordinal.domain (.bvar 4) ⋏ (RelationalSource.Ordinal.domain (.bvar 3) ⋏
        (RelationalSource.Ordinal.domain (.bvar 2) ⋏ (RelationalSource.PairGraph.orderIso (.bvar 5) (.bvar 4) ⋏
          (RelationalSource.PairGraph.orderIso (.bvar 3) (.bvar 2) ⋏
            (RelationalSource.PairGraph.addResult (.bvar 5) (.bvar 3) (.bvar 1) ⋏
              RelationalSource.PairGraph.addResult (.bvar 4) (.bvar 2) (.bvar 0))))))) 🡒
        RelationalSource.PairGraph.orderIso (.bvar 1) (.bvar 0)))⌝
  simp [binaryRelation,binaryPoint,←FFL.FirstOrder.Semiterm.typed_quote_bvar]
#print axioms binaryRelation_addition_quote
theorem binaryRelation_multiplication_quote : binaryRelation (domain (V:=V)) multiplication isoPredicate=
    ⌜RelationalSource.PairGraph.mulCoherenceStatement⌝ := by
  change binaryRelation (domain (V:=V)) multiplication isoPredicate=⌜∀¹
    (RelationalSource.Ordinal.domain (.bvar 0) 🡒 ∀¹ ∀¹ ∀¹ ∀¹ ∀¹
      ((RelationalSource.Ordinal.domain (.bvar 4) ⋏ (RelationalSource.Ordinal.domain (.bvar 3) ⋏
        (RelationalSource.Ordinal.domain (.bvar 2) ⋏ (RelationalSource.PairGraph.orderIso (.bvar 5) (.bvar 4) ⋏
          (RelationalSource.PairGraph.orderIso (.bvar 3) (.bvar 2) ⋏
            (RelationalSource.PairGraph.mulResult (.bvar 5) (.bvar 3) (.bvar 1) ⋏
              RelationalSource.PairGraph.mulResult (.bvar 4) (.bvar 2) (.bvar 0))))))) 🡒
        RelationalSource.PairGraph.orderIso (.bvar 1) (.bvar 0)))⌝
  simp [binaryRelation,binaryPoint,←FFL.FirstOrder.Semiterm.typed_quote_bvar]
#print axioms binaryRelation_multiplication_quote
end M6.PA.NumericPAeqValueCoherence
