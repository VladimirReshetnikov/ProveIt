module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaEqualityTransportBoth
public import M6PA.Calibration.NumericPAeqFormulaEqualityTransportCode
@[expose] public section
namespace M6.PA.NumericPAeqFormulaEqualityTransport
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary NumericPAeqValueCoherence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
variable {T : InternalTheory V RelationalSource.language}
noncomputable def transportProof (D P Q U W : SF (V:=V) 1) (R : SF (V:=V) 2) :
    ND.Proof (T:=T) (insert (∼(symmetry D R ⋏ transitivity D R)) ∅) (transportStatement D P Q U W R) := by
  apply ND.impIntro
  let I := pairwise (D ⋏ P) (D ⋏ U) R ⋏ (pairwise (D ⋏ Q) (D ⋏ W) R ⋏
    ((∃¹ (D ⋏ P)) ⋏ ((∃¹ (D ⋏ Q)) ⋏ ((∃¹ (D ⋏ U)) ⋏ (∃¹ (D ⋏ W))))))
  let C : ND.Seq (V:=V) := insert (∼I) (insert (∼(symmetry D R ⋏ transitivity D R)) ∅)
  have hi : ND.Proof (T:=T) C I := ND.assumption _ (by simp [C])
  have hl : ND.Proof (T:=T) C (symmetry D R ⋏ transitivity D R) := ND.assumption _ (by simp [C])
  exact transportBoth D P Q U W R (ND.andLeft hl) (ND.andRight hl)
    (ND.andLeft hi) (ND.andLeft (ND.andRight hi))
    (ND.andLeft (ND.andRight (ND.andRight hi)))
    (ND.andLeft (ND.andRight (ND.andRight (ND.andRight hi))))
    (ND.andLeft (ND.andRight (ND.andRight (ND.andRight (ND.andRight hi)))))
    (ND.andRight (ND.andRight (ND.andRight (ND.andRight (ND.andRight hi)))))

theorem symmetry_quote : symmetry (domain (V:=V)) isoPredicate =
    ⌜RelationalSource.PairGraph.isoSymmetryClosed⌝ := by
  rw [RelationalSource.PairGraph.isoSymmetryClosed_eq]
  simp [symmetry,←FFL.FirstOrder.Semiterm.typed_quote_bvar]
theorem transitivity_quote : transitivity (domain (V:=V)) isoPredicate =
    ⌜RelationalSource.PairGraph.isoTransitivityClosed⌝ := by
  rw [RelationalSource.PairGraph.isoTransitivityClosed_eq]
  simp [transitivity,←FFL.FirstOrder.Semiterm.typed_quote_bvar]
#print axioms transportProof
#print axioms symmetry_quote
#print axioms transitivity_quote
end M6.PA.NumericPAeqFormulaEqualityTransport
