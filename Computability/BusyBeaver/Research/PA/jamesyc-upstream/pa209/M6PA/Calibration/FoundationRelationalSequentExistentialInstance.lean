module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentAllRule
@[expose] public section

/-! Actual existential introduction from a guarded finite source-term label.
The witness label comes from real in-range lookup, never a default assumption. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCertificateEquivalence ActualCheckerBlueprint

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

private theorem exs_value (v a : V) :
    ActualArithmeticGraph.eval translationExs v a 0 0=wn (wal v (wn a)) := by
  simp [translationExs,ActualHeadGraphs.ex,ActualHeadGraphs.al,ActualHeadGraphs.neg,
    wn,wal,wim,implicationValue,universalValue,ActualHeadGraphs.universalExpr,
    ActualHeadGraphs.implicationExpr,ActualHeadGraphs.im,ActualArithmeticGraph.eval]

theorem existential_instance_certificate (p t y f lo z : V)
    (hc : FormulaCovered 0 f lo z (qqExs p)) (ht : VariableLabel y t 0 f) :
    ∃ code, verifyValue code=wim
      (translate (parameters 0 f (lo+1) z) (substs1 language t p))
      (translate (parameters 0 f lo z) (qqExs p))+1 := by
  have hp : IsSemiformula language 1 p := by simpa using hc.2.1
  have child := coverage_exs hc
  have hy : y<lo := label_below ht hc.1.1
  have hlz : lo<z := lt_of_lt_of_le (lt_add_one lo) child.1.1.2.1
  have hfy : z≠y := Ne.symm (ne_of_lt (lt_trans hy hlz))
  have fresh : FreshEnvironment lo 0 f (lo+1) z := environments_eigenFresh hc.1.1 (ne_of_lt hlz)
  have hb : RenameEnvironment lo y (lo∷0) (y∷0) := renameEnvironment_head fresh.2.2.1
  have hf : RenameEnvironment lo y f f := renameEnvironment_fixed fresh.2.2.2
  obtain ⟨forward,backward,hforward,hbackward⟩ := formula_rename_certificates p lo y (lo∷0) (y∷0)
    f f (lo+1) z child hb hf (lt_add_one lo) (lt_trans hy (lt_add_one lo))
  let a := translate (parameters (lo∷0) f (lo+1) z) p
  let b := translate (parameters (y∷0) f (lo+1) z) p
  let rename : ConditionalBiWitness (neighborhoodValue lo y z) a b :=
    ⟨⟨forward,hforward⟩,⟨backward,hbackward⟩⟩
  have targetCoverage := coverage_rename hb hf child (lt_trans hy (lt_add_one lo))
  obtain ⟨vac,hvac⟩ := formula_vacuity_certificate p lo (y∷0) f (lo+1) z targetCoverage
    (fresh.adjoin_avoiding (Ne.symm (ne_of_lt hy)))
  let spec := universalSpecializeNeighborhood lo y z (wn a) (wn b)
    (Ne.symm (ne_of_lt hlz)) hfy rename.neg.forward (negationVacuity lo b ⟨vac,hvac⟩)
  let out := implicationCompose (doubleNegationIntroduction b) (contrapose spec)
  refine ⟨out.code,?_⟩
  rw [translate_substs1 p t y 0 f (lo+1) z hp ht,translate_exs _ _ hp.isUFormula,
    parameters_allocator,advance_parameters,exs_value]
  exact out.accepted

theorem covered_existential_instance_certificate (p t f lo z : V)
    (hc : FormulaCovered 0 f lo z (qqExs p)) (ht : Covered t 0 f) :
    ∃ code, verifyValue code=wim
      (translate (parameters 0 f (lo+1) z) (substs1 language t p))
      (translate (parameters 0 f lo z) (qqExs p))+1 := by
  obtain ⟨y,hy⟩ := (label_exists_iff _ _ _).mpr ht
  exact existential_instance_certificate p t y f lo z hc hy

#print axioms existential_instance_certificate
#print axioms covered_existential_instance_certificate
end M6.PA.RelationalSource.Numeric

