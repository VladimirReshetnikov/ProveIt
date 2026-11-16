module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSequentGuardedPropositional
public import M6PA.Calibration.NumericPAeqInductionInterpretationSyntax
public import M6PA.Calibration.FoundationRelationalSequentConnectiveNormalization
@[expose] public section

/-! The exact outer-domain source formula used for requested-parameter proof
translation. Its native implication view is connected by accepted certificates. -/
namespace M6.PA.NumericPAeqFormula.Sequent
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open NumericPAeqInductionInterpretation (freeDomain freeDomain_valid)
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCertificateEquivalence ActualCheckerBlueprint
open RelationalSource.Numeric (translate translateGraph translate_graph translate_imp_certificates)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def guardedCode (f s : V) : V :=
  imp language (freeDomain f) (sequentCode (parameters 0 f) s)

attribute [local irreducible] parametersGraph sequentGraph NumericPAeqValueDomainGuard.guardGraph impGraph
noncomputable def guardedCodeGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out f s. ∃ n param guard folded, !lenDef n f ∧ !parametersGraph param 0 f ∧
    !NumericPAeqValueDomainGuard.guardGraph guard f n ∧ !sequentGraph folded param s ∧
    !(impGraph language) out guard folded”

theorem guardedCode_graph (out f s : V) : guardedCodeGraph.val.Evalb ![out,f,s] ↔
    out=guardedCode f s := by
  simp [guardedCodeGraph,guardedCode,freeDomain,parameters_graph,sequent_graph,
    NumericPAeqValueDomainGuard.guard_graph,Matrix.comp_vecCons'']

theorem guardedCode_valid {f s : V} (hf : IsSemitermVec language (len f) 0 f)
    (hs : SupportedSet (parameters 0 f) s) : IsFormula language (guardedCode f s) := by
  exact IsSemiformula.imp.mpr ⟨freeDomain_valid hf,sequent_valid _ _ 0 0 hs⟩

theorem guardedCode_native_certificates (native f s : V)
    (hf : IsSemitermVec language (len f) 0 f) (hs : SupportedSet (parameters 0 f) s) :
    ∃ forward backward, BiCertificates forward backward (translate native (guardedCode f s))
      (wim (translate native (freeDomain f)) (translate native (sequentCode (parameters 0 f) s))) :=
  translate_imp_certificates native _ _ (freeDomain_valid hf).isUFormula
    (sequent_valid _ _ 0 0 hs).isUFormula

theorem guardedCode_to_native (native f s child : V)
    (hf : IsSemitermVec language (len f) 0 f) (hs : SupportedSet (parameters 0 f) s)
    (hc : verifyValue child=translate native (guardedCode f s)+1) :
    ∃ code, verifyValue code=wim (translate native (freeDomain f))
      (translate native (sequentCode (parameters 0 f) s))+1 := by
  obtain ⟨forward,backward,hforward,hbackward⟩ := guardedCode_native_certificates native f s hf hs
  let out := (⟨child,hc⟩ : Certificate (translate native (guardedCode f s))).mp ⟨forward,hforward⟩
  exact ⟨out.code,out.accepted⟩

theorem guardedCode_from_native (native f s child : V)
    (hf : IsSemitermVec language (len f) 0 f) (hs : SupportedSet (parameters 0 f) s)
    (hc : verifyValue child=wim (translate native (freeDomain f))
      (translate native (sequentCode (parameters 0 f) s))+1) :
    ∃ code, verifyValue code=translate native (guardedCode f s)+1 := by
  obtain ⟨forward,backward,hforward,hbackward⟩ := guardedCode_native_certificates native f s hf hs
  let out := (⟨child,hc⟩ : Certificate (wim (translate native (freeDomain f))
    (translate native (sequentCode (parameters 0 f) s)))).mp ⟨backward,hbackward⟩
  exact ⟨out.code,out.accepted⟩

#print axioms guardedCode_graph
#print axioms guardedCode_valid
#print axioms guardedCode_native_certificates
#print axioms guardedCode_to_native
#print axioms guardedCode_from_native
end M6.PA.NumericPAeqFormula.Sequent

