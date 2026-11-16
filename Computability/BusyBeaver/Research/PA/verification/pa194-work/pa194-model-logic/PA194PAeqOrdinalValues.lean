import PA194OrdinalTemplateRew
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqOrdinalValues
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194SourceTemplates PA194ModelLogic PA194BindSource
open M6.PA.RelationalSource M6.PA.RelationalSource.Ordinal
open M6.PA.RelationalSource.ND (eq)
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def domainTemplate : Formula 1 := domain (.bvar 0)
def zeroTemplate : Formula 1 := zero (.bvar 0)
def successorTemplate : Formula 2 := successor (.bvar 0) (.bvar 1)
def equalityTemplate : Formula 2 := eq (.bvar 0) (.bvar 1)
noncomputable def domainCode (z : V) : V := templateOne domainTemplate z
noncomputable def zeroCode (z : V) : V := templateOne zeroTemplate z
noncomputable def successorCode (x z : V) : V := templateTwo successorTemplate x z
noncomputable def equalityCode (x z : V) : V := templateTwo equalityTemplate x z

theorem domainCode_graph (out z : V) :
    (templateOneGraph domainTemplate).val.Evalb ![out,z] ↔ out = domainCode z := templateOne_graph _ _ _
theorem zeroCode_graph (out z : V) :
    (templateOneGraph zeroTemplate).val.Evalb ![out,z] ↔ out = zeroCode z := templateOne_graph _ _ _
theorem successorCode_graph (out x z : V) :
    (templateTwoGraph successorTemplate).val.Evalb ![out,x,z] ↔ out = successorCode x z := templateTwo_graph _ _ _ _
theorem equalityCode_graph (out x z : V) :
    (templateTwoGraph equalityTemplate).val.Evalb ![out,x,z] ↔ out = equalityCode x z := templateTwo_graph _ _ _ _

theorem domainCode_valid {n z : V} (hz : IsSemiterm SourceL n z) :
    IsSemiformula SourceL n (domainCode z) := templateOne_valid _ hz
theorem zeroCode_valid {n z : V} (hz : IsSemiterm SourceL n z) :
    IsSemiformula SourceL n (zeroCode z) := templateOne_valid _ hz
theorem successorCode_valid {n x z : V} (hx : IsSemiterm SourceL n x) (hz : IsSemiterm SourceL n z) :
    IsSemiformula SourceL n (successorCode x z) := templateTwo_valid _ hx hz
theorem equalityCode_valid {n x z : V} (hx : IsSemiterm SourceL n x) (hz : IsSemiterm SourceL n z) :
    IsSemiformula SourceL n (equalityCode x z) := templateTwo_valid _ hx hz

theorem domainCode_quote {m : Nat} (z : Term m) : domainCode (⌜z⌝ : V) = ⌜domain z⌝ := by
  rw [domainCode, templateOne_quote]
  congr 1
  simpa [domainTemplate, Rewriting.subst, app_eq_rewAux] using domain_rew (Rew.subst ![z]) (.bvar 0)
theorem zeroCode_quote {m : Nat} (z : Term m) : zeroCode (⌜z⌝ : V) = ⌜zero z⌝ := by
  rw [zeroCode, templateOne_quote]
  congr 1
  simpa [zeroTemplate, Rewriting.subst, app_eq_rewAux] using zero_rew (Rew.subst ![z]) (.bvar 0)
theorem successorCode_quote {m : Nat} (x z : Term m) :
    successorCode (⌜x⌝ : V) ⌜z⌝ = ⌜successor x z⌝ := by
  rw [successorCode, templateTwo_quote]
  congr 1
  simpa [successorTemplate, Rewriting.subst, app_eq_rewAux] using successor_rew (Rew.subst ![x,z]) (.bvar 0) (.bvar 1)
theorem equalityCode_quote {m : Nat} (x z : Term m) :
    equalityCode (⌜x⌝ : V) ⌜z⌝ = ⌜eq x z⌝ := by
  rw [equalityCode, templateTwo_quote]
  congr 1
  simp [equalityTemplate, eq, Rewriting.subst, app_eq_rewAux, Semiformula.rewAux]

noncomputable def variableValue (z x : V) : V := domainCode z ^⋏ equalityCode z x
noncomputable def zeroValue (z : V) : V := domainCode z ^⋏ zeroCode z

noncomputable def variableValueGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out z x. ∃ d e, !(templateOneGraph domainTemplate) d z ∧
    !(templateTwoGraph equalityTemplate) e z x ∧ !qqAndDef out d e”
noncomputable def zeroValueGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out z. ∃ d e, !(templateOneGraph domainTemplate) d z ∧
    !(templateOneGraph zeroTemplate) e z ∧ !qqAndDef out d e”

theorem variableValue_graph (out z x : V) :
    variableValueGraph.val.Evalb ![out,z,x] ↔ out = variableValue z x := by
  simp [variableValueGraph,variableValue,domainCode,equalityCode]
theorem zeroValue_graph (out z : V) :
    zeroValueGraph.val.Evalb ![out,z] ↔ out = zeroValue z := by
  simp [zeroValueGraph,zeroValue,domainCode,zeroCode]

instance variableValue_defined : 𝚺₁-Function₂ (variableValue : V → V → V) via variableValueGraph := .mk fun v => by
  change variableValueGraph.val.Evalb v ↔ v 0 = variableValue (v 1) (v 2)
  have hv : ![v 0,v 1,v 2] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
        rfl
  simpa only [hv] using variableValue_graph (v 0) (v 1) (v 2)
instance zeroValue_defined : 𝚺₁-Function₁ (zeroValue : V → V) via zeroValueGraph := .mk fun v => by
  change zeroValueGraph.val.Evalb v ↔ v 0 = zeroValue (v 1)
  have hv : ![v 0,v 1] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact Fin.cases rfl (fun k => Fin.elim0 k) j
  simpa only [hv] using zeroValue_graph (v 0) (v 1)

theorem variableValue_valid {n z x : V} (hz : IsSemiterm SourceL n z) (hx : IsSemiterm SourceL n x) :
    IsSemiformula SourceL n (variableValue z x) :=
  IsSemiformula.and.mpr ⟨domainCode_valid hz,equalityCode_valid hz hx⟩
theorem zeroValue_valid {n z : V} (hz : IsSemiterm SourceL n z) :
    IsSemiformula SourceL n (zeroValue z) := IsSemiformula.and.mpr ⟨domainCode_valid hz,zeroCode_valid hz⟩
theorem variableValue_quote {m : Nat} (z x : Term m) :
    variableValue (⌜z⌝ : V) ⌜x⌝ = ⌜domain z ⋏ eq z x⌝ := by
  simp [variableValue,domainCode_quote,equalityCode_quote]
theorem zeroValue_quote {m : Nat} (z : Term m) :
    zeroValue (⌜z⌝ : V) = ⌜domain z ⋏ zero z⌝ := by
  simp [zeroValue,domainCode_quote,zeroCode_quote]
/-- One interpreted successor value, supplied the translated child under a binder. -/
noncomputable def successorValue (z child : V) : V :=
  domainCode z ^⋏ (^∃ (child ^⋏ successorCode (^#(0 : V)) (termBShift SourceL z)))
noncomputable def successorValueGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out z child. ∃ d zs b s inner ex,
    !(templateOneGraph domainTemplate) d z ∧ !(termBShiftGraph SourceL) zs z ∧
    !qqBvarDef b 0 ∧ !(templateTwoGraph successorTemplate) s b zs ∧
    !qqAndDef inner child s ∧ !qqExsDef ex inner ∧ !qqAndDef out d ex”
theorem successorValue_graph (out z child : V) :
    successorValueGraph.val.Evalb ![out,z,child] ↔ out = successorValue z child := by
  simp [successorValueGraph,successorValue,domainCode,successorCode]

instance successorValue_defined : 𝚺₁-Function₂ (successorValue : V → V → V) via successorValueGraph := .mk fun v => by
  change successorValueGraph.val.Evalb v ↔ v 0 = successorValue (v 1) (v 2)
  have hv : ![v 0,v 1,v 2] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
        rfl
  simpa only [hv] using successorValue_graph (v 0) (v 1) (v 2)

theorem successorValue_valid {n z child : V} (hz : IsSemiterm SourceL n z)
    (hc : IsSemiformula SourceL (n+1) child) :
    IsSemiformula SourceL n (successorValue z child) := by
  apply IsSemiformula.and.mpr
  refine ⟨domainCode_valid hz, IsSemiformula.exs.mpr (IsSemiformula.and.mpr ⟨hc, ?_⟩)⟩
  exact successorCode_valid (by simp) (by simpa using hz.bShift)

theorem successorValue_quote {m : Nat} (z : Term m) (child : Formula (m+1)) :
    successorValue (⌜z⌝ : V) ⌜child⌝ =
      ⌜domain z ⋏ (∃⁰ (child ⋏ successor (.bvar 0) (Rew.bShift z)))⌝ := by
  rw [successorValue,domainCode_quote]
  have hb : (^#(0 : V)) = (⌜(.bvar 0 : Term (m+1))⌝ : V) := by simp
  have hs : termBShift SourceL (⌜z⌝ : V) = ⌜Rew.bShift z⌝ := by
    simp [Semiterm.quote_def]
  rw [hb,hs,successorCode_quote]
  rfl
#print axioms successorValue_graph
#print axioms successorValue_valid
#print axioms successorValue_quote
#print axioms variableValue_graph
#print axioms zeroValue_graph
#print axioms domainCode_quote
#print axioms successorCode_quote
#print axioms variableValue_quote
#print axioms zeroValue_quote
end generic
end PA194PAeqOrdinalValues
