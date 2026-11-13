module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermTemplates
@[expose] public section

/-! Actual relational formula-code constructors for arithmetic term values.
The successor child is supplied under one additional bound variable; it is not
an assumed witness or an already completed recursive translation. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open RelationalSource.Ordinal (Term Formula)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def equalityTemplate : Formula 2 := RelationalSource.ND.eq (.bvar 0) (.bvar 1)
noncomputable def equalityCode (x z : V) : V := templateTwo equalityTemplate x z
noncomputable abbrev equalityCodeGraph : 𝚺ᴬ₁.Semisentence 3 := templateTwoGraph equalityTemplate

theorem equalityCode_graph (out x z : V) :
    equalityCodeGraph.val.Evalb ![out,x,z] ↔ out=equalityCode x z := templateTwo_graph _ _ _ _

theorem equalityCode_quote {m : Nat} (x z : Term m) :
    equalityCode (⌜x⌝ : V) ⌜z⌝=⌜RelationalSource.ND.eq x z⌝ := by
  rw [equalityCode,templateTwo_quote]
  rfl

noncomputable def variableValue (z x : V) : V := qqAnd (domainCode z) (equalityCode z x)
noncomputable def zeroValue (z : V) : V := qqAnd (domainCode z) (zeroCode z)
noncomputable def successorValue (z child : V) : V :=
  qqAnd (domainCode z) (qqExs (qqAnd child (successorCode (qqBvar 0) (termBShift language z))))

attribute [local irreducible] templateOneGraph templateTwoGraph
noncomputable def variableValueGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out z x. ∃ d e, !domainCodeGraph d z ∧ !equalityCodeGraph e z x ∧ !qqAndDef out d e”
noncomputable def zeroValueGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “out z. ∃ d e, !domainCodeGraph d z ∧ !zeroCodeGraph e z ∧ !qqAndDef out d e”
noncomputable def successorValueGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out z child. ∃ d zs b s inner ex,
    !domainCodeGraph d z ∧ !(termBShiftGraph language) zs z ∧ !qqBvarDef b 0 ∧
    !successorCodeGraph s b zs ∧ !qqAndDef inner child s ∧ !qqExsDef ex inner ∧ !qqAndDef out d ex”

theorem variableValue_graph (out z x : V) :
    variableValueGraph.val.Evalb ![out,z,x] ↔ out=variableValue z x := by
  simp [variableValueGraph,variableValue,domainCode_graph,equalityCode_graph,Matrix.comp_vecCons'']; rfl
theorem zeroValue_graph (out z : V) :
    zeroValueGraph.val.Evalb ![out,z] ↔ out=zeroValue z := by
  simp [zeroValueGraph,zeroValue,domainCode_graph,zeroCode_graph,Matrix.comp_vecCons'']; rfl
theorem successorValue_graph (out z child : V) :
    successorValueGraph.val.Evalb ![out,z,child] ↔ out=successorValue z child := by
  simp [successorValueGraph,successorValue,domainCode_graph,successorCode_graph,Matrix.comp_vecCons'']; rfl

instance variableValue_defined : 𝚺ᴬ₁-Function₂ (variableValue : V → V → V) via variableValueGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! variableValue_graph (v 0) (v 1) (v 2)
instance zeroValue_defined : 𝚺ᴬ₁-Function₁ (zeroValue : V → V) via zeroValueGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! zeroValue_graph (v 0) (v 1)
instance successorValue_defined : 𝚺ᴬ₁-Function₂ (successorValue : V → V → V) via successorValueGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! successorValue_graph (v 0) (v 1) (v 2)

theorem variableValue_quote {m : Nat} (z x : Term m) :
    variableValue (⌜z⌝ : V) ⌜x⌝=⌜RelationalSource.Ordinal.domain z ⋏ RelationalSource.ND.eq z x⌝ := by
  simp [variableValue,domainCode_quote,equalityCode_quote]
theorem zeroValue_quote {m : Nat} (z : Term m) :
    zeroValue (⌜z⌝ : V)=⌜RelationalSource.Ordinal.domain z ⋏ RelationalSource.Ordinal.zero z⌝ := by
  simp [zeroValue,domainCode_quote,zeroCode_quote]
theorem successorValue_quote {m : Nat} (z : Term m) (child : Formula (m+1)) :
    successorValue (⌜z⌝ : V) ⌜child⌝=⌜RelationalSource.Ordinal.domain z ⋏
      (∃¹ (child ⋏ RelationalSource.Ordinal.successor (.bvar 0) (Rew.bShift z)))⌝ := by
  rw [successorValue, domainCode_quote]
  have hb : (qqBvar (0 : V)) = (⌜(.bvar 0 : Term (m+1))⌝ : V) := by simp
  have hs : termBShift language (⌜z⌝ : V) = ⌜Rew.bShift z⌝ := by
    simp [FFL.FirstOrder.Semiterm.quote_def]
  rw [hb, hs, successorCode_quote]
  rfl

theorem variableValue_isSemiformula {n z x : V}
    (hz : IsSemiterm language n z) (hx : IsSemiterm language n x) :
    IsSemiformula language n (variableValue z x) := by
  exact IsSemiformula.and.mpr ⟨domainCode_isSemiformula hz, templateTwo_isSemiformula equalityTemplate hz hx⟩
theorem zeroValue_isSemiformula {n z : V} (hz : IsSemiterm language n z) :
    IsSemiformula language n (zeroValue z) :=
  IsSemiformula.and.mpr ⟨domainCode_isSemiformula hz, zeroCode_isSemiformula hz⟩
theorem successorValue_isSemiformula {n z child : V} (hz : IsSemiterm language n z)
    (hc : IsSemiformula language (n+1) child) :
    IsSemiformula language n (successorValue z child) := by
  apply IsSemiformula.and.mpr
  refine ⟨domainCode_isSemiformula hz, IsSemiformula.exs.mpr (IsSemiformula.and.mpr ⟨hc, ?_⟩)⟩
  exact successorCode_isSemiformula (by simp) (by simpa using hz.bShift)

theorem variableValue_bound_forward {n m : Nat} (i : Fin n)
    (b : Fin n → Term m) (f : Nat → Term m) (z : Term m) :
    variableValue (⌜z⌝ : V) ⌜b i⌝ = ⌜ForwardRelational.value (.bvar i) b f z⌝ :=
  variableValue_quote z (b i)
theorem variableValue_free_forward {n m : Nat} (i : Nat)
    (b : Fin n → Term m) (f : Nat → Term m) (z : Term m) :
    variableValue (⌜z⌝ : V) ⌜f i⌝ = ⌜ForwardRelational.value (.fvar i) b f z⌝ :=
  variableValue_quote z (f i)
theorem zeroValue_forward {n m : Nat} (b : Fin n → Term m) (f : Nat → Term m) (z : Term m) :
    zeroValue (⌜z⌝ : V) = ⌜ForwardRelational.value (Presentation.zero : ForwardRelational.SourceTerm n) b f z⌝ :=
  zeroValue_quote z
theorem successorValue_forward {n m : Nat} (t : ForwardRelational.SourceTerm n)
    (b : Fin n → Term m) (f : Nat → Term m) (z : Term m) :
    successorValue (⌜z⌝ : V) ⌜ForwardRelational.value t
      (ForwardRelational.shiftEnv b) (ForwardRelational.shiftEnv f) (.bvar 0)⌝ =
    ⌜ForwardRelational.value (Presentation.succ t) b f z⌝ := by
  exact successorValue_quote z _

#print axioms variableValue_bound_forward
#print axioms variableValue_free_forward
#print axioms zeroValue_forward
#print axioms successorValue_forward
#print axioms equalityCode_graph
#print axioms equalityCode_quote
#print axioms variableValue_graph
#print axioms zeroValue_graph
#print axioms successorValue_graph
#print axioms variableValue_defined
#print axioms zeroValue_defined
#print axioms successorValue_defined
#print axioms variableValue_quote
#print axioms zeroValue_quote
#print axioms successorValue_quote
#print axioms variableValue_isSemiformula
#print axioms zeroValue_isSemiformula
#print axioms successorValue_isSemiformula
end M6.PA.NumericPAeqTerm

