module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermLanguage
public import M6PA.Calibration.PAForwardRelationalSyntax
public import Mathlib.Tactic.FinCases
@[expose] public section

/-! Fixed relational predicate templates instantiated by actual model-valued
term codes. All substitution is Foundation's capture-aware coded substitution.
These are total Sigma-one functions, not semantic witnesses of ordinal values. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open RelationalSource.Ordinal (Term Formula)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem value_quote_formula {n m : Nat} {ξ : Type*}
    (bv : Fin m → V) (fv : ξ → V) (p : Formula n) :
    (⌜p⌝ : ArithmeticSemiterm ξ m).val bv fv = (⌜p⌝ : V) := by
  simp [gödelNumber'_def, FFL.FirstOrder.Semiformula.quote_eq_encode, numeral_eq_natCast]

noncomputable def templateOne (p : Formula 1) (z : V) : V :=
  substs1 language z ⌜p⌝
noncomputable def templateOneGraph (p : Formula 1) : 𝚺ᴬ₁.Semisentence 2 :=
  .mkSigma “out z. !(substs1Graph language) out z ↑(⌜p⌝ : Nat)”

theorem templateOne_graph (p : Formula 1) (out z : V) :
    (templateOneGraph p).val.Evalb ![out,z] ↔ out=templateOne p z := by
  simp [templateOneGraph,templateOne,FFL.FirstOrder.Semiformula.coe_quote_eq_quote]

instance templateOne_defined (p : Formula 1) :
    𝚺ᴬ₁-Function₁ (templateOne p : V → V) via templateOneGraph p :=
  .mk fun v => by
    have hv : ![v 0,v 1]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! templateOne_graph p (v 0) (v 1)

theorem templateOne_total_unique (p : Formula 1) (z : V) :
    ∃! out, (templateOneGraph p).val.Evalb ![out,z] := by
  refine ⟨templateOne p z,(templateOne_graph _ _ _).mpr rfl,?_⟩
  intro out h; exact (templateOne_graph _ _ _).mp h

theorem templateOne_quote {m : Nat} (p : Formula 1) (z : Term m) :
    templateOne p (⌜z⌝ : V)=⌜p ⇜ ![z]⌝ := by
  simp only [templateOne, substs1, FFL.FirstOrder.Semiformula.quote_def,
    FFL.FirstOrder.Semiformula.typed_quote_substs]
  rfl

noncomputable def templateTwo (p : Formula 2) (x z : V) : V :=
  subst language (x ∷ (z ∷ 0)) ⌜p⌝
noncomputable def templateTwoGraph (p : Formula 2) : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “out x z. ∃ zs xs, !adjoinDef zs z 0 ∧ !adjoinDef xs x zs ∧
    !(substsGraph language) out xs ↑(⌜p⌝ : Nat)”

theorem templateTwo_graph (p : Formula 2) (out x z : V) :
    (templateTwoGraph p).val.Evalb ![out,x,z] ↔ out=templateTwo p x z := by
  simp [templateTwoGraph,templateTwo,FFL.FirstOrder.Semiformula.coe_quote_eq_quote]

instance templateTwo_defined (p : Formula 2) :
    𝚺ᴬ₁-Function₂ (templateTwo p : V → V → V) via templateTwoGraph p :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! templateTwo_graph p (v 0) (v 1) (v 2)

theorem templateTwo_total_unique (p : Formula 2) (x z : V) :
    ∃! out, (templateTwoGraph p).val.Evalb ![out,x,z] := by
  refine ⟨templateTwo p x z,(templateTwo_graph _ _ _ _).mpr rfl,?_⟩
  intro out h; exact (templateTwo_graph _ _ _ _).mp h

theorem templateTwo_quote {m : Nat} (p : Formula 2) (x z : Term m) :
    templateTwo p (⌜x⌝ : V) ⌜z⌝=⌜p ⇜ ![x,z]⌝ := by
  simp only [templateTwo, FFL.FirstOrder.Semiformula.quote_def,
    FFL.FirstOrder.Semiformula.typed_quote_substs]
  rfl

def domainTemplate : Formula 1 := RelationalSource.Ordinal.domain (.bvar 0)
def zeroTemplate : Formula 1 := RelationalSource.Ordinal.zero (.bvar 0)
def successorTemplate : Formula 2 := RelationalSource.Ordinal.successor (.bvar 0) (.bvar 1)

noncomputable def domainCode (z : V) : V := templateOne domainTemplate z
noncomputable def zeroCode (z : V) : V := templateOne zeroTemplate z
noncomputable def successorCode (x z : V) : V := templateTwo successorTemplate x z

noncomputable abbrev domainCodeGraph : 𝚺ᴬ₁.Semisentence 2 := templateOneGraph domainTemplate
noncomputable abbrev zeroCodeGraph : 𝚺ᴬ₁.Semisentence 2 := templateOneGraph zeroTemplate
noncomputable abbrev successorCodeGraph : 𝚺ᴬ₁.Semisentence 3 := templateTwoGraph successorTemplate

theorem domainCode_graph (out z : V) : domainCodeGraph.val.Evalb ![out,z] ↔ out=domainCode z :=
  templateOne_graph _ _ _
theorem zeroCode_graph (out z : V) : zeroCodeGraph.val.Evalb ![out,z] ↔ out=zeroCode z :=
  templateOne_graph _ _ _
theorem successorCode_graph (out x z : V) :
    successorCodeGraph.val.Evalb ![out,x,z] ↔ out=successorCode x z := templateTwo_graph _ _ _ _

theorem templateOne_isSemiformula (p : Formula 1) {n z : V} (hz : IsSemiterm language n z) :
    IsSemiformula language n (templateOne p z) :=
  IsSemiformula.substs1 hz (by simpa using FFL.FirstOrder.Semiformula.quote_isSemiformula (V := V) p)

theorem templateTwo_isSemiformula (p : Formula 2) {n x z : V}
    (hx : IsSemiterm language n x) (hz : IsSemiterm language n z) :
    IsSemiformula language n (templateTwo p x z) := by
  apply IsSemiformula.subst (show IsSemiformula language 2 (⌜p⌝ : V) by simpa using FFL.FirstOrder.Semiformula.quote_isSemiformula (V := V) p)
  simp [hx,hz]

theorem domainCode_isSemiformula {n z : V} (hz : IsSemiterm language n z) :
    IsSemiformula language n (domainCode z) := templateOne_isSemiformula _ hz
theorem zeroCode_isSemiformula {n z : V} (hz : IsSemiterm language n z) :
    IsSemiformula language n (zeroCode z) := templateOne_isSemiformula _ hz
theorem successorCode_isSemiformula {n x z : V}
    (hx : IsSemiterm language n x) (hz : IsSemiterm language n z) :
    IsSemiformula language n (successorCode x z) := templateTwo_isSemiformula _ hx hz

theorem domainCode_quote {m : Nat} (z : Term m) :
    domainCode (⌜z⌝ : V)=⌜RelationalSource.Ordinal.domain z⌝ := by
  rw [domainCode,templateOne_quote]
  congr 1
  exact RelationalSource.Ordinal.domain_rew _ _

theorem zeroCode_quote {m : Nat} (z : Term m) :
    zeroCode (⌜z⌝ : V)=⌜RelationalSource.Ordinal.zero z⌝ := by
  rw [zeroCode,templateOne_quote]
  congr 1
  exact RelationalSource.Ordinal.zero_rew _ _

theorem successorCode_quote {m : Nat} (x z : Term m) :
    successorCode (⌜x⌝ : V) ⌜z⌝=⌜RelationalSource.Ordinal.successor x z⌝ := by
  rw [successorCode,templateTwo_quote]
  congr 1
  exact RelationalSource.Ordinal.successor_rew _ _ _

#print axioms domainCode_isSemiformula
#print axioms zeroCode_isSemiformula
#print axioms successorCode_isSemiformula
#print axioms value_quote_formula
#print axioms domainCode_graph
#print axioms zeroCode_graph
#print axioms successorCode_graph
#print axioms templateOne_isSemiformula
#print axioms templateTwo_isSemiformula
#print axioms templateOne_graph
#print axioms templateOne_defined
#print axioms templateOne_total_unique
#print axioms templateOne_quote
#print axioms templateTwo_graph
#print axioms templateTwo_defined
#print axioms templateTwo_total_unique
#print axioms templateTwo_quote
#print axioms domainCode_quote
#print axioms zeroCode_quote
#print axioms successorCode_quote
end M6.PA.NumericPAeqTerm

