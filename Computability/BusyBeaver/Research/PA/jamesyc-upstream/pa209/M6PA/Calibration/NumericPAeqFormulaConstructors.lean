module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermTemplates
@[expose] public section

/-! Actual coded relational equality and guarded quantifier constructors for
arithmetic interpretation. Inputs are relational formula codes, not native
Hilbert formula numbers. Child-environment realization is a separate contract. -/
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open RelationalSource.Ordinal (Term Formula)
open NumericPAeqTerm

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def equalityTail : Formula 2 := RelationalSource.PairGraph.orderIso (.bvar 1) (.bvar 0)

noncomputable def equalityCode (a b : V) : V :=
  qqExs (qqExs (qqAnd a (qqAnd b ⌜equalityTail⌝)))
noncomputable def guardedAllCode (p : V) : V :=
  qqAll (imp language ⌜domainTemplate⌝ p)
noncomputable def guardedExsCode (p : V) : V :=
  qqExs (qqAnd ⌜domainTemplate⌝ p)

noncomputable def equalityGraph : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “out a b. ∃ tail body inner, !qqAndDef tail b ↑(Encodable.encode equalityTail) ∧
    !qqAndDef body a tail ∧ !qqExsDef inner body ∧ !qqExsDef out inner”
private noncomputable def guardedAllGraphFor (d : Nat) : 𝚺ᴬ₁.Semisentence 2 :=
  .mkSigma “out p. ∃ body, !(impGraph language) body ↑d p ∧ !qqAllDef out body”

private noncomputable def guardedExsGraphFor (d : Nat) : 𝚺ᴬ₁.Semisentence 2 :=
  .mkSigma “out p. ∃ body, !qqAndDef body ↑d p ∧ !qqExsDef out body”

noncomputable def guardedAllGraph : 𝚺ᴬ₁.Semisentence 2 :=
  .mkSigma “out p. ∃ body, !(impGraph language) body ↑(Encodable.encode domainTemplate) p ∧
    !qqAllDef out body”

noncomputable def guardedExsGraph : 𝚺ᴬ₁.Semisentence 2 :=
  .mkSigma “out p. ∃ body, !qqAndDef body ↑(Encodable.encode domainTemplate) p ∧
    !qqExsDef out body”

private theorem guardedAll_graph_for (d : Nat) (out p : V) :
    (guardedAllGraphFor d).val.Evalb ![out,p] ↔
      out=qqAll (imp language (↑d : V) p) := by
  simp [guardedAllGraphFor,numeral_eq_natCast]

private theorem guardedExs_graph_for (d : Nat) (out p : V) :
    (guardedExsGraphFor d).val.Evalb ![out,p] ↔
      out=qqExs (qqAnd (↑d : V) p) := by
  simp [guardedExsGraphFor,numeral_eq_natCast]

theorem equality_graph (out a b : V) :
    equalityGraph.val.Evalb ![out,a,b] ↔ out=equalityCode a b := by
  simp [equalityGraph,equalityCode,FFL.FirstOrder.Semiformula.quote_eq_encode,numeral_eq_natCast]
theorem guardedAll_graph (out p : V) :
    guardedAllGraph.val.Evalb ![out,p] ↔ out=guardedAllCode p := by
  refine (guardedAll_graph_for (Encodable.encode domainTemplate) out p).trans ?_
  simp only [guardedAllCode, FFL.FirstOrder.Semiformula.quote_eq_encode]
theorem guardedExs_graph (out p : V) :
    guardedExsGraph.val.Evalb ![out,p] ↔ out=guardedExsCode p := by
  refine (guardedExs_graph_for (Encodable.encode domainTemplate) out p).trans ?_
  simp only [guardedExsCode, FFL.FirstOrder.Semiformula.quote_eq_encode]

instance equality_defined : 𝚺ᴬ₁-Function₂ (equalityCode : V → V → V) via equalityGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! equality_graph (v 0) (v 1) (v 2)
instance guardedAll_defined : 𝚺ᴬ₁-Function₁ (guardedAllCode : V → V) via guardedAllGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! guardedAll_graph (v 0) (v 1)
instance guardedExs_defined : 𝚺ᴬ₁-Function₁ (guardedExsCode : V → V) via guardedExsGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! guardedExs_graph (v 0) (v 1)

theorem equality_total_unique (a b : V) : ∃! out,equalityGraph.val.Evalb ![out,a,b] :=
  ⟨equalityCode a b,(equality_graph _ _ _).mpr rfl,fun _ h => (equality_graph _ _ _).mp h⟩
theorem guardedAll_total_unique (p : V) : ∃! out,guardedAllGraph.val.Evalb ![out,p] :=
  ⟨guardedAllCode p,(guardedAll_graph _ _).mpr rfl,fun _ h => (guardedAll_graph _ _).mp h⟩
theorem guardedExs_total_unique (p : V) : ∃! out,guardedExsGraph.val.Evalb ![out,p] :=
  ⟨guardedExsCode p,(guardedExs_graph _ _).mpr rfl,fun _ h => (guardedExs_graph _ _).mp h⟩

#print axioms equality_defined
#print axioms guardedAll_defined
#print axioms guardedExs_defined
#print axioms equality_total_unique
#print axioms guardedAll_total_unique
#print axioms guardedExs_total_unique
end M6.PA.NumericPAeqFormula

