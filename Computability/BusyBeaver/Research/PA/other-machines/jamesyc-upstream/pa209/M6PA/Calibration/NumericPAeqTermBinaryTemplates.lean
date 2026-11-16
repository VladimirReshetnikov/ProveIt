module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermParameters
@[expose] public section

/-! Ternary fixed templates for the exact frozen addition/multiplication result
predicates. No new arithmetic relation or value selection is introduced. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open RelationalSource.Ordinal (Term Formula)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def templateThree (p : Formula 3) (x y z : V) : V :=
  subst language (x ∷ (y ∷ (z ∷ 0))) ⌜p⌝
noncomputable def templateThreeGraph (p : Formula 3) : 𝚺ᴬ₁.Semisentence 4 :=
  .mkSigma “out x y z. ∃ zs ys xs, !adjoinDef zs z 0 ∧ !adjoinDef ys y zs ∧
    !adjoinDef xs x ys ∧ !(substsGraph language) out xs ↑(⌜p⌝ : Nat)”
theorem templateThree_graph (p : Formula 3) (out x y z : V) :
    (templateThreeGraph p).val.Evalb ![out,x,y,z] ↔ out=templateThree p x y z := by
  simp [templateThreeGraph,templateThree]
instance templateThree_defined (p : Formula 3) :
    𝚺ᴬ₁-Function₃ (templateThree p : V → V → V → V) via templateThreeGraph p :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2,v 3]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! templateThree_graph p (v 0) (v 1) (v 2) (v 3)
theorem templateThree_total_unique (p : Formula 3) (x y z : V) :
    ∃! out, (templateThreeGraph p).val.Evalb ![out,x,y,z] := by
  refine ⟨templateThree p x y z,(templateThree_graph _ _ _ _ _).mpr rfl,?_⟩
  intro out h; exact (templateThree_graph _ _ _ _ _).mp h
theorem templateThree_quote {m : Nat} (p : Formula 3) (x y z : Term m) :
    templateThree p (⌜x⌝ : V) ⌜y⌝ ⌜z⌝=⌜p ⇜ ![x,y,z]⌝ := by
  simp only [templateThree, FFL.FirstOrder.Semiformula.quote_def,
    FFL.FirstOrder.Semiformula.typed_quote_substs]
  rfl
theorem templateThree_isSemiformula (p : Formula 3) {n x y z : V}
    (hx : IsSemiterm language n x) (hy : IsSemiterm language n y) (hz : IsSemiterm language n z) :
    IsSemiformula language n (templateThree p x y z) := by
  apply IsSemiformula.subst (show IsSemiformula language 3 (⌜p⌝ : V) by simpa using FFL.FirstOrder.Semiformula.quote_isSemiformula (V := V) p)
  simp [hx,hy,hz,show (3:V)=2+1 from two_add_one_eq_three.symm]

def additionTemplate : Formula 3 := RelationalSource.PairGraph.addResult (.bvar 0) (.bvar 1) (.bvar 2)
def multiplicationTemplate : Formula 3 := RelationalSource.PairGraph.mulResult (.bvar 0) (.bvar 1) (.bvar 2)
noncomputable def additionCode (x y z : V) : V := templateThree additionTemplate x y z
noncomputable def multiplicationCode (x y z : V) : V := templateThree multiplicationTemplate x y z
noncomputable abbrev additionCodeGraph : 𝚺ᴬ₁.Semisentence 4 := templateThreeGraph additionTemplate
noncomputable abbrev multiplicationCodeGraph : 𝚺ᴬ₁.Semisentence 4 := templateThreeGraph multiplicationTemplate

theorem additionCode_graph (out x y z : V) :
    additionCodeGraph.val.Evalb ![out,x,y,z] ↔ out=additionCode x y z := templateThree_graph _ _ _ _ _
theorem multiplicationCode_graph (out x y z : V) :
    multiplicationCodeGraph.val.Evalb ![out,x,y,z] ↔ out=multiplicationCode x y z := templateThree_graph _ _ _ _ _
theorem additionCode_quote {m : Nat} (x y z : Term m) :
    additionCode (⌜x⌝ : V) ⌜y⌝ ⌜z⌝=⌜RelationalSource.PairGraph.addResult x y z⌝ := by
  rw [additionCode,templateThree_quote]
  congr 1
  exact RelationalSource.PairGraph.addResult_rew _ _ _ _
theorem multiplicationCode_quote {m : Nat} (x y z : Term m) :
    multiplicationCode (⌜x⌝ : V) ⌜y⌝ ⌜z⌝=⌜RelationalSource.PairGraph.mulResult x y z⌝ := by
  rw [multiplicationCode,templateThree_quote]
  congr 1
  exact RelationalSource.PairGraph.mulResult_rew _ _ _ _
theorem additionCode_isSemiformula {n x y z : V}
    (hx : IsSemiterm language n x) (hy : IsSemiterm language n y) (hz : IsSemiterm language n z) :
    IsSemiformula language n (additionCode x y z) := templateThree_isSemiformula _ hx hy hz
theorem multiplicationCode_isSemiformula {n x y z : V}
    (hx : IsSemiterm language n x) (hy : IsSemiterm language n y) (hz : IsSemiterm language n z) :
    IsSemiformula language n (multiplicationCode x y z) := templateThree_isSemiformula _ hx hy hz

#print axioms templateThree_graph
#print axioms templateThree_defined
#print axioms templateThree_total_unique
#print axioms templateThree_quote
#print axioms templateThree_isSemiformula
#print axioms additionCode_graph
#print axioms multiplicationCode_graph
#print axioms additionCode_quote
#print axioms multiplicationCode_quote
#print axioms additionCode_isSemiformula
#print axioms multiplicationCode_isSemiformula
end M6.PA.NumericPAeqTerm

