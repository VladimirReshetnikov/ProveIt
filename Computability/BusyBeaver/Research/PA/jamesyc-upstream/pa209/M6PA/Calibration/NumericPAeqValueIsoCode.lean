module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermTemplates
public import M6PA.Calibration.PAForwardRelationalRewriting
@[expose] public section
namespace M6.PA.NumericPAeqValueIsoGuard
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm
open RelationalSource.Ordinal (Term Formula)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def isoTemplate : Formula 2 := RelationalSource.PairGraph.orderIso (.bvar 0) (.bvar 1)
noncomputable def isoCode (x y:V) : V := templateTwo isoTemplate x y
noncomputable abbrev isoCodeGraph : 𝚺ᴬ₁.Semisentence 3 := templateTwoGraph isoTemplate
theorem isoCode_graph (out x y:V) : isoCodeGraph.val.Evalb ![out,x,y] ↔ out=isoCode x y :=
  templateTwo_graph _ _ _ _
theorem isoCode_isSemiformula {n x y:V}
    (hx:IsSemiterm RelationalSource.language n x) (hy:IsSemiterm RelationalSource.language n y) :
    IsSemiformula RelationalSource.language n (isoCode x y) := templateTwo_isSemiformula isoTemplate hx hy
theorem isoCode_quote {n:Nat} (x y:Term n) :
    isoCode (⌜x⌝:V) ⌜y⌝=(⌜RelationalSource.PairGraph.orderIso x y⌝:V) := by
  rw [isoCode,templateTwo_quote]
  congr 1
  simp [isoTemplate,RelationalSource.PairGraph.orderIso_rew]
#print axioms isoCode_graph
#print axioms isoCode_isSemiformula
#print axioms isoCode_quote
end M6.PA.NumericPAeqValueIsoGuard

