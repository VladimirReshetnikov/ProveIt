import ConditionalComparison
import ModifiedCarrierFacts
import CarrierGamma

/-! Source-only arithmetic client. All imports are unelaborated drafts;
no graph-zero extraction or endpoint follows from this module. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Arithmetic84To85Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing Conditional84To85Draft
open ModifiedCarrierFactsDraft ModifiedCarrierGammaDraft ArithmeticPellRecurrence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The 84→85 map under explicit natural Pell coordinates and carrier
balance. These assumptions are not extracted from the graph zero here. -/
theorem from84_with_carrier (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (U H d X Y a c k R W : V)
    (hport : (p 0 : DiffRing V)=ι beta) (hv : ∀ j, 0<v j)
    (hU : 0<U) (hY : 0<Y) (hq : 1≤q beta v)
    (hX : X=q beta v*v 6) (ha : a=X*Y+Y) (hH : H=4*a+3)
    (hR : 3≤R) (hc : c=ycoord R a) (hd : d=xcoord R a)
    (hk : k=R+1+U*W)
    (hbal : U*d+H*k=U*(X+a*c)+H*(U*v 12+R+1))
    (hz : InternalZero (P84QcubeGraph.graph p).output v) :
    ∃ v' : Fin 14 → V, (∀ j, 0<v' j) ∧ InternalZero (P85QcubeGraph.graph p).output v' := by
  have hgamma : v 6<v 12 :=
    gamma_gt_from_modified_balance U H d X Y a c (v 12) k R W (q beta v) (v 6)
      hU hY hq hX ha hH hR hc hd hk hbal
  exact map_84_to_85 p beta v hport hv hgamma hz

/-- The 85→84 map under explicit Mersenne representation, power and
factor-three divisibility. These are not extracted from the graph zero here. -/
theorem from85_with_mersenne (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (t R : V) (hport : (p 0 : DiffRing V)=ι beta) (hv : ∀ j, 0<v j)
    (ht : 4≤t) (hq : q beta v=(Exp.exp t-1)*v 0+1)
    (hX : v 6=Exp.exp R) (hdiv : q beta v∣3*v 6)
    (hz : InternalZero (P85QcubeGraph.graph p).output v) :
    ∃ v' : Fin 14 → V, (∀ j, 0<v' j) ∧ InternalZero (P84QcubeGraph.graph p).output v' := by
  have hd : q beta v∣v 6 := mersenne_divides_X t R (q beta v) (v 0) (v 6) ht hq hX hdiv
  exact map_85_to_84 p beta v hport hv hd hz

end DiophantineConsistency.Arithmetic84To85Draft

#print axioms DiophantineConsistency.Arithmetic84To85Draft.from84_with_carrier
#print axioms DiophantineConsistency.Arithmetic84To85Draft.from85_with_mersenne
