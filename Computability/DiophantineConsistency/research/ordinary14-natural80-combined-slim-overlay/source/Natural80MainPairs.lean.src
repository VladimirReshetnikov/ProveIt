import Natural80GuardGap
import PairEvalRingBridge
import DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011
import DiophantineConsistency.ArithmeticAdaptiveTransport2011

/-! Source-only literal 74 main-pair bindings for a partially shifted 80
zero. The rewrites and every imported source draft are unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.Natural80MainPairsDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveScaledNorms2011
open ArithmeticAdaptiveTransport2011 PairEvalRingBridgeDraft
open FirstFactor74Draft FactorResidues74Draft Natural80Partial74Draft
open Natural80OwnZeroNormDraft Natural80GuardGapDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def scale (beta : V) (u : Fin 14 → V) : V := Y beta u*(q beta u*q beta u)
def coeffA (beta : V) (u : Fin 14 → V) : V := X beta u*Y beta u+Y beta u
def coeffC (beta : V) (u : Fin 14 → V) : V := u 9+Y beta u*(u 9+u 10)
def coeffH (beta : V) (u : Fin 14 → V) : V := 3+4*coeffA beta u
def rankValue (beta MC MF : V) (u : Fin 14 → V) : V :=
  (u 2+(q beta u-u 1)*(u 0*beta))*(q beta u*q beta u-1)+u 0*(MC+MF*q beta u)
def positivePart (beta MC MF : V) (u : Fin 14 → V) : V :=
  scale beta u*(X beta u+coeffA beta u*coeffC beta u)+
    coeffH beta u*(scale beta u*u 12+rankValue beta MC MF u+1)
def negativePart (beta : V) (u : Fin 14 → V) : V := coeffH beta u*(u 9+u 10)
def rhsValue (beta : V) (u : Fin 14 → V) : V :=
  scale beta u*scale beta u*
    (1+(coeffH beta u+coeffA beta u*coeffA beta u)*(coeffC beta u*coeffC beta u))

/-- The positive main RHS is represented using the beta port alone. -/
theorem rhs_eval (p : Fin 4 → ℤ) (beta : V) (u : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) :
    (mainRhs p).evalRing (fun j => ι (u j)) = ι (rhsValue beta u) := by
  simp [mainRhs, rhsValue, scale, coeffA, coeffC, coeffH,
    P74PositiveGuard.graph, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    q,X,Y,hbeta,map_add,map_mul,map_one] <;> ring

theorem rhs_rep (p : Fin 4 → ℤ) (beta : V) (u : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) :
    Equivalent (pairEval (mainRhs p) u) (natural (rhsValue beta u)) := by
  apply represented_of_ring_eval (mainRhs p) u (rhsValue beta u) 0
  simpa using rhs_eval p beta u hbeta

/-- Exact signed main root; the two truncated natural subtractions are
justified by the explicit guard gap and the automatic `q>=1`. -/
theorem root_eval (p : Fin 4 → ℤ) (beta MC MF : V) (u : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta)
    (hMC : (p 2 : DiffRing V)=ι MC) (hMF : (p 3 : DiffRing V)=ι MF)
    (hgap : u 1+u 2<q beta u) :
    (P74PositiveGuard.graph p).Dstar.evalRing (fun j => ι (u j)) =
      ι (positivePart beta MC MF u)-ι (negativePart beta u) := by
  have hq : 1≤q beta u := by dsimp [q]; simp
  have hF : u 1≤q beta u := le_trans (by simp : u 1≤u 1+u 2) (le_of_lt hgap)
  have hq2 : 1≤q beta u*q beta u := one_le_mul hq hq
  have hFcancel : q beta u-u 1+u 1=q beta u := tsub_add_cancel_of_le hF
  have hqcancel : q beta u*q beta u-1+1=q beta u*q beta u := tsub_add_cancel_of_le hq2
  have hFcast : ι (q beta u-u 1)=ι (q beta u)-ι (u 1) := by
    apply eq_sub_iff_add_eq.mpr
    rw [←map_add,hFcancel]
  have hqcast : ι (q beta u*q beta u-1)=ι (q beta u*q beta u)-1 := by
    apply eq_sub_iff_add_eq.mpr
    rw [←map_one ι,←map_add,hqcancel]
  simp [positivePart,negativePart,rankValue,scale,coeffA,coeffC,coeffH,
    P74PositiveGuard.graph, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    hbeta,hMC,hMF,map_add,map_mul,map_one,hFcast,hqcast,q,X,Y] <;> ring

theorem root_rep (p : Fin 4 → ℤ) (beta MC MF : V) (u : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta)
    (hMC : (p 2 : DiffRing V)=ι MC) (hMF : (p 3 : DiffRing V)=ι MF)
    (hgap : u 1+u 2<q beta u) :
    Equivalent (pairEval (P74PositiveGuard.graph p).Dstar u)
      (positivePart beta MC MF u,negativePart beta u) := by
  exact represented_of_ring_eval _ u _ _ (root_eval p beta MC MF u hbeta hMC hMF hgap)

/-- A factor unit and represented root/right side yield the main magnitude
norm. Pair equivalence, rather than literal pair equality, is sufficient. -/
theorem norm_from_representations (p : Fin 4 → ℤ) (u : Fin 14 → V) (P N rhs : V)
    (hunit : (pairEval (P74PositiveGuard.graph p).main u).1=
      (pairEval (P74PositiveGuard.graph p).main u).2+1)
    (hroot : Equivalent (pairEval (P74PositiveGuard.graph p).Dstar u) (P,N))
    (hrhs : Equivalent (pairEval (mainRhs p) u) (natural rhs)) :
    magnitude (P,N)*magnitude (P,N)=rhs := by
  have hu := hunit
  rw [FactorResidues74Draft.main_shape] at hu
  change (pairEval (1+((P74PositiveGuard.graph p).Dstar*(P74PositiveGuard.graph p).Dstar-mainRhs p)) u).1 =
    (pairEval (1+((P74PositiveGuard.graph p).Dstar*(P74PositiveGuard.graph p).Dstar-mainRhs p)) u).2+1 at hu
  have hn := unit_square_norm (P74PositiveGuard.graph p).Dstar (mainRhs p) u hu
  have hmag := magnitude_equivalent hroot
  rw [hmag] at hn
  have he : (pairEval (mainRhs p) u).1=(pairEval (mainRhs p) u).2+rhs := by
    simpa [Equivalent,natural] using hrhs
  nlinarith

/-- Proposed literal main norm at a natural 80 zero, with all four port
representations explicit. MC and MF inequalities are not needed here. -/
theorem norm_of_80_zero (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)
    (hMC : (p 2 : DiffRing V)=ι MC) (hMF : (p 3 : DiffRing V)=ι MF)
    (hb : 0<beta) (hKpos : 0<K)
    (hz : InternalZero (P80NaturalForcedGamma.graph p).output v) :
    let u := partial74 v
    magnitude (positivePart beta MC MF u,negativePart beta u)*
      magnitude (positivePart beta MC MF u,negativePart beta u)=rhsValue beta u := by
  let u := partial74 v
  have hunits := units_of_80_zero p beta K v hbeta hK hb hKpos hz
  have hgap := gap_of_80_zero p beta K v hbeta hK hb hKpos hz
  exact norm_from_representations p u _ _ _ hunits.2.1
    (root_rep p beta MC MF u hbeta hMC hMF hgap) (rhs_rep p beta u hbeta)

end DiophantineConsistency.Natural80MainPairsDraft

#print axioms DiophantineConsistency.Natural80MainPairsDraft.rhs_rep
#print axioms DiophantineConsistency.Natural80MainPairsDraft.root_rep
#print axioms DiophantineConsistency.Natural80MainPairsDraft.norm_of_80_zero
