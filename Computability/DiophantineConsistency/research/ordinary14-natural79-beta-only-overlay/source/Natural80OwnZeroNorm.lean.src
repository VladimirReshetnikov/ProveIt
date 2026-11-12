import Natural80Partial74
import Natural80JPos
import OwnZeroUnits74
import DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011
import DiophantineConsistency.ArithmeticAdaptiveTransport2011

/-! Source-only 80 own-zero factor extraction and conditional main norm.
All graph, model and proof dependencies remain unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.Natural80OwnZeroNormDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveScaledNorms2011
open ArithmeticAdaptiveTransport2011
open FirstFactor74Draft OwnZeroProduct74Draft FactorResidues74Draft
open Natural80Partial74Draft Natural80JPosDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed own-zero extraction: beta and strict K0 representations and
positivity are explicit; f, r, y and gamma need not be positive. -/
theorem units_of_80_zero (p : Fin 4 → ℤ) (beta K : V) (v : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)
    (hb : 0<beta) (hKpos : 0<K)
    (hz : InternalZero (P80NaturalForcedGamma.graph p).output v) :
    let u := partial74 v
    u 8*u 8=(m beta u*k u)*(m beta u*k u+k u)+1 ∧
    (pairEval (P74PositiveGuard.graph p).main u).1=
      (pairEval (P74PositiveGuard.graph p).main u).2+1 ∧
    (pairEval (P74PositiveGuard.graph p).aux u).1=
      (pairEval (P74PositiveGuard.graph p).aux u).2+1 ∧
    (pairEval (P74PositiveGuard.graph p).guardFactor u).1=
      (pairEval (P74PositiveGuard.graph p).guardFactor u).2+1 ∧
    (pairEval (P74PositiveGuard.graph p).strong u).1=
      (pairEval (P74PositiveGuard.graph p).strong u).2+1 := by
  let u := partial74 v
  have hJ0 : 0<v 0 := Natural80JPosDraft.J_pos_of_zero p K v hK hKpos hz
  have hJ : 0<u 0 := by simpa [u,partial74] using hJ0
  have hw : 0<u 6 := by simp [u,partial74]
  have hs : 0<u 7 := by simp [u,partial74]
  have hz74 : InternalZero (P74PositiveGuard.graph p).output u :=
    (internalZero_iff_partial p v).mp hz
  obtain ⟨hm,ha,hstrong⟩ := restricted_residues p u
  exact factor_units_of_zero p beta u hbeta hb hJ hw hs hz74 hm ha hstrong

/-- Literal right side of the 74 main unit; its pair binding is not
asserted here. -/
def mainRhs (p : Fin 4 → ℤ) : Expr (Fin 14) :=
  let g := P74PositiveGuard.graph p
  g.U*g.U*(1+((3+4*g.a)+g.a*g.a)*(g.c*g.c))

/-- Conditional bridge from the main factor unit to the signed-magnitude
norm. The literal root-pair and right-side natural-pair bindings are
deliberately explicit hypotheses. -/
theorem main_norm_of_unit (p : Fin 4 → ℤ) (u : Fin 14 → V) (P N rhs : V)
    (hunit : (pairEval (P74PositiveGuard.graph p).main u).1=
      (pairEval (P74PositiveGuard.graph p).main u).2+1)
    (hroot : Equivalent (pairEval (P74PositiveGuard.graph p).Dstar u) (P,N))
    (hrhs : pairEval (mainRhs p) u=(rhs,0)) :
    magnitude (P,N)*magnitude (P,N)=rhs := by
  have hu := hunit
  rw [FactorResidues74Draft.main_shape] at hu
  change (pairEval (1+((P74PositiveGuard.graph p).Dstar*(P74PositiveGuard.graph p).Dstar-mainRhs p)) u).1 =
    (pairEval (1+((P74PositiveGuard.graph p).Dstar*(P74PositiveGuard.graph p).Dstar-mainRhs p)) u).2+1 at hu
  have hn := unit_square_norm (P74PositiveGuard.graph p).Dstar (mainRhs p) u hu
  rw [hrhs] at hn
  have hmag := magnitude_equivalent hroot
  rw [hmag] at hn
  simpa using hn

end DiophantineConsistency.Natural80OwnZeroNormDraft

#print axioms DiophantineConsistency.Natural80OwnZeroNormDraft.units_of_80_zero
#print axioms DiophantineConsistency.Natural80OwnZeroNormDraft.main_norm_of_unit
