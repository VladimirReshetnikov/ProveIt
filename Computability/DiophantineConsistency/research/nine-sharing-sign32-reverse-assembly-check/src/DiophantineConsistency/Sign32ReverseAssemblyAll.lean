import DiophantineConsistency.Sign32ReverseAssembly02

/-! UNCOMPILED final reverse residual assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32ReverseAssembly
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem new_rows (p : Fin 4 → ℤ) :
    SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p =
      [SharingSeed32Sextic.firstResidual p,
       Sign32Substitution01.newX p,
       Sign32Substitution01.newY p,
       Sign32Substitution01.newE p,
       Sign32Substitution02.newkY p,
       Sign32Substitution02.newell p,
       Sign32Substitution02.newDelta p,
       Sign32Substitution03.newmainRoot p,
       Sign32Substitution03.newc2 p,
       Sign32Substitution03.newDc2 p,
       Sign32Substitution04.newN1 p,
       Sign32Substitution04.newgap p,
       Sign32Substitution04.newtau p,
       Sign32Substitution05.newN0 p,
       Sign32Substitution05.newNt p,
       Sign32Substitution05.newf2 p,
       Sign32Substitution06.newcTminusR p,
       Sign32Substitution06.newV p,
       Sign32Substitution06.newnormalizedS p,
       Sign32Substitution07.newnormalizedS2 p,
       Sign32Substitution07.newV2minusY2 p,
       Sign32Substitution07.newNa p,
       Sign32Substitution07.newscaledNs p] := by rfl

theorem source33_to_source32 (p : Fin 4 → ℤ) (beta : V) (v : Fin 34 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed33.seed p) v) :
    InternalZero (SharingSeed32Sextic.seed p) (Sign32CoordinateRecover.drop v) := by
  have hr := Sign32CoordinateRecover.lift_drop p beta v hp0 hz
  have hz' : InternalZero (SharingSeed33.seed p) (Sign32Substitution00.lift beta (Sign32CoordinateRecover.drop v)) := by
    rw [hr]
    exact hz
  have ho := (SharingSign33Squares.seed_zero_iff_residuals p (Sign32Substitution00.lift beta (Sign32CoordinateRecover.drop v))).mp hz'
  apply (SharingSign32Squares.seed_zero_iff_residuals p (Sign32CoordinateRecover.drop v)).mpr
  intro e he
  rw [new_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact q3_zero p beta (Sign32CoordinateRecover.drop v) hp0 ho
  · exact X_zero p beta (Sign32CoordinateRecover.drop v) ho
  · exact Y_zero p beta (Sign32CoordinateRecover.drop v) ho
  · exact E_zero p beta (Sign32CoordinateRecover.drop v) ho
  · exact kY_zero p beta (Sign32CoordinateRecover.drop v) ho
  · exact ell_zero p beta (Sign32CoordinateRecover.drop v) ho
  · exact Delta_zero p beta (Sign32CoordinateRecover.drop v) ho
  · exact mainRoot_zero p beta (Sign32CoordinateRecover.drop v) ho
  · exact c2_zero p beta (Sign32CoordinateRecover.drop v) ho
  · exact Dc2_zero p beta (Sign32CoordinateRecover.drop v) ho
  · exact N1_zero p beta (Sign32CoordinateRecover.drop v) ho
  · exact gap_zero p beta (Sign32CoordinateRecover.drop v) ho
  · exact tau_zero p beta (Sign32CoordinateRecover.drop v) hp0 ho
  · exact N0_zero p beta (Sign32CoordinateRecover.drop v) ho
  · exact Nt_zero p beta (Sign32CoordinateRecover.drop v) ho
  · exact f2_zero p beta (Sign32CoordinateRecover.drop v) ho
  · exact cTminusR_zero p beta (Sign32CoordinateRecover.drop v) hp0 ho
  · exact V_zero p beta (Sign32CoordinateRecover.drop v) ho
  · exact normalizedS_zero p beta (Sign32CoordinateRecover.drop v) ho
  · exact normalizedS2_zero p beta (Sign32CoordinateRecover.drop v) ho
  · exact V2minusY2_zero p beta (Sign32CoordinateRecover.drop v) ho
  · exact Na_zero p beta (Sign32CoordinateRecover.drop v) ho
  · exact scaledNs_zero p beta (Sign32CoordinateRecover.drop v) ho
end DiophantineConsistency.Sign32ReverseAssembly

#print axioms DiophantineConsistency.Sign32ReverseAssembly.new_rows
#print axioms DiophantineConsistency.Sign32ReverseAssembly.source33_to_source32
