import DiophantineConsistency.Sign32ForwardAssembly02

/-! UNCOMPILED final forward residual assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32ForwardAssembly
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem old_rows (p : Fin 4 → ℤ) :
    SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p =
      [SharingSeed33.firstResidual p,
       Sign32Substitution00.oldQ3 p,
       Sign32Substitution01.oldX p,
       Sign32Substitution01.oldY p,
       Sign32Substitution01.oldE p,
       Sign32Substitution02.oldkY p,
       Sign32Substitution02.oldell p,
       Sign32Substitution02.oldDelta p,
       Sign32Substitution03.oldmainRoot p,
       Sign32Substitution03.oldc2 p,
       Sign32Substitution03.oldDc2 p,
       Sign32Substitution04.oldN1 p,
       Sign32Substitution04.oldgap p,
       Sign32Substitution04.oldtau p,
       Sign32Substitution05.oldN0 p,
       Sign32Substitution05.oldNt p,
       Sign32Substitution05.oldf2 p,
       Sign32Substitution06.oldcTminusR p,
       Sign32Substitution06.oldV p,
       Sign32Substitution06.oldnormalizedS p,
       Sign32Substitution07.oldnormalizedS2 p,
       Sign32Substitution07.oldV2minusY2 p,
       Sign32Substitution07.oldNa p,
       Sign32Substitution07.oldscaledNs p] := by rfl

theorem source32_to_source33 (p : Fin 4 → ℤ) (beta : V) (v : Fin 33 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed32Sextic.seed p) v) :
    InternalZero (SharingSeed33.seed p) (Sign32Substitution00.lift beta v) := by
  have hn := (SharingSign32Squares.seed_zero_iff_residuals p v).mp hz
  apply (SharingSign33Squares.seed_zero_iff_residuals p (Sign32Substitution00.lift beta v)).mpr
  intro e he
  rw [old_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Sign32Substitution00.old_q2_zero p beta v hp0
  · exact q3_zero p beta v hp0 hn
  · exact X_zero p beta v hn
  · exact Y_zero p beta v hn
  · exact E_zero p beta v hn
  · exact kY_zero p beta v hn
  · exact ell_zero p beta v hn
  · exact Delta_zero p beta v hn
  · exact mainRoot_zero p beta v hn
  · exact c2_zero p beta v hn
  · exact Dc2_zero p beta v hn
  · exact N1_zero p beta v hn
  · exact gap_zero p beta v hn
  · exact tau_zero p beta v hp0 hn
  · exact N0_zero p beta v hn
  · exact Nt_zero p beta v hn
  · exact f2_zero p beta v hn
  · exact cTminusR_zero p beta v hp0 hn
  · exact V_zero p beta v hn
  · exact normalizedS_zero p beta v hn
  · exact normalizedS2_zero p beta v hn
  · exact V2minusY2_zero p beta v hn
  · exact Na_zero p beta v hn
  · exact scaledNs_zero p beta v hn
end DiophantineConsistency.Sign32ForwardAssembly

#print axioms DiophantineConsistency.Sign32ForwardAssembly.old_rows
#print axioms DiophantineConsistency.Sign32ForwardAssembly.source32_to_source33
