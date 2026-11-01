import DiophantineConsistency.AdaptiveQF41Norm
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveQF41Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveQF41Context AdaptiveQF41Zeros AdaptiveQF41Maps AdaptiveQF41Norm
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem project_zero (p : Fin 4 → ℤ) (v : Fin 42 → V) (hv : ∀i,0<v i)
    (hz : InternalZero (AdaptiveQV42Context.literal p) v) :
    ∃ t : V, 0<t ∧ InternalZero (literal p) (project v t) := by
  obtain ⟨t,ht,hzscale,hn⟩ := quotient p v hv hz
  refine ⟨t,ht,?_⟩
  apply (new_all p (project v t)).mpr
  intro i
  by_cases hi : i=0
  · subst i
    apply (child_norm p (project v t)).mpr
    simpa [project] using hn
  · let j : Fin 31 := ⟨i.val-1,by omega⟩
    have hj : newIndex j=i := Fin.ext (by dsimp [newIndex,j]; omega)
    rw [←hj]
    exact (project_common p v t hzscale j).mp ((old_all p v).mp hz (oldIndex j))

theorem extend_zero (p : Fin 4 → ℤ) (v : Fin 41 → V)
    (hz : InternalZero (literal p) v) : InternalZero (AdaptiveQV42Context.literal p) (extend v) := by
  have hn := (child_norm p v).mp ((new_all p v).mp hz 0)
  apply (old_all p (extend v)).mpr
  intro i
  by_cases h0 : i=0
  · subst i
    change InternalZero ((.var 23*.var 23)-(.var 29*(1+.var 30)) : Expr (Fin 42)) (extend v)
    have heq : (extend v 23)*(extend v 23)=(extend v 29)*(1+extend v 30) := by
      change (v 14*v 23)*(v 14*v 23)=(v 14*v 14)*(1+v 29)
      rw [←hn]
      ring
    simpa [InternalZero,Expr.splitNatural,NatExpr.evalSemiring,HSub.hSub,Sub.sub] using heq
  by_cases h20 : i=20
  · subst i
    change InternalZero ((.var 29-(.var 14*.var 14)) : Expr (Fin 42)) (extend v)
    simp [InternalZero,Expr.splitNatural,NatExpr.evalSemiring,HSub.hSub,Sub.sub,extend]
  · have hex : ∃ j : Fin 31, oldIndex j=i := by
      fin_cases i <;> try {exfalso; exact h0 rfl} <;> try {exfalso; exact h20 rfl} <;>
      first
      | exact ⟨0,rfl⟩
      | exact ⟨1,rfl⟩
      | exact ⟨2,rfl⟩
      | exact ⟨3,rfl⟩
      | exact ⟨4,rfl⟩
      | exact ⟨5,rfl⟩
      | exact ⟨6,rfl⟩
      | exact ⟨7,rfl⟩
      | exact ⟨8,rfl⟩
      | exact ⟨9,rfl⟩
      | exact ⟨10,rfl⟩
      | exact ⟨11,rfl⟩
      | exact ⟨12,rfl⟩
      | exact ⟨13,rfl⟩
      | exact ⟨14,rfl⟩
      | exact ⟨15,rfl⟩
      | exact ⟨16,rfl⟩
      | exact ⟨17,rfl⟩
      | exact ⟨18,rfl⟩
      | exact ⟨19,rfl⟩
      | exact ⟨20,rfl⟩
      | exact ⟨21,rfl⟩
      | exact ⟨22,rfl⟩
      | exact ⟨23,rfl⟩
      | exact ⟨24,rfl⟩
      | exact ⟨25,rfl⟩
      | exact ⟨26,rfl⟩
      | exact ⟨27,rfl⟩
      | exact ⟨28,rfl⟩
      | exact ⟨29,rfl⟩
      | exact ⟨30,rfl⟩
    obtain ⟨j,hj⟩ := hex
    rw [←hj]
    exact (extend_common p v j).mpr ((new_all p v).mp hz (newIndex j))

/-- Both directions are over positive inputs in arbitrary IΣ₁ models. -/
theorem shifted_no_zero_iff (p : Fin 4 → ℤ) :
    (∀ v : Fin 41 → V, ¬ InternalZero (positiveShift (literal p)) v) ↔
      ∀ v : Fin 42 → V, ¬ InternalZero (positiveShift (AdaptiveQV42Context.literal p)) v := by
  constructor
  · intro h v hz
    let old : Fin 42 → V := fun i => v i+1
    have hp : ∀ i, 0<old i := fun i => lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have hzero : InternalZero (AdaptiveQV42Context.literal p) old := (internalZero_positiveShift _ _).mp hz
    obtain ⟨t,ht,hn⟩ := project_zero p old hp hzero
    have hnewpos := project_pos old t hp ht
    let shifted : Fin 41 → V := fun i => project old t i-1
    have hs : (fun i => shifted i+1)=project old t := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hnewpos i))
    apply h shifted
    rw [internalZero_positiveShift,hs]
    exact hn
  · intro h v hz
    let new : Fin 41 → V := fun i => v i+1
    have hp : ∀ i,0<new i := fun i => lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
    have hzero : InternalZero (literal p) new := (internalZero_positiveShift _ _).mp hz
    have holdpos := extend_pos new hp
    have holdzero := extend_zero p new hzero
    let shifted : Fin 42 → V := fun i => extend new i-1
    have hs : (fun i => shifted i+1)=extend new := by
      funext i
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (holdpos i))
    apply h shifted
    rw [internalZero_positiveShift,hs]
    exact holdzero
#print axioms project_zero
#print axioms extend_zero
#print axioms shifted_no_zero_iff
end DiophantineConsistency.AdaptiveQF41Model
