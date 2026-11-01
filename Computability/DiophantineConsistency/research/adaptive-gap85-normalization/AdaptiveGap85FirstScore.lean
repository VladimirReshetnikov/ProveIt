import DiophantineConsistency.AdaptiveGap85ScoreCoding
import DiophantineConsistency.AdaptiveGap85ThirdMinimal

/-! Least first-coordinate scores of positive 85 zeros.

This reuses the fixed-arity Cantor coding of the full tuple and applies
the IΣ₁ least-number principle. It does not assert existence of a zero,
normalization of a zero, or equivalence with the 86-operation equation.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85FirstScore
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveGap85Literal AdaptiveGap85ScoreCoding
open AdaptiveGap85ThirdMinimal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def firstScore (p : Fin 4 → ℕ) (m : V) : Prop :=
  ∃ v : Fin 13 → V, (∀ i,0<v i) ∧
    InternalZero (expressionAt85 (fun j => (p j:ℤ))) v ∧ m=v 1

def codeFirst (code : V) : V := tupleProjection 12 code 1

def firstCodedScore (p : Fin 4 → ℕ) (m : V) : Prop :=
  ∃ code : V, tuplePositive code ∧ codeZero p code ∧ m=codeFirst code

theorem firstCodedScore_iff (p : Fin 4 → ℕ) (m : V) :
    firstCodedScore p m ↔ firstScore p m := by
  constructor
  · rintro ⟨code,hpos,hzero,heq⟩
    exact ⟨tupleProjection 12 code,(tuplePositive_iff code).mp hpos,hzero,heq⟩
  · rintro ⟨v,hpos,hzero,heq⟩
    refine ⟨tupleValue 12 v,?_,?_,?_⟩
    · apply (tuplePositive_iff _).mpr
      simpa only [tupleProjection_value] using hpos
    · simpa only [codeZero,tupleProjection_value] using hzero
    · simpa only [codeFirst,tupleProjection_value] using heq

theorem codeFirst_definable : 𝚺₁-Function₁[V] (codeFirst (V:=V)) := by
  exact (projection_defined (V:=V) 12 1).to_definable

theorem firstCodedScore_definable (p : Fin 4 → ℕ) :
    𝚺₁-Predicate (firstCodedScore (V:=V) p) := by
  letI := tuplePositive_definable (V:=V)
  letI := codeZero_definable (V:=V) p
  letI := codeFirst_definable (V:=V)
  unfold firstCodedScore
  definability

theorem firstScore_definable (p : Fin 4 → ℕ) :
    𝚺₁-Predicate (firstScore (V:=V) p) := by
  have he : firstScore (V:=V) p = firstCodedScore p := by
    funext m
    exact propext (firstCodedScore_iff p m).symm
  rw [he]
  exact firstCodedScore_definable p

/-- Any existing positive zero has a positive zero with least F coordinate. -/
theorem exists_first_minimizing_zero (p : Fin 4 → ℕ)
    (hex : ∃ v : Fin 13 → V, (∀ i,0<v i) ∧
      InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    ∃ v : Fin 13 → V, (∀ i,0<v i) ∧
      InternalZero (expressionAt85 (fun j => (p j:ℤ))) v ∧
      ∀ w : Fin 13 → V, (∀ i,0<w i) →
        InternalZero (expressionAt85 (fun j => (p j:ℤ))) w → v 1≤w 1 := by
  obtain ⟨u,hu,huz⟩ := hex
  have hwit : firstScore (V:=V) p (u 1) := ⟨u,hu,huz,rfl⟩
  obtain ⟨m,⟨v,hv,hz,hm⟩,hmin⟩ :=
    InductionOnHierarchy.least_number 𝚺 1 (firstScore_definable p) hwit
  refine ⟨v,hv,hz,?_⟩
  intro w hwp hwz
  apply le_of_not_gt
  intro hlt
  apply hmin (w 1)
  · simpa only [hm] using hlt
  · exact ⟨w,hwp,hwz,rfl⟩

/-- A least-F positive zero necessarily blocks one of the two decrements in
the third shift. Both existence of a zero and a positive first port are
explicit premises. -/
theorem exists_first_minimal_blocked (p : Fin 4 → ℕ)
    (hp : 0<(p 0:V))
    (hex : ∃ v : Fin 13 → V, (∀ i,0<v i) ∧
      InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    ∃ v : Fin 13 → V, (∀ i,0<v i) ∧
      InternalZero (expressionAt85 (fun j => (p j:ℤ))) v ∧
      (let b := v 0*(p 0:V); let q := 1+b;
       let A := v 6+(p 1:V)*q; let U := v 7*(q*q);
       let c := v 9+v 7*(v 9+v 10);
       v 1≤A*(c*U) ∨ v 12≤(q*q-1)*(A+1)*c) := by
  obtain ⟨v,hv,hz,hmin⟩ := exists_first_minimizing_zero p hex
  exact ⟨v,hv,hz,minimal_first_has_blocker p v hp hv hz hmin⟩
end DiophantineConsistency.AdaptiveGap85FirstScore
