import DiophantineConsistency.AdaptiveAQ32
import DiophantineConsistency.AdaptiveAQ34
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveVSignTransport32
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem from42 (p : Fin 4 → ℕ) (hb : (2:V) ≤ (p 0:V)) (v : Fin 42 → V)
    (hv : ∀ i, 0 < v i)
    (hz : InternalZero (AdaptiveNamedValues42.literal (fun j => (p j:ℤ))) v)
    (hsign : v 31 < v 30) :
    ∃ u : Fin 32 → V, (∀ i, 0 < u i) ∧
      InternalZero (AdaptiveAQ32Literal.literal (fun j => (p j:ℤ))) u ∧ u 24 < u 23 := by
  let v40 := AdaptiveAQ40Maps.project v
  have hp40 : ∀ i, 0 < v40 i := AdaptiveAQ40Maps.project_pos v hv
  have hz40 : InternalZero (AdaptiveAQ40Literal.literal (fun j => (p j:ℤ))) v40 :=
    AdaptiveAQ40.project_zero _ v hz
  let v36 := AdaptiveAQ36Maps.project v40
  have hp36 : ∀ i, 0 < v36 i := AdaptiveAQ36Maps.project_pos v40 hp40
  have hz36 : InternalZero (AdaptiveAQ36Literal.literal (fun j => (p j:ℤ))) v36 :=
    AdaptiveAQ36.project_zero _ v40 hz40
  let v35 := AdaptiveAQ35Maps.project v36
  have hp35 : ∀ i, 0 < v35 i := AdaptiveAQ35Maps.project_pos v36 hp36
  have hz35 : InternalZero (AdaptiveAQ35Literal.literal (fun j => (p j:ℤ))) v35 :=
    AdaptiveAQ35.project_zero _ v36 hz36
  obtain ⟨r,hr,hmag,hz34⟩ := AdaptiveAQ34.project_zero _ v35 hp35 hz35
  let v34 := AdaptiveAQ34Maps.project v35 r
  have hp34 : ∀ i, 0 < v34 i := AdaptiveAQ34Maps.project_pos v35 r hp35 hr hmag
  let v33 := AdaptiveAQ33Maps.project v34
  have hp33 : ∀ i, 0 < v33 i := AdaptiveAQ33Maps.project_pos p v34 hp34 hz34
  have hz33 : InternalZero (AdaptiveAQ33Literal.literal (fun j => (p j:ℤ))) v33 :=
    AdaptiveAQ33Transport.project_zero p v34 hp34 hz34
  have hd := AdaptiveAQ32Positive.signed_d_positive p v33 hb hp33 hz33
  let v32 := AdaptiveAQ32Maps.project v33
  have hp32 : ∀ i, 0 < v32 i := AdaptiveAQ32Maps.project_pos v33 hp33 hd
  have hz32 : InternalZero (AdaptiveAQ32Literal.literal (fun j => (p j:ℤ))) v32 :=
    AdaptiveAQ32Transport.project_zero _ v33 hd hz33
  refine ⟨v32,hp32,hz32,?_⟩
  simpa [v32,v33,v34,v35,v36,v40,AdaptiveAQ32Maps.project,AdaptiveAQ32Context.oldRest,AdaptiveAQ32Context.newRest,
    AdaptiveAQ33Maps.project,AdaptiveAQ33Context.oldRest,AdaptiveAQ33Context.newRest,
    AdaptiveAQ34Maps.project,AdaptiveAQ35Maps.project,AdaptiveAQ35Context.oldRest,
    AdaptiveAQ36Maps.project,AdaptiveAQ36Context.oldRest,AdaptiveAQ40Maps.project,AdaptiveAQ40Context.oldRest] using hsign
#print axioms from42
end DiophantineConsistency.AdaptiveVSignTransport32
