import DiophantineConsistency.SharingTopology38

/-! Two applications of checked topology give ring-value agreement. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33RingTopology
open SharingGateModel SharingTopology38
variable {R ι : Type*} [CommRing R] [DecidableEq ι]

theorem static_agrees_of_topological (gs : List (Gate ι)) (done : List ι)
    (env reference : ι → R) (htop : Topological gs done)
    (hinit : ∀ i ∈ done, env i = reference i)
    (href : ∀ g ∈ gs,
      reference g.target = ringCompute g.op (reference g.left) (reference g.right))
    (hvalue : ∀ g ∈ gs,
      env g.target = ringCompute g.op (env g.left) (env g.right)) :
    ∀ i ∈ completed gs done, env i = reference i := by
  have hv := ringRun_agrees_of_topological gs done env env htop (fun _ _ => rfl) hvalue
  have hr := ringRun_agrees_of_topological gs done env reference htop hinit href
  intro i hi
  exact (hv i hi).symm.trans (hr i hi)
end DiophantineConsistency.Sign33RingTopology
#print axioms DiophantineConsistency.Sign33RingTopology.static_agrees_of_topological
