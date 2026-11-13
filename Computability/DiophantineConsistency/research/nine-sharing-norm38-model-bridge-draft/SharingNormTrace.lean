import DiophantineConsistency.SharingGateModel

/-! UNCOMPILED DRAFT. General reverse-trace and topological invariant lemmas.
The 38-seed specialization and all iPRA endpoints remain unproved. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingNormTrace
open SharingGateModel

variable {S R ι : Type*} [CommSemiring S] [CommRing R] [DecidableEq ι]

/-- A single final assignment satisfying every gate supplies a constant trace.
The final assignment itself can serve as every intermediate state. -/
theorem constantTrace (embed : S →+* R) (gs : List (Gate ι)) (v : ι → SignedPair S)
    (h : ∀ g ∈ gs,
      positiveResidual embed g.op (v g.left) (v g.right) (v g.target) = 0 ∧
      negativeResidual embed g.op (v g.left) (v g.right) (v g.target) = 0) :
    ResidualTrace embed gs v v := by
  induction gs with
  | nil => exact ResidualTrace.nil v
  | cons g gs ih =>
    apply ResidualTrace.cons g gs v v v
    · exact ⟨fun _ _ => rfl, h g (by simp)⟩
    · apply ih
      intro e he
      exact h e (by simp [he])

/-- Candidate consequence: gate equations make the represented ring assignment
fixed under the entire gate replay. -/
theorem fixedPoint_of_residuals (embed : S →+* R) (gs : List (Gate ι))
    (v : ι → SignedPair S)
    (h : ∀ g ∈ gs,
      positiveResidual embed g.op (v g.left) (v g.right) (v g.target) = 0 ∧
      negativeResidual embed g.op (v g.left) (v g.right) (v g.target) = 0) :
    (fun i => pairValue embed (v i)) = ringRun gs (fun i => pairValue embed (v i)) :=
  residualTrace_value embed (constantTrace embed gs v h)

/-- A reference valuation is preserved on already certified nodes, and a
fresh gate target becomes certified when its operands were certified. -/
theorem ringStep_extends (g : Gate ι) (done : List ι) (env reference : ι → R)
    (hprev : ∀ i ∈ done, env i = reference i)
    (hleft : env g.left = reference g.left)
    (hright : env g.right = reference g.right)
    (hreference : reference g.target = ringCompute g.op (reference g.left) (reference g.right))
    (hfresh : ∀ i ∈ done, i ≠ g.target) :
    ∀ i ∈ g.target :: done, ringStep g env i = reference i := by
  intro i hi
  simp only [List.mem_cons] at hi
  rcases hi with rfl | hi
  · simp only [ringStep, Function.update_same, hleft, hright]
    exact hreference.symm
  · have hn : i ≠ g.target := hfresh i hi
    simpa [ringStep, Function.update_noteq, hn, Ne.symm hn] using hprev i hi

-- Unresolved: build a final pair assignment for all 60 graph nodes from the
-- 38 seed witnesses; prove each inline or cut relation and use constantTrace.
-- Then instantiate ringStep_extends along the concrete topological graph to
-- identify the five terminal values with Carrier65.core in every model.
end DiophantineConsistency.SharingNormTrace
