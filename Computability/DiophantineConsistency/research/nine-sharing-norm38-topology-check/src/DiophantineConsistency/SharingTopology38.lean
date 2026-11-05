import DiophantineConsistency.NormAssignment38

/-! Uncompiled extension of checked generic trace lemmas. No claim about
concrete seed residuals or Carrier65 correspondence is made here. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingTopology38
open SharingGateModel SharingNormTrace

variable {R ι : Type*} [CommRing R] [DecidableEq ι]

/-- Every gate consumes already known nodes and introduces a fresh target. -/
def Topological : List (Gate ι) → List ι → Prop
  | [], _ => True
  | g :: gs, done =>
      g.left ∈ done ∧ g.right ∈ done ∧ g.target ∉ done ∧ Topological gs (g.target :: done)

/-- The nodes known after replaying all gates. -/
def completed : List (Gate ι) → List ι → List ι
  | [], done => done
  | g :: gs, done => completed gs (g.target :: done)

/-- A topologically ordered gate replay agrees with any reference assignment
that agrees initially and satisfies every corresponding ring gate equation. -/
theorem ringRun_agrees_of_topological (gs : List (Gate ι)) (done : List ι)
    (env reference : ι → R) (htop : Topological gs done)
    (hinit : ∀ i ∈ done, env i = reference i)
    (href : ∀ g ∈ gs,
      reference g.target = ringCompute g.op (reference g.left) (reference g.right)) :
    ∀ i ∈ completed gs done, ringRun gs env i = reference i := by
  induction gs generalizing done env with
  | nil => simpa [completed, ringRun] using hinit
  | cons g gs ih =>
    rcases htop with ⟨hl, hr, hfresh, hrest⟩
    have hrefg := href g (by simp)
    have hstep : ∀ i ∈ g.target :: done, ringStep g env i = reference i :=
      ringStep_extends g done env reference hinit (hinit g.left hl) (hinit g.right hr)
        hrefg (fun i hi heq => hfresh (heq ▸ hi))
    have hremainder : ∀ e ∈ gs,
        reference e.target = ringCompute e.op (reference e.left) (reference e.right) :=
      fun e he => href e (by simp [he])
    change ∀ i ∈ completed gs (g.target :: done),
      ringRun gs (ringStep g env) i = reference i
    exact ih (g.target :: done) (ringStep g env) hrest hstep hremainder

/-- A single concrete assignment satisfying all gate residuals is a fixed
point of its gate replay. This does not derive those residuals from the seed. -/
theorem static_assignment_fixed {S : Type*} [CommSemiring S]
    (embed : S →+* R) (ports : Fin 4 → S) (w : Fin 38 → S)
    (h : NormAssignment38.gatesHold embed ports w) :
    (fun i => pairValue embed (NormAssignment38.assignment ports w i)) =
      ringRun NormAssignment38.gates
        (fun i => pairValue embed (NormAssignment38.assignment ports w i)) := by
  exact fixedPoint_of_residuals embed NormAssignment38.gates
    (NormAssignment38.assignment ports w) h
end DiophantineConsistency.SharingTopology38

#print axioms DiophantineConsistency.SharingTopology38.ringRun_agrees_of_topological
#print axioms DiophantineConsistency.SharingTopology38.static_assignment_fixed
