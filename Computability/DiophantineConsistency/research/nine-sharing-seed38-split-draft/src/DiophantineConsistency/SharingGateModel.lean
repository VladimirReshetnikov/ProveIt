import DiophantineConsistency.NineFreshJones

/-! UNCOMPILED DRAFT. Generic signed-pair gate algebra for the proposed
sharing-aware quartic seeds. No declaration here is a checked result, and
this does not prove the 54- or 52-witness seed bridge. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingGateModel

/-- Two natural-like values represent their difference in a ring. -/
structure SignedPair (S : Type*) where
  positive : S
  negative : S

inductive GateOp where
  | add | sub | mul
  deriving DecidableEq

variable {S R : Type*} [CommSemiring S] [CommRing R]

/-- The witness components are computed using natural addition and multiplication only. -/
def pairCompute (op : GateOp) (a b : SignedPair S) : SignedPair S :=
  match op with
  | .add => ⟨a.positive + b.positive, a.negative + b.negative⟩
  | .sub => ⟨a.positive + b.negative, a.negative + b.positive⟩
  | .mul => ⟨a.positive * b.positive + a.negative * b.negative,
      a.positive * b.negative + a.negative * b.positive⟩

def ringCompute (op : GateOp) (a b : R) : R :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b

def pairValue (ι : S →+* R) (a : SignedPair S) : R :=
  ι a.positive - ι a.negative

/-- Candidate forward algebra for every inline gate. -/
theorem pairValue_compute (ι : S →+* R) (op : GateOp) (a b : SignedPair S) :
    pairValue ι (pairCompute op a b) = ringCompute op (pairValue ι a) (pairValue ι b) := by
  cases op <;> simp only [pairCompute, ringCompute, pairValue, map_add, map_mul] <;> ring

/-- The two materialized-coordinate residuals interpreted in the ring. -/
def positiveResidual (ι : S →+* R) (op : GateOp)
    (a b out : SignedPair S) : R :=
  ι out.positive - ι (pairCompute op a b).positive

def negativeResidual (ι : S →+* R) (op : GateOp)
    (a b out : SignedPair S) : R :=
  ι out.negative - ι (pairCompute op a b).negative

/-- Candidate forward witness construction: use the computed natural pair. -/
theorem computed_residuals_zero (ι : S →+* R) (op : GateOp) (a b : SignedPair S) :
    positiveResidual ι op a b (pairCompute op a b) = 0 ∧
      negativeResidual ι op a b (pairCompute op a b) = 0 := by
  simp [positiveResidual, negativeResidual]

/-- Candidate backward gate step from vanishing residuals to the ring value. -/
theorem materialized_value (ι : S →+* R) (op : GateOp) (a b out : SignedPair S)
    (hp : positiveResidual ι op a b out = 0)
    (hn : negativeResidual ι op a b out = 0) :
    pairValue ι out = ringCompute op (pairValue ι a) (pairValue ι b) := by
  have hp' : ι out.positive = ι (pairCompute op a b).positive := sub_eq_zero.mp hp
  have hn' : ι out.negative = ι (pairCompute op a b).negative := sub_eq_zero.mp hn
  calc
    pairValue ι out = pairValue ι (pairCompute op a b) := by
      simp only [pairValue, hp', hn']
    _ = ringCompute op (pairValue ι a) (pairValue ι b) := pairValue_compute ι op a b

/-- A nonnegative materialized result needs only its positive component. -/
theorem one_component_value (ι : S →+* R) (op : GateOp) (a b : SignedPair S) (out : S)
    (hz : (pairCompute op a b).negative = 0)
    (hp : ι out - ι (pairCompute op a b).positive = 0) :
    pairValue ι ⟨out, 0⟩ = ringCompute op (pairValue ι a) (pairValue ι b) := by
  apply materialized_value ι op a b ⟨out, 0⟩
  · exact hp
  · simp [negativeResidual, hz]

/-- A finite gate updates one named pair while preserving all other entries. -/
structure Gate (ι : Type*) where
  target : ι
  left : ι
  right : ι
  op : GateOp

variable {ι : Type*} [DecidableEq ι]

def pairStep (g : Gate ι) (v : ι → SignedPair S) : ι → SignedPair S :=
  Function.update v g.target (pairCompute g.op (v g.left) (v g.right))

def ringStep (g : Gate ι) (v : ι → R) : ι → R :=
  Function.update v g.target (ringCompute g.op (v g.left) (v g.right))

/-- Candidate one-step commutation; no graph-specific assumptions. -/
theorem pairStep_value (embed : S →+* R) (g : Gate ι) (v : ι → SignedPair S) :
    (fun i => pairValue embed (pairStep g v i)) =
      ringStep g (fun i => pairValue embed (v i)) := by
  funext i
  by_cases h : i = g.target
  · subst i
    simp only [pairStep, ringStep, Function.update_self]
    exact pairValue_compute embed g.op (v g.left) (v g.right)
  · simp [pairStep, ringStep, Function.update_apply, h]

def pairRun (gs : List (Gate ι)) (v : ι → SignedPair S) : ι → SignedPair S :=
  gs.foldl (fun e g => pairStep g e) v

def ringRun (gs : List (Gate ι)) (v : ι → R) : ι → R :=
  gs.foldl (fun e g => ringStep g e) v

/-- Candidate forward replay: natural-pair execution commutes with ring execution. -/
theorem pairRun_value (embed : S →+* R) (gs : List (Gate ι))
    (v : ι → SignedPair S) :
    (fun i => pairValue embed (pairRun gs v i)) =
      ringRun gs (fun i => pairValue embed (v i)) := by
  induction gs generalizing v with
  | nil => rfl
  | cons g gs ih =>
    change (fun i => pairValue embed (pairRun gs (pairStep g v) i)) =
      ringRun gs (ringStep g (fun i => pairValue embed (v i)))
    rw [ih, pairStep_value]

/-- A materialized gate may choose any natural pair satisfying both residuals. -/
def StepResidual (embed : S →+* R) (g : Gate ι)
    (before after : ι → SignedPair S) : Prop :=
  (∀ i, i ≠ g.target → after i = before i) ∧
    positiveResidual embed g.op (before g.left) (before g.right) (after g.target) = 0 ∧
    negativeResidual embed g.op (before g.left) (before g.right) (after g.target) = 0

/-- Candidate backward one-step semantics, with no injectivity assumption. -/
theorem stepResidual_value (embed : S →+* R) (g : Gate ι)
    (before after : ι → SignedPair S) (h : StepResidual embed g before after) :
    (fun i => pairValue embed (after i)) =
      ringStep g (fun i => pairValue embed (before i)) := by
  funext i
  by_cases hi : i = g.target
  · subst i
    simp only [ringStep, Function.update_self]
    exact materialized_value embed g.op (before g.left) (before g.right)
      (after g.target) h.2.1 h.2.2
  · rw [h.1 i hi]
    simp [ringStep, Function.update_apply, hi]

/-- A chronological trace of arbitrary residual-satisfying witness choices. -/
inductive ResidualTrace (embed : S →+* R) :
    List (Gate ι) → (ι → SignedPair S) → (ι → SignedPair S) → Prop
  | nil (v : ι → SignedPair S) : ResidualTrace embed [] v v
  | cons (g : Gate ι) (gs : List (Gate ι))
      (before middle after : ι → SignedPair S)
      (step : StepResidual embed g before middle)
      (rest : ResidualTrace embed gs middle after) :
      ResidualTrace embed (g :: gs) before after

/-- Candidate reverse replay from all chronological residual constraints. -/
theorem residualTrace_value (embed : S →+* R) {gs : List (Gate ι)}
    {before after : ι → SignedPair S} (h : ResidualTrace embed gs before after) :
    (fun i => pairValue embed (after i)) =
      ringRun gs (fun i => pairValue embed (before i)) := by
  induction h with
  | nil => rfl
  | cons g gs before middle after step rest ih =>
    change (fun i => pairValue embed (after i)) =
      ringRun gs (ringStep g (fun i => pairValue embed (before i)))
    rw [← stepResidual_value embed g before middle step]
    exact ih

-- Remaining: represent the finite source graph in Lean, prove acyclic replay,
-- construct a ResidualTrace from one final assignment using acyclicity;
-- link every inlined/cut pair to these gate rules, extract vanishing residuals
-- from the sum of squares in each IΣ₁ model, and construct/recover all 54 or
-- 52 seed coordinates. Then prove degree, normalization and current bridge.
end DiophantineConsistency.SharingGateModel
