/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Estimates.AllocatedSlicedEndpointIdentity

namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {D : Type*} [Fintype D] {B : D → Type*} [∀ d, Fintype (B d)]
variable (h : D → ℕ) (P : D → Prop) [DecidablePred P]

noncomputable def oneCubeEndpointReindex : OneCubeActiveEndpoint (B := B) h P ≃
    Fin 2 × PrincipalTupleIndex (fun d : {d // ¬P d} => B d.val) (fun d => h d.val) where
  toFun j := (finTwoEquiv.symm j.1.1, ⟨j.1.2, j.2⟩)
  invFun j := ⟨(finTwoEquiv j.1, j.2.1), j.2.2⟩
  left_inv j := by rcases j with ⟨⟨β, d⟩, b, i⟩; simp
  right_inv j := by rcases j with ⟨β, d, b, i⟩; simp

theorem oneCubeEndpointBox_pair_law :
    (unitBoxMeasure (OneCubeActiveEndpoint (B := B) h P)).map
      (fun x => ((fun j => x ⟨(false, j.1), j.2⟩), (fun j => x ⟨(true, j.1), j.2⟩))) =
    (unitBoxMeasure (PrincipalTupleIndex (fun d : {d // ¬P d} => B d.val) (fun d => h d.val))).prod
      (unitBoxMeasure (PrincipalTupleIndex (fun d : {d // ¬P d} => B d.val) (fun d => h d.val))) := by
  have h₁ := unitBoxMeasure_reindex (oneCubeEndpointReindex (B := B) h P)
  have h₂ := unitBoxMeasure_curry (Fin 2)
    (PrincipalTupleIndex (fun d : {d // ¬P d} => B d.val) (fun d => h d.val))
  have h₃ := measurePreserving_finTwoArrow
    (unitBoxMeasure (PrincipalTupleIndex (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)))
  exact (h₃.comp (h₂.comp h₁)).map_eq

def scalarOneCubeFromEndpoints {I : Type*} (p : (I → ℝ) × (I → ℝ)) (j : I) : Option (Fin 1) → ℝ
  | none => p.1 j
  | some _ => p.2 j - p.1 j

theorem scalarOneCubeFromEndpoints_law (I : Type*) [Fintype I] :
    ((unitBoxMeasure I).prod (unitBoxMeasure I)).map scalarOneCubeFromEndpoints =
      scalarCubeProductMeasure I (Fin 1) := by
  have hi : Measurable (scalarOneCubeFromEndpoints (I := I)) := by
    apply Measurable.of_eval
    intro j
    apply Measurable.of_eval
    intro i
    cases i <;> dsimp only [scalarOneCubeFromEndpoints] <;> fun_prop
  have he : Measurable (fun a : I → Option (Fin 1) → ℝ =>
      ((fun j => a j none), (fun j => a j none + a j (some 0)))) := by fun_prop
  rw [← scalarOneCube_product_endpoints I, Measure.map_map hi he]
  have hid : scalarOneCubeFromEndpoints ∘ (fun a : I → Option (Fin 1) → ℝ =>
      ((fun j => a j none), (fun j => a j none + a j (some 0)))) = id := by
    funext x j i
    cases i with
    | none => rfl
    | some i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp [scalarOneCubeFromEndpoints]
  rw [hid, Measure.map_id]

def oneCubeJointShiftScale
    (lower width : ∀ d : {d // ¬P d}, B d.val × Fin (h d.val) → ℝ)
    (x : PrincipalAxisParameter (B := B) (h := h) (α := Fin 1) (fun d => ¬P d) → ℝ)
    (j : PrincipalAxisParameter (B := B) (h := h) (α := Fin 1) (fun d => ¬P d)) : ℝ :=
  match j.2.2.2 with
  | none => lower j.1 (j.2.1, j.2.2.1) + width j.1 (j.2.1, j.2.2.1) * x j
  | some _ => width j.1 (j.2.1, j.2.2.1) * x j

omit [Fintype D] [∀ index, Fintype (B index)] [DecidablePred P] in
theorem oneCubeSlicedParameter_measurable
    [Fintype D] [∀ index, Fintype (B index)] [DecidablePred P]
    (lower width : ∀ d : {d // ¬P d}, B d.val × Fin (h d.val) → ℝ) :
    Measurable (oneCubeSlicedParameter h P lower width) := by
  apply Measurable.of_eval
  intro j
  unfold oneCubeSlicedParameter
  split <;> fun_prop

theorem oneCubeSlicedParameter_source_law
    (lower width : ∀ d : {d // ¬P d}, B d.val × Fin (h d.val) → ℝ) :
    (unitBoxMeasure (OneCubeActiveEndpoint (B := B) h P)).map (oneCubeSlicedParameter h P lower width) =
      (jointBooleanSource (B := fun d : {d // ¬P d} => B d.val) (α := Fin 1) (fun d => h d.val)).map
        (oneCubeJointShiftScale h P lower width) := by
  let pair : (OneCubeActiveEndpoint (B := B) h P → ℝ) →
      ((PrincipalTupleIndex (fun d : {d // ¬P d} => B d.val) (fun d => h d.val) → ℝ) ×
        (PrincipalTupleIndex (fun d : {d // ¬P d} => B d.val) (fun d => h d.val) → ℝ)) :=
    fun x => ((fun j => x ⟨(false, j.1), j.2⟩), (fun j => x ⟨(true, j.1), j.2⟩))
  let F := principalTupleFlatten (fun d : {d // ¬P d} => B d.val) (fun d => h d.val) (Fin 1)
  have hp : Measurable pair := by fun_prop
  have hi : Measurable (scalarOneCubeFromEndpoints
      (I := PrincipalTupleIndex (fun d : {d // ¬P d} => B d.val) (fun d => h d.val))) := by
    apply Measurable.of_eval
    intro j
    apply Measurable.of_eval
    intro i
    cases i <;> dsimp only [scalarOneCubeFromEndpoints] <;> fun_prop
  have hs : Measurable (oneCubeJointShiftScale h P lower width) := by
    apply Measurable.of_eval
    intro j
    unfold oneCubeJointShiftScale
    split <;> fun_prop
  rw [jointBooleanSource_eq_principalTuple_map, ← scalarOneCubeFromEndpoints_law,
    ← oneCubeEndpointBox_pair_law h P]
  rw [Measure.map_map hi hp, Measure.map_map F.continuous.measurable (hi.comp hp),
    Measure.map_map hs (F.continuous.measurable.comp (hi.comp hp))]
  congr 1
  funext x j
  rcases j with ⟨d, b, i, r⟩
  cases r <;> rfl

end Erdos3

end

end OAI
