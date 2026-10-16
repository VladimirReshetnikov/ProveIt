import GowersSzemeredi.Proofs16Lemma1

/-! # Recurrence on whole product boxes

Partitioning the lifted product directly keeps the last-axis progression
at the common difference of each cell. This avoids a separate retile of an
unrefined last axis after the base box has changed its common difference.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Drop the final axis of a box. -/
def boxInit {N k : Nat} (P : Box N (k + 1)) : Box N k where
  axis i := P.axis i.castSucc
  commonDiff := P.commonDiff
  axis_step i := P.axis_step i.castSucc

theorem boxInit_isProper {N k : Nat} (P : Box N (k + 1)) (hP : P.IsProper) :
    (boxInit P).IsProper := fun i => hP i.castSucc

theorem boxInit_width {N k : Nat} (P : Box N (k + 1)) (hk : 0 < k) :
    P.width ≤ (boxInit P).width :=
  (boxInit P).le_width_of_le_axis hk (fun i => P.width_le_axis_length i.castSucc)

@[simp] theorem mem_boxInit_snoc {N k : Nat} [NeZero N]
    (P : Box N (k + 1)) (x : Point N k) (y : ZMod N) :
    Fin.snoc x y ∈ P.carrier ↔ x ∈ (boxInit P).carrier ∧ y ∈ (P.axis (Fin.last k)).carrier := by
  simp only [Box.carrier, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact ⟨fun i => by simpa only [Fin.snoc_castSucc, boxInit] using h i.castSucc,
      by simpa only [Fin.snoc_last] using h (Fin.last k)⟩
  · intro h i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using h.2
    · simpa only [Fin.snoc_castSucc, boxInit] using h.1 j

@[simp] theorem section16Init_snoc {N k : Nat} (x : Point N k) (y : ZMod N) :
    section16Init (Fin.snoc x y) = x := by
  funext i
  simp only [section16Init, Fin.snoc_castSucc]

/-- Canonical last-coordinate decomposition of a box. -/
theorem boxInit_last_product {N k : Nat} [NeZero N] (P : Box N (k + 1)) :
    IsLastCoordinateBoxProduct P (boxInit P) (P.axis (Fin.last k)) := by
  refine ⟨?_, rfl, P.axis_step (Fin.last k)⟩
  ext x
  have hx : x = Fin.snoc (Fin.init x) (x (Fin.last k)) := (Fin.snoc_init_self x).symm
  rw [hx]
  simp only [mem_boxInit_snoc, Finset.mem_filter, Finset.mem_univ, true_and,
    section16Init_snoc, section16Last, Fin.snoc_last]

/-- Multiplication by a new final coordinate preserves multilinearity. -/
theorem IsMultilinear.mul_last_coordinate {N k : Nat}
    {mu : Point N k → ZMod N} (hmu : IsMultilinear mu) :
    IsMultilinear (fun z : Point N (k + 1) => mu (Fin.init z) * z (Fin.last k)) := by
  obtain ⟨c, hc⟩ := hmu
  refine ⟨fun e => if e (Fin.last k) then c (Fin.init e) else 0, ?_⟩
  intro z
  dsimp only
  rw [hc, ← (Fin.snocEquiv (fun _ : Fin (k + 1) => Bool)).sum_comp, Fintype.sum_prod_type]
  simp [Fin.snocEquiv, Fin.prod_univ_castSucc, Fin.init, Finset.mul_sum,
    mul_comm, mul_left_comm]

end LeanProofs.GowersSzemeredi
