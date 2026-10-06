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
  classical
  obtain ⟨c, hc⟩ := hmu
  refine ⟨fun e => if e (Fin.last k) then c (Fin.init e) else 0, ?_⟩
  intro z
  dsimp only
  rw [hc]
  rw [← (Fin.snocEquiv (fun _ : Fin (k + 1) => Bool)).sum_comp, Fintype.sum_prod_type]
  simp [Fin.snocEquiv, Fin.prod_univ_castSucc, Fin.init, Finset.mul_sum,
    mul_comm, mul_left_comm]

/-- A lifted image diameter controls multiplication by the final-axis step. -/
theorem lifted_last_diameter_commonDiff {N k : Nat} [NeZero N]
    (P : Box N (k + 1)) (mu : Point N k → ZMod N) (s : Real)
    (hdiam : diameterAtMostReal
      (P.carrier.image (fun z => mu (Fin.init z) * z (Fin.last k))) s)
    (hwidth : 2 ≤ P.width) (x : Point N k) (hx : x ∈ (boxInit P).carrier) :
    (centeredAbs (mu x * P.commonDiff) : Real) ≤ s := by
  classical
  let I := P.axis (Fin.last k)
  have hI : 2 ≤ I.length := hwidth.trans (P.width_le_axis_length (Fin.last k))
  have hy : I.start ∈ I.carrier := by
    refine Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
    simp
  have hmem (y : ZMod N) (hy : y ∈ I.carrier) :
      mu x * y ∈ P.carrier.image (fun z => mu (Fin.init z) * z (Fin.last k)) := by
    refine Finset.mem_image.mpr ⟨Fin.snoc x y, (mem_boxInit_snoc _ _ _).mpr ⟨hx, hy⟩, ?_⟩
    simp
  obtain hnext | hprev := I.adjacent_mem hI hy
  · have h := hdiam.centeredAbs_sub_le (hmem _ hnext) (hmem _ hy)
    have heq : mu x * (I.start + I.step) - mu x * I.start = mu x * P.commonDiff := by
      change mu x * (I.start + (P.axis (Fin.last k)).step) - mu x * I.start = _
      rw [P.axis_step]
      ring
    rwa [heq] at h
  · have h := hdiam.centeredAbs_sub_le (hmem _ hy) (hmem _ hprev)
    have heq : mu x * I.start - mu x * (I.start - I.step) = mu x * P.commonDiff := by
      change mu x * I.start - mu x * (I.start - (P.axis (Fin.last k)).step) = _
      rw [P.axis_step]
      ring
    rwa [heq] at h

/-- The product-box strengthening of Lemma 16.1, with exactly its exponent
and threshold. Every cell keeps its own last-axis progression at the
common difference controlled by the recurrence estimate. -/
theorem proper_product_multilinear_recurrence {N k q m : Nat} [NeZero N]
    (hk : 1 ≤ k) (P : Box N (k + 1)) (hP : P.IsProper)
    (mu : Fin q → Point N k → ZMod N) (hmu : ∀ i, IsMultilinear (mu i))
    (hm : section16WidthThreshold k q ≤ m) (hmP : m ≤ P.width) :
    ∃ M : Nat, ∃ Q : Fin M → Box N (k + 1),
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
      (∀ j, (m : Real) ^ section16RecurrenceExponent k q ≤ (Q j).width) ∧
      ∀ i j x, x ∈ (boxInit (Q j)).carrier →
        (centeredAbs (mu i x * (Q j).commonDiff) : Real) ≤
          2 * (m : Real) ^ (-section16RecurrenceExponent k q) * N := by
  let nu (i : Fin q) (z : Point N (k + 1)) := mu i (Fin.init z) * z (Fin.last k)
  have hnu : ∀ i, MultilinearOn P.carrier (nu i) :=
    fun i => ⟨nu i, (hmu i).mul_last_coordinate, fun _ _ => rfl⟩
  rw [section16WidthThreshold_eq_multilinear] at hm
  obtain ⟨M, Q, hpart, hproper, hwidth, hdiam⟩ :=
    proper_multilinear_simultaneous (k + 1) (by omega) q N m P hP nu hm hmP hnu
  refine ⟨M, Q, hpart, hproper, ?_, ?_⟩
  · simpa only [section16RecurrenceExponent_eq_multilinear] using hwidth
  · intro i j x hx
    rw [section16RecurrenceExponent_eq_multilinear]
    have hw : 2 ≤ (Q j).width := by
      exact_mod_cast (multilinearPartition_root_two_le (by omega : 2 ≤ k + 1) hm).trans (hwidth j)
    exact lifted_last_diameter_commonDiff (Q j) (mu i) _ (hdiam i j) hw x hx

end LeanProofs.GowersSzemeredi
