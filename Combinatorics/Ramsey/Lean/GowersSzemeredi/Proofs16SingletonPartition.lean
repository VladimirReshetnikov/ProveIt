import GowersSzemeredi.Proofs16RecurrenceThreshold

/-! # The singleton branch of the Section 16 local partition construction -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A genuine length-one box at a point, with no inflated formal lengths. -/
def pointSingletonBox {N d : Nat} (x : Point N d) : Box N d where
  axis i := { start := x i, step := 1, length := 1 }
  commonDiff := 1
  axis_step _ := rfl

@[simp] theorem pointSingletonBox_axis_carrier {N d : Nat} (x : Point N d) (i : Fin d) :
    ((pointSingletonBox x).axis i).carrier = {x i} := by
  classical
  simp [pointSingletonBox, ModAP.carrier]

@[simp] theorem pointSingletonBox_carrier {N d : Nat} [NeZero N] (x : Point N d) :
    (pointSingletonBox x).carrier = {x} := by
  classical
  ext y
  simp only [Box.carrier, Finset.mem_filter, Finset.mem_univ, true_and,
    pointSingletonBox_axis_carrier, Finset.mem_singleton]
  exact ⟨fun h => funext h, fun h i => congrFun h i⟩

theorem pointSingletonBox_isProper {N d : Nat} (x : Point N d) :
    (pointSingletonBox x).IsProper := by
  classical
  intro i
  change ((pointSingletonBox x).axis i).carrier.card = 1
  rw [pointSingletonBox_axis_carrier]
  simp

@[simp] theorem pointSingletonBox_width {N d : Nat} (hd : 0 < d) (x : Point N d) :
    (pointSingletonBox x).width = 1 := by
  apply le_antisymm
  · exact (pointSingletonBox x).width_le_axis_length ⟨0, hd⟩
  · exact (pointSingletonBox x).le_width_of_le_axis hd (fun _ => le_rfl)

/-- Partition any box into its points, retaining actual width one in
positive dimension and allowing the empty partition for the empty box. -/
theorem box_singleton_partition {N d : Nat} [NeZero N] (P : Box N d) :
    ∃ M : Nat, ∃ x : Fin M → Point N d,
      IsBoxPartition (fun j => pointSingletonBox (x j)) P := by
  classical
  let e := Fintype.equivFin {x // x ∈ P.carrier}
  refine ⟨Fintype.card {x // x ∈ P.carrier}, fun j => (e.symm j).val, ?_⟩
  constructor
  · intro x
    simp only [pointSingletonBox_carrier, Finset.mem_singleton]
    constructor
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp⟩
    · rintro ⟨j, rfl⟩
      exact (e.symm j).property
  · intro i j hij
    simp only [pointSingletonBox_carrier, Finset.disjoint_singleton]
    intro h
    exact (bne_iff_ne.mp hij) (e.symm.injective (Subtype.ext h))

/-- Every map is affine when restricted to a subset of a singleton. -/
theorem LinearOn.of_subset_singleton {N : Nat} (A : Finset (ZMod N))
    (f : ZMod N → ZMod N) (y : ZMod N) (hA : A ⊆ {y}) : LinearOn A f := by
  refine ⟨0, f y, ?_⟩
  intro x hx
  have hxy : x = y := Finset.mem_singleton.mp (hA hx)
  simp [hxy]

/-- Width targets at most one need no frequency or Bohr hypotheses. -/
theorem section16_local_linearity_singletons {N k : Nat} [NeZero N]
    (P : Box N (k + 1)) (l : Real) (hl : l ≤ 1)
    (A : Point N k → Finset (ZMod N)) (f : Point N k → ZMod N → ZMod N) :
    ∃ M : Nat, ∃ Q : Fin M → Box N (k + 1),
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
      (∀ j, l ≤ (Q j).width) ∧
      ∀ j x, LinearOn (((Q j).axis (Fin.last k)).carrier.filter fun y => y ∈ A x) (f x) := by
  classical
  obtain ⟨M, x, hpart⟩ := box_singleton_partition P
  refine ⟨M, fun j => pointSingletonBox (x j), hpart,
    fun j => pointSingletonBox_isProper _, ?_, ?_⟩
  · intro j
    simpa only [pointSingletonBox_width (by omega : 0 < k + 1), Nat.cast_one] using hl
  · intro j z
    apply LinearOn.of_subset_singleton _ _ ((x j) (Fin.last k))
    intro y hy
    simpa only [pointSingletonBox_axis_carrier] using (Finset.mem_filter.mp hy).1

/-- The local product result holds at every scale in positive base
dimension, using singletons when the requested width is at most one. -/
theorem section16_local_linearity {N k q m : Nat} [NeZero N]
    (hk : 1 ≤ k) (theta gamma : Real)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (P : Box N (k + 1)) (hP : P.IsProper) (hmP : m ≤ P.width)
    (mu : Fin q → Point N k → ZMod N) (hmu : ∀ i, IsMultilinear (mu i))
    (K : Point N k → Finset (ZMod N)) (G : Finset (Point N k))
    (A : Point N k → Finset (ZMod N)) (f : Point N k → ZMod N → ZMod N)
    (hcover : ∀ x ∈ (boxInit P).carrier, x ∈ G → ∀ r ∈ K x, ∃ i, r = mu i x)
    (hlinear : ∀ x ∈ G, ∀ v : Nat, 0 < v → ∀ I : ModAP N, I.length ≤ v →
      I.step ∈ bohr (K x) (section16Zeta theta gamma k / v) →
      LinearOn (I.carrier ∩ A x) (f x)) :
    ∃ M : Nat, ∃ Q : Fin M → Box N (k + 1),
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
      (∀ j, (section16Zeta theta gamma k / 2) *
        Real.sqrt ((m : Real) ^ section16RecurrenceExponent k q) ≤ (Q j).width) ∧
      ∀ j x, x ∈ (boxInit (Q j)).carrier → x ∈ G →
        LinearOn (((Q j).axis (Fin.last k)).carrier.filter fun y => y ∈ A x) (f x) := by
  classical
  by_cases hl : (section16Zeta theta gamma k / 2) *
      Real.sqrt ((m : Real) ^ section16RecurrenceExponent k q) ≤ 1
  · obtain ⟨M, Q, hpart, hproper, hwidth, hlin⟩ := section16_local_linearity_singletons P _ hl A f
    exact ⟨M, Q, hpart, hproper, hwidth, fun j x _ _ => hlin j x⟩
  · have hm : 0 < m := by
      by_contra hm
      have hm0 : m = 0 := by omega
      have he : 0 < section16RecurrenceExponent k q := by
        rw [section16RecurrenceExponent_eq_multilinear]
        have hK := multilinearPartitionConstant_eight_le (by omega : 2 ≤ k + 1)
        unfold multilinearPartitionExponent
        positivity
      subst m
      simp [Real.zero_rpow he.ne'] at hl
    exact section16_local_linearity_above_one hk hm theta gamma ht ht1 hg hg1 P hP hmP
      mu hmu K G A f hcover hlinear (lt_of_not_ge hl)

end LeanProofs.GowersSzemeredi
