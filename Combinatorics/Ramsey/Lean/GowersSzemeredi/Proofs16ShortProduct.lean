import GowersSzemeredi.Proofs16ProductRecurrence

/-! # Short proper cells retaining the lifted product recurrence -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Projecting a nonempty final axis preserves box containment. -/
theorem boxInit_carrier_subset {N k : Nat} [NeZero N]
    (P Q : Box N (k + 1)) (hsub : P.carrier ⊆ Q.carrier)
    (hpos : 0 < (P.axis (Fin.last k)).length) :
    (boxInit P).carrier ⊆ (boxInit Q).carrier := by
  classical
  intro x hx
  have hy : (P.axis (Fin.last k)).start ∈ (P.axis (Fin.last k)).carrier := by
    refine Finset.mem_image.mpr ⟨⟨0, hpos⟩, Finset.mem_univ _, ?_⟩
    simp
  exact ((mem_boxInit_snoc Q _ _).mp (hsub ((mem_boxInit_snoc P _ _).mpr ⟨hx, hy⟩))).1

/-- Refine the whole lifted product into short cells of the same controlled
common difference. Formal lengths remain cardinalities throughout. -/
theorem proper_short_product_recurrence {N k q m v : Nat} [NeZero N]
    (hk : 1 ≤ k) (P : Box N (k + 1)) (hP : P.IsProper)
    (mu : Fin q → Point N k → ZMod N) (hmu : ∀ i, IsMultilinear (mu i))
    (hm : section16WidthThreshold k q ≤ m) (hmP : m ≤ P.width)
    (hv : 2 ≤ v) (hvscale : (v : Real) ^ 2 ≤ (m : Real) ^ section16RecurrenceExponent k q) :
    ∃ M : Nat, ∃ Q : Fin M → Box N (k + 1),
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
      (∀ j, v - 1 ≤ (Q j).width) ∧
      (∀ j i, 0 < ((Q j).axis i).length ∧ ((Q j).axis i).length ≤ v) ∧
      ∀ i j x, x ∈ (boxInit (Q j)).carrier →
        (centeredAbs (mu i x * (Q j).commonDiff) : Real) ≤
          2 * (m : Real) ^ (-section16RecurrenceExponent k q) * N := by
  classical
  obtain ⟨M, R, hRpart, hRproper, hRwidth, hRsmall⟩ :=
    proper_product_multilinear_recurrence hk P hP mu hmu hm hmP
  have hsize (j : Fin M) : 1 * v ^ 2 ≤ (R j).width := by
    have := hvscale.trans (hRwidth j)
    simp only [one_mul]
    exact_mod_cast this
  choose L S hSpart hSproper hSwidth hSaxes hSstep using fun j : Fin M =>
    section5_box_residue_partition (R j) (hRproper j) (by omega) 1 v (by norm_num) (by omega) (hsize j)
  refine ⟨∑ j, L j, boxFlatten L S, boxFlatten_partition P R L S hRpart hSpart, ?_, ?_, ?_, ?_⟩
  · intro j
    exact hSproper _ _
  · intro j
    exact hSwidth _ _
  · intro j i
    dsimp only [boxFlatten]
    have h := hSaxes ((section5NatFlattenEquiv L).symm j).1 ((section5NatFlattenEquiv L).symm j).2 i
    exact ⟨h.1, by rcases h.2 with h | h <;> omega⟩
  · intro i j x hx
    let z := (section5NatFlattenEquiv L).symm j
    have hsub : (boxInit (S z.1 z.2)).carrier ⊆ (boxInit (R z.1)).carrier :=
      boxInit_carrier_subset _ _ (IsPartition.cell_subset (hSpart z.1) z.2)
        (hSaxes z.1 z.2 (Fin.last k)).1
    have hstep : (S z.1 z.2).commonDiff = (R z.1).commonDiff := by simpa using hSstep z.1 z.2
    change (centeredAbs (mu i x * (S z.1 z.2).commonDiff) : Real) ≤ _
    rw [hstep]
    exact hRsmall i z.1 x (hsub hx)

/-- A finite multilinear cover of the frequencies gives a common-difference
Bohr element on every selected base point. -/
theorem product_recurrence_bohr_mem {N k q : Nat} [NeZero N]
    (mu : Fin q → Point N k → ZMod N) (K : Point N k → Finset (ZMod N))
    (x : Point N k) (d : ZMod N) (e zeta : Real) (v : Nat)
    (hcover : ∀ r ∈ K x, ∃ i, r = mu i x)
    (hsmall : ∀ i, (centeredAbs (mu i x * d) : Real) ≤ e * N)
    (hbudget : e ≤ zeta / v) : d ∈ bohr (K x) (zeta / v) := by
  classical
  simp only [bohr, Finset.mem_filter, Finset.mem_univ, true_and]
  intro r hr
  obtain ⟨i, rfl⟩ := hcover r hr
  exact (hsmall i).trans (mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg N))

/-- The recurrence partition yields linearity on the final-axis cells when
their frequency cover and the short-progression input are available. -/
theorem proper_short_product_linearity {N k q m v : Nat} [NeZero N]
    (hk : 1 ≤ k) (P : Box N (k + 1)) (hP : P.IsProper)
    (mu : Fin q → Point N k → ZMod N) (hmu : ∀ i, IsMultilinear (mu i))
    (hm : section16WidthThreshold k q ≤ m) (hmP : m ≤ P.width)
    (hv : 2 ≤ v) (hvscale : (v : Real) ^ 2 ≤ (m : Real) ^ section16RecurrenceExponent k q)
    (K : Point N k → Finset (ZMod N)) (zeta : Real) (G : Finset (Point N k))
    (A : Point N k → Finset (ZMod N)) (f : Point N k → ZMod N → ZMod N)
    (hcover : ∀ x ∈ (boxInit P).carrier, x ∈ G → ∀ r ∈ K x, ∃ i, r = mu i x)
    (hlinear : ∀ x ∈ G, ∀ I : ModAP N, I.length ≤ v → I.step ∈ bohr (K x) (zeta / v) →
      LinearOn (I.carrier ∩ A x) (f x))
    (hbudget : 2 * (m : Real) ^ (-section16RecurrenceExponent k q) ≤ zeta / v) :
    ∃ M : Nat, ∃ Q : Fin M → Box N (k + 1),
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
      (∀ j, v - 1 ≤ (Q j).width) ∧
      ∀ j x, x ∈ (boxInit (Q j)).carrier → x ∈ G →
        LinearOn (((Q j).axis (Fin.last k)).carrier.filter fun y => y ∈ A x) (f x) := by
  classical
  obtain ⟨M, Q, hpart, hproper, hwidth, haxes, hsmall⟩ :=
    proper_short_product_recurrence hk P hP mu hmu hm hmP hv hvscale
  refine ⟨M, Q, hpart, hproper, hwidth, ?_⟩
  intro j x hx hxG
  have hxP := boxInit_carrier_subset (Q j) P (IsPartition.cell_subset hpart j)
    (haxes j (Fin.last k)).1 hx
  have hd := product_recurrence_bohr_mem mu K x (Q j).commonDiff _ zeta v
    (hcover x hxP hxG) (fun i => hsmall i j x hx) hbudget
  have hl := hlinear x hxG ((Q j).axis (Fin.last k)) (haxes j (Fin.last k)).2
    (by simpa only [(Q j).axis_step] using hd)
  simpa only [Finset.filter_mem_eq_inter] using hl

end LeanProofs.GowersSzemeredi
