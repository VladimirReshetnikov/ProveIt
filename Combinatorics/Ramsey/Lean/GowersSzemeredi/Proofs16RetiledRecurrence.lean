import GowersSzemeredi.Proofs16RelativeSteps

/-! # Recurrence followed by compatible final-axis tiling

Apply Lemma 16.1 to the base box alone, then retile the final axis using
short containment of the base inside a parallel parent progression. The
intermediate product need not have a common-step box presentation.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- A finite-set product in the last-coordinate convention. -/
def lastProductSet {N k : Nat} [NeZero N] (A : Finset (Point N k))
    (I : Finset (ZMod N)) : Finset (Point N (k + 1)) :=
  Finset.univ.filter (fun x => section16Init x ∈ A ∧ section16Last x ∈ I)

/-- A partition of the base remains a partition after taking its product
with an arbitrary fixed final set. -/
theorem lastProductSet_partition {N k M : Nat} [NeZero N]
    (A : Fin M → Finset (Point N k)) (S : Finset (Point N k))
    (I : Finset (ZMod N)) (hpart : IsPartition A S) :
    IsPartition (fun j => lastProductSet (A j) I) (lastProductSet S I) := by
  classical
  constructor
  · intro x
    simp only [lastProductSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hy⟩
      obtain ⟨j, hj⟩ := (hpart.1 _).mp hx
      exact ⟨j, hj, hy⟩
    · rintro ⟨j, hj, hy⟩
      exact ⟨(hpart.1 _).mpr ⟨j, hj⟩, hy⟩
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hi hj
    exact Finset.disjoint_left.mp (hpart.2 i j hij)
      ((Finset.mem_filter.mp hi).2.1) ((Finset.mem_filter.mp hj).2.1)

/-- The base recurrence and signed tiling combine into proper product cells
with short final axes, retaining the frequency-times-step estimate. -/
theorem proper_retiled_product_recurrence {N k q m v : Nat} [NeZero N]
    (P : Box N k) (B I : ModAP N) (i : Fin k) (u : (ZMod N)ˣ)
    (hP : P.IsProper) (hI : I.IsProper)
    (hBstep : B.step = (↑u : ZMod N)) (hIstep : I.step = B.step)
    (hsub : (P.axis i).carrier ⊆ B.carrier) (hshort : 2 * B.length ≤ N)
    (hL : B.length ≤ I.length)
    (mu : Fin q → Point N k → ZMod N) (hmu : ∀ a, IsMultilinear (mu a))
    (hm : section16WidthThreshold k q ≤ m) (hmP : m ≤ P.width)
    (hv : 2 ≤ v)
    (hvscale : (v : Real) ^ 2 + 1 ≤ (m : Real) ^ section16RecurrenceExponent k q) :
    ∃ M : Nat, ∃ S : Fin M → Box N (k + 1), ∃ T : Fin M → Box N k,
      ∃ J : Fin M → ModAP N,
      IsPartition (fun j => (S j).carrier) (lastProductSet P.carrier I.carrier) ∧
      (∀ j, (S j).IsProper ∧ v - 1 ≤ (S j).width) ∧
      (∀ j, IsLastCoordinateBoxProduct (S j) (T j) (J j)) ∧
      (∀ j, (T j).carrier ⊆ P.carrier) ∧
      (∀ j, 0 < (J j).length ∧ (J j).length ≤ v) ∧
      ∀ a j x, x ∈ (T j).carrier →
        (centeredAbs (mu a x * (J j).step) : Real) ≤
          2 * (m : Real) ^ (-section16RecurrenceExponent k q) * N := by
  classical
  obtain ⟨M, R, hpart, hproper, hwidth, hsmall⟩ :=
    proper_lemma_16_1 N k q m P hP mu hm hmP hmu
  have hfit (j : Fin M) : v ^ 2 ≤ (R j).width - 1 := by
    have h := hvscale.trans (hwidth j)
    have h' : v ^ 2 + 1 ≤ (R j).width := by exact_mod_cast h
    omega
  have hnonempty (j : Fin M) : (R j).carrier.Nonempty := by
    apply Box.carrier_nonempty_of_axis_pos
    intro a
    have h := (R j).width_le_axis_length a
    have h' := hfit j
    have hv2 : 1 ≤ v ^ 2 := one_le_pow₀ (by omega)
    omega
  have hsub' (j : Fin M) : ((R j).axis i).carrier ⊆ B.carrier :=
    Finset.Subset.trans ((R j).axis_carrier_subset_of_carrier_subset P (hnonempty j)
      (IsPartition.cell_subset hpart j) i) hsub
  choose L S J hSpart hSprop hSproduct hJlength using fun j =>
    box_product_tiling_of_contained_axis (R j) B I i u (hproper j) hI hBstep hIstep
      (hsub' j) hshort hL (by omega : 1 ≤ v) (hfit j)
  let e := section5NatFlattenEquiv L
  refine ⟨∑ j, L j, boxFlatten L S, (fun j => R (e.symm j).1),
    (fun j => J (e.symm j).1 (e.symm j).2),
    finsetPartition_flatten L (fun j => lastProductSet (R j).carrier I.carrier)
      (lastProductSet P.carrier I.carrier) (fun j a => (S j a).carrier)
      (lastProductSet_partition _ _ _ hpart) hSpart, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact hSprop _ _
  · intro j
    exact hSproduct _ _
  · intro j
    exact IsPartition.cell_subset hpart _
  · intro j
    have h := hJlength (e.symm j).1 (e.symm j).2
    change 0 < (J (e.symm j).1 (e.symm j).2).length ∧
      (J (e.symm j).1 (e.symm j).2).length ≤ v
    exact ⟨h.1, by rcases h.2 with h | h <;> omega⟩
  · intro a j x hx
    have hp := hSproduct (e.symm j).1 (e.symm j).2
    rw [hp.2.2, hp.2.1]
    exact hsmall a _ x hx

/-- Frequency coverage converts the retiled base recurrence into linearity
on every final-axis cell. This allows the base and final input steps to differ. -/
theorem proper_retiled_product_linearity {N k q m v : Nat} [NeZero N]
    (P : Box N k) (B I : ModAP N) (i : Fin k) (u : (ZMod N)ˣ)
    (hP : P.IsProper) (hI : I.IsProper)
    (hBstep : B.step = (↑u : ZMod N)) (hIstep : I.step = B.step)
    (hsub : (P.axis i).carrier ⊆ B.carrier) (hshort : 2 * B.length ≤ N)
    (hL : B.length ≤ I.length)
    (mu : Fin q → Point N k → ZMod N) (hmu : ∀ a, IsMultilinear (mu a))
    (hm : section16WidthThreshold k q ≤ m) (hmP : m ≤ P.width)
    (hv : 2 ≤ v)
    (hvscale : (v : Real) ^ 2 + 1 ≤ (m : Real) ^ section16RecurrenceExponent k q)
    (K : Point N k → Finset (ZMod N)) (zeta : Real) (G : Finset (Point N k))
    (A : Point N k → Finset (ZMod N)) (f : Point N k → ZMod N → ZMod N)
    (hcover : ∀ x ∈ P.carrier, x ∈ G → ∀ r ∈ K x, ∃ a, r = mu a x)
    (hlinear : ∀ x ∈ G, ∀ J : ModAP N, J.length ≤ v → J.step ∈ bohr (K x) (zeta / v) →
      LinearOn (J.carrier ∩ A x) (f x))
    (hbudget : 2 * (m : Real) ^ (-section16RecurrenceExponent k q) ≤ zeta / v) :
    ∃ M : Nat, ∃ S : Fin M → Box N (k + 1), ∃ T : Fin M → Box N k,
      ∃ J : Fin M → ModAP N,
      IsPartition (fun j => (S j).carrier) (lastProductSet P.carrier I.carrier) ∧
      (∀ j, (S j).IsProper ∧ v - 1 ≤ (S j).width) ∧
      (∀ j, IsLastCoordinateBoxProduct (S j) (T j) (J j)) ∧
      ∀ j x, x ∈ (T j).carrier → x ∈ G → LinearOn ((J j).carrier ∩ A x) (f x) := by
  obtain ⟨M, S, T, J, hpart, hproper, hproduct, hTsub, hJlength, hsmall⟩ :=
    proper_retiled_product_recurrence P B I i u hP hI hBstep hIstep hsub hshort hL
      mu hmu hm hmP hv hvscale
  refine ⟨M, S, T, J, hpart, hproper, hproduct, ?_⟩
  intro j x hx hxG
  exact hlinear x hxG (J j) (hJlength j).2
    (product_recurrence_bohr_mem mu K x (J j).step _ zeta v
      (hcover x (hTsub j hx) hxG) (fun a => hsmall a j x hx) hbudget)

/-- At the actual Section 16 radius, a target above one automatically
supplies the recurrence threshold, the length-minus-one margin, and the
Bohr budget needed by the retiled construction. -/
theorem section16_retiled_linearity_above_one {N k q m : Nat} [NeZero N]
    (hk : 1 ≤ k) (hm : 0 < m) (theta gamma : Real)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (P : Box N k) (B I : ModAP N) (i : Fin k) (u : (ZMod N)ˣ)
    (hP : P.IsProper) (hI : I.IsProper) (hmP : m ≤ P.width)
    (hBstep : B.step = (↑u : ZMod N)) (hIstep : I.step = B.step)
    (hsub : (P.axis i).carrier ⊆ B.carrier) (hshort : 2 * B.length ≤ N)
    (hL : B.length ≤ I.length)
    (mu : Fin q → Point N k → ZMod N) (hmu : ∀ a, IsMultilinear (mu a))
    (K : Point N k → Finset (ZMod N)) (G : Finset (Point N k))
    (A : Point N k → Finset (ZMod N)) (f : Point N k → ZMod N → ZMod N)
    (hcover : ∀ x ∈ P.carrier, x ∈ G → ∀ r ∈ K x, ∃ a, r = mu a x)
    (hlinear : ∀ x ∈ G, ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
      J.step ∈ bohr (K x) (section16Zeta theta gamma k / v) →
      LinearOn (J.carrier ∩ A x) (f x))
    (hlarge : 1 < (section16Zeta theta gamma k / 2) *
      Real.sqrt ((m : Real) ^ section16RecurrenceExponent k q)) :
    ∃ M : Nat, ∃ S : Fin M → Box N (k + 1), ∃ T : Fin M → Box N k,
      ∃ J : Fin M → ModAP N,
      IsPartition (fun j => (S j).carrier) (lastProductSet P.carrier I.carrier) ∧
      (∀ j, (S j).IsProper ∧ (section16Zeta theta gamma k / 2) *
        Real.sqrt ((m : Real) ^ section16RecurrenceExponent k q) ≤ (S j).width) ∧
      (∀ j, IsLastCoordinateBoxProduct (S j) (T j) (J j)) ∧
      ∀ j x, x ∈ (T j).carrier → x ∈ G → LinearOn ((J j).carrier ∩ A x) (f x) := by
  have hmr : (0 : Real) < m := by exact_mod_cast hm
  obtain ⟨hz, hzHalf⟩ := section16Zeta_pos_le_half k ht ht1 hg hg1
  obtain ⟨v, hv, hvwidth, hvscale, hvbudget⟩ := section16_short_scale_margin
    ((m : Real) ^ section16RecurrenceExponent k q) (section16Zeta theta gamma k)
    (Real.rpow_pos_of_pos hmr _) hz hzHalf hlarge
  have hthreshold := section16_threshold_of_large_width hk hm ht ht1 hg hg1 hlarge
  have hbudget : 2 * (m : Real) ^ (-section16RecurrenceExponent k q) ≤ section16Zeta theta gamma k / v := by
    simpa only [Real.rpow_neg hmr.le, div_eq_mul_inv] using hvbudget
  obtain ⟨M, S, T, J, hpart, hproper, hproduct, hlin⟩ := proper_retiled_product_linearity
    P B I i u hP hI hBstep hIstep hsub hshort hL mu hmu hthreshold hmP hv hvscale
    K (section16Zeta theta gamma k) G A f hcover
    (fun x hx J hJ hd => hlinear x hx v (by omega) J hJ hd) hbudget
  refine ⟨M, S, T, J, hpart, ?_, hproduct, hlin⟩
  intro j
  exact ⟨(hproper j).1, hvwidth.trans (by exact_mod_cast (hproper j).2)⟩

end LeanProofs.GowersSzemeredi
