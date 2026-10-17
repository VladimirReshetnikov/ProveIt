import GowersSzemeredi.Proofs16RelativeSteps
import GowersSzemeredi.Proofs16ShortProduct

/-! # Recurrence followed by compatible final-axis tiling

Apply Lemma 16.1 to the base box alone, then retile the final axis using
short containment of the base inside a parallel parent progression. The
intermediate product need not have a common-step box presentation.

`proper_retiled_product_linearity`, `proper_retiled_product_recurrence` and
`section16_retiled_linearity_above_one` are in `Proofs16RetiledRecurrenceSide`,
outside the final route. -/
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

/-- Any common recurrence partition can be retiled along a compatible final
axis. The width scale and error are independent of the recurrence theorem. -/
theorem proper_retiled_product_of_recurrence {N k q v : Nat} [NeZero N]
    (P : Box N k) (B I : ModAP N) (i : Fin k) (u : (ZMod N)ˣ)
    (hI : I.IsProper)
    (hBstep : B.step = (↑u : ZMod N)) (hIstep : I.step = B.step)
    (hsub : (P.axis i).carrier ⊆ B.carrier) (hshort : 2 * B.length ≤ N)
    (hL : B.length ≤ I.length)
    (mu : Fin q → Point N k → ZMod N)
    (scale error : Real)
    (hrec : ∃ M : Nat, ∃ R : Fin M → Box N k,
      IsBoxPartition R P ∧ (∀ j, (R j).IsProper) ∧
      (∀ j, scale ≤ (R j).width) ∧
      ∀ a j x, x ∈ (R j).carrier →
        (centeredAbs (mu a x * (R j).commonDiff) : Real) ≤ error * N)
    (hv : 2 ≤ v)
    (hvscale : (v : Real) ^ 2 + 1 ≤ scale) :
    ∃ M : Nat, ∃ S : Fin M → Box N (k + 1), ∃ T : Fin M → Box N k,
      ∃ J : Fin M → ModAP N,
      IsPartition (fun j => (S j).carrier) (lastProductSet P.carrier I.carrier) ∧
      (∀ j, (S j).IsProper ∧ v - 1 ≤ (S j).width) ∧
      (∀ j, IsLastCoordinateBoxProduct (S j) (T j) (J j)) ∧
      (∀ j, (T j).carrier ⊆ P.carrier) ∧
      (∀ j, 0 < (J j).length ∧ (J j).length ≤ v) ∧
      ∀ a j x, x ∈ (T j).carrier →
        (centeredAbs (mu a x * (J j).step) : Real) ≤
          error * N := by
  obtain ⟨M, R, hpart, hproper, hwidth, hsmall⟩ :=
    hrec
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

end LeanProofs.GowersSzemeredi
