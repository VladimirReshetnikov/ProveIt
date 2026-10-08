import GowersSzemeredi.Proofs05MultilinearStep

/-! Simultaneous multiaffine height reduction on proper boxes.

The prescribed-step coarse partition is common to the whole coefficient
family. Each phase loses the same maximal square-free monomial, after which
a simultaneous lower-height partition is transported back and flattened.
The recurrence estimate, scale, and lower-height theorem are explicit inputs.
This supplies the geometric step for a family-size polynomial bound; that
bound and its numerical induction are not asserted here.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace LeanProofs.GowersSzemeredi
/-- One common height-reduction step for all q phases. Both rounded
child widths are admitted by the simultaneous lower-height input. -/
theorem simultaneous_multiaffine_box_height_step {N k : Nat} [NeZero N]
    (hk : 0 < k) (F : Finset (Finset (Fin k))) (hF : MonomialFamilyClosed F)
    (A : Finset (Fin k)) (hA : A ∈ F) (hmax : ∀ S ∈ F, A ⊆ S → S = A)
    (q : Nat) (c : Fin q → Finset (Fin k) → ZMod N) (P : Box N k) (hP : P.IsProper)
    (p u : Nat) (hp : 0 < p) (hu : 1 ≤ u) (hsize : p * u ^ 2 ≤ P.width)
    (W D E : Real) (hW : 0 < W)
    (hcoeff : ∀ a, (u : Real) ^ A.card *
      centeredAbs (c a A * ((p : ZMod N) * P.commonDiff) ^ A.card) ≤ E)
    (hchild : ∀ (B : Box N k), B.IsProper → u - 1 ≤ B.width → B.width ≤ u →
      ∀ c' : Fin q → Finset (Fin k) → ZMod N,
        ∃ L : Nat, ∃ R : Fin L → Box N k,
          IsBoxPartition R B ∧ (∀ j, (R j).IsProper) ∧
          (∀ j, W ≤ (R j).width) ∧
          ∀ a j, diameterAtMostReal ((R j).carrier.image (multiaffineEval (F.erase A) (c' a))) D) :
    ∃ M : Nat, ∃ Q : Fin M → Box N k,
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
      (∀ j, W ≤ (Q j).width) ∧
      ∀ a j, diameterAtMostReal ((Q j).carrier.image (multiaffineEval F (c a))) (E + D) := by
  classical
  obtain ⟨M, Q, hQpart, hQproper, hQwidth, hQlengths, hQstep⟩ :=
    section5_box_residue_partition P hP hk p u hp hu hsize
  have hQupper (i : Fin M) (j : Fin k) : ((Q i).axis j).length ≤ u := by
    rcases (hQlengths i j).2 with h | h <;> omega
  have hQwidthUpper (i : Fin M) : (Q i).width ≤ u :=
    ((Q i).width_le_axis_length ⟨0, hk⟩).trans (hQupper i ⟨0, hk⟩)
  let c' (i : Fin M) (a : Fin q) := multiaffineAffineCoeff F (c a)
    (fun j => ((Q i).axis j).start) (Q i).commonDiff
  choose L R hRpart hRproper hRwidth hRdiam using fun i =>
    hchild (boxIndexModel (Q i)) (boxIndexModel_isProper (Q i) (hQproper i))
      (by simpa using hQwidth i) (by simpa using hQwidthUpper i) (c' i)
  have hRnonempty (i : Fin M) (j : Fin (L i)) : (R i j).carrier.Nonempty := by
    apply Box.carrier_nonempty_of_axis_pos
    intro l
    have hw : 0 < (R i j).width := by exact_mod_cast hW.trans_le (hRwidth i j)
    exact hw.trans_le ((R i j).width_le_axis_length l)
  let T (i : Fin M) (j : Fin (L i)) := boxAffineTransport (Q i) (R i j)
  have hTpart (i : Fin M) : IsBoxPartition (T i) (Q i) :=
    boxAffineTransport_partition (Q i) (hQproper i) (R i) (hRpart i)
  have hTproper (i : Fin M) (j : Fin (L i)) : (T i j).IsProper :=
    boxAffineTransport_isProper (Q i) (R i j) (hQproper i) (hRproper i j)
      (hRnonempty i j) (IsPartition.cell_subset (hRpart i) j)
  let b (a : Fin q) := c a A * ((p : ZMod N) * P.commonDiff) ^ A.card
  have hlead (a : Fin q) (i : Fin M) : diameterAtMostReal
      ((boxIndexModel (Q i)).carrier.image fun x => b a * ∏ l ∈ A, x l) E := by
    refine ⟨u ^ A.card * centeredAbs (b a),
      diameterAtMost_indexModel_monomial (Q i) A (b a) (hQupper i), ?_⟩
    simpa only [Nat.cast_mul, Nat.cast_pow] using hcoeff a
  have hTdiam (a : Fin q) (i : Fin M) (j : Fin (L i)) :
      diameterAtMostReal ((T i j).carrier.image (multiaffineEval F (c a))) (E + D) := by
    have hsmall := diameterAtMostReal_mono
      (Finset.image_mono (fun x : Point N k => b a * ∏ l ∈ A, x l)
        (IsPartition.cell_subset (hRpart i) j)) (hlead a i) le_rfl
    have hsum := diameterAtMostReal_add_image (R i j).carrier
      (fun x => b a * ∏ l ∈ A, x l) (multiaffineEval (F.erase A) (c' i a))
      hsmall (hRdiam i a j)
    have himage : (T i j).carrier.image (multiaffineEval F (c a)) =
        (R i j).carrier.image (fun x => b a * ∏ l ∈ A, x l +
          multiaffineEval (F.erase A) (c' i a) x) := by
      rw [show T i j = boxAffineTransport (Q i) (R i j) from rfl,
        boxAffineTransport_carrier, Finset.image_image]
      apply Finset.image_congr
      intro x _
      change multiaffineEval F (c a) (fun l => ((Q i).axis l).start + (Q i).commonDiff * x l) = _
      rw [multiaffine_affine_height_drop F hF A hA hmax]
      change c a A * (Q i).commonDiff ^ A.card * (∏ l ∈ A, x l) +
        multiaffineEval (F.erase A) (c' i a) x = _
      rw [hQstep]
    rw [himage]
    exact hsum
  refine ⟨∑ i, L i, boxFlatten L T, boxFlatten_partition P Q L T hQpart hTpart, ?_, ?_, ?_⟩
  · intro j
    let z := (section5NatFlattenEquiv L).symm j
    exact hTproper z.1 z.2
  · intro j
    let z := (section5NatFlattenEquiv L).symm j
    exact hRwidth z.1 z.2
  · intro a j
    let z := (section5NatFlattenEquiv L).symm j
    exact hTdiam a z.1 z.2

end LeanProofs.GowersSzemeredi
