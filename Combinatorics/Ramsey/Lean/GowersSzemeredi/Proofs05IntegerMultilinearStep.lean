import GowersSzemeredi.Proofs16IntegerResiduePartition
import GowersSzemeredi.Proofs05MultilinearBudgets

/-! Height reduction with ascending integer-axis certificates. The original
width, diameter, rounding and recurrence budgets are retained exactly. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace LeanProofs.GowersSzemeredi

/-- One complete height-reduction step, before specializing the numerical
budgets. Both rounded child widths are admitted by the lower-height input. -/
theorem multiaffine_integer_box_height_step {N k : Nat} [NeZero N]
    (hk : 0 < k) (F : Finset (Finset (Fin k))) (hF : MonomialFamilyClosed F)
    (A : Finset (Fin k)) (hA : A ∈ F) (hmax : ∀ S ∈ F, A ⊆ S → S = A)
    (c : Finset (Fin k) → ZMod N) (P : Box N k) (hP : P.IsAscendingInteger)
    (p u : Nat) (hp : 0 < p) (hu : 1 ≤ u) (hsize : p * u ^ 2 ≤ P.width)
    (W D E : Real) (hW : 0 < W)
    (hcoeff : (u : Real) ^ A.card *
      centeredAbs (c A * ((p : ZMod N) * P.commonDiff) ^ A.card) ≤ E)
    (hchild : ∀ (B : Box N k), B.IsAscendingInteger → u - 1 ≤ B.width → B.width ≤ u →
      ∀ c' : Finset (Fin k) → ZMod N,
        ∃ L : Nat, ∃ R : Fin L → Box N k,
          IsBoxPartition R B ∧ (∀ j, (R j).IsAscendingInteger) ∧
          (∀ j, W ≤ (R j).width) ∧
          ∀ j, diameterAtMostReal ((R j).carrier.image (multiaffineEval (F.erase A) c')) D) :
    ∃ M : Nat, ∃ Q : Fin M → Box N k,
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsAscendingInteger) ∧
      (∀ j, W ≤ (Q j).width) ∧
      ∀ j, diameterAtMostReal ((Q j).carrier.image (multiaffineEval F c)) (E + D) := by
  classical
  obtain ⟨M, Q, hQpart, hQascending, hQwidth, hQlengths, hQstep⟩ :=
    P.ascending_residue_partition hP hk p u hp hu hsize
  have hQproper (i : Fin M) : (Q i).IsProper := (hQascending i).isProper
  have hQupper (i : Fin M) (j : Fin k) : ((Q i).axis j).length ≤ u := by
    rcases (hQlengths i j).2 with h | h <;> omega
  have hQwidthUpper (i : Fin M) : (Q i).width ≤ u :=
    ((Q i).width_le_axis_length ⟨0, hk⟩).trans (hQupper i ⟨0, hk⟩)
  let c' (i : Fin M) := multiaffineAffineCoeff F c
    (fun j => ((Q i).axis j).start) (Q i).commonDiff
  choose L R hRpart hRascending hRwidth hRdiam using fun i =>
    hchild (boxIndexModel (Q i)) (boxIndexModel_isAscendingInteger (Q i) (hQproper i))
      (by simpa using hQwidth i) (by simpa using hQwidthUpper i) (c' i)
  have hRnonempty (i : Fin M) (j : Fin (L i)) : (R i j).carrier.Nonempty := by
    apply Box.carrier_nonempty_of_axis_pos
    intro l
    have hw : 0 < (R i j).width := by exact_mod_cast hW.trans_le (hRwidth i j)
    exact hw.trans_le ((R i j).width_le_axis_length l)
  let T (i : Fin M) (j : Fin (L i)) := boxAffineTransport (Q i) (R i j)
  have hTpart (i : Fin M) : IsBoxPartition (T i) (Q i) :=
    boxAffineTransport_partition (Q i) (hQproper i) (R i) (hRpart i)
  have hTascending (i : Fin M) (j : Fin (L i)) : (T i j).IsAscendingInteger :=
    boxAffineTransport_isAscendingInteger (Q i) (R i j) (hQascending i) (hRascending i j)
      (hRnonempty i j) (IsPartition.cell_subset (hRpart i) j)
  let b := c A * ((p : ZMod N) * P.commonDiff) ^ A.card
  have hlead (i : Fin M) : diameterAtMostReal
      ((boxIndexModel (Q i)).carrier.image fun x => b * ∏ l ∈ A, x l) E := by
    refine ⟨u ^ A.card * centeredAbs b,
      diameterAtMost_indexModel_monomial (Q i) A b (hQupper i), ?_⟩
    simpa only [Nat.cast_mul, Nat.cast_pow] using hcoeff
  have hTdiam (i : Fin M) (j : Fin (L i)) :
      diameterAtMostReal ((T i j).carrier.image (multiaffineEval F c)) (E + D) := by
    have hsmall := diameterAtMostReal_mono
      (Finset.image_mono (fun x : Point N k => b * ∏ l ∈ A, x l)
        (IsPartition.cell_subset (hRpart i) j)) (hlead i) le_rfl
    have hsum := diameterAtMostReal_add_image (R i j).carrier
      (fun x => b * ∏ l ∈ A, x l) (multiaffineEval (F.erase A) (c' i))
      hsmall (hRdiam i j)
    have himage : (T i j).carrier.image (multiaffineEval F c) =
        (R i j).carrier.image (fun x => b * ∏ l ∈ A, x l +
          multiaffineEval (F.erase A) (c' i) x) := by
      rw [show T i j = boxAffineTransport (Q i) (R i j) from rfl,
        boxAffineTransport_carrier, Finset.image_image]
      apply Finset.image_congr
      intro x _
      change multiaffineEval F c (fun l => ((Q i).axis l).start + (Q i).commonDiff * x l) = _
      rw [multiaffine_affine_height_drop F hF A hA hmax]
      change c A * (Q i).commonDiff ^ A.card * (∏ l ∈ A, x l) +
        multiaffineEval (F.erase A) (c' i) x = _
      rw [hQstep]
    rw [himage]
    exact hsum
  refine ⟨∑ i, L i, boxFlatten L T, boxFlatten_partition P Q L T hQpart hTpart, ?_, ?_, ?_⟩
  · intro j
    let z := (section5NatFlattenEquiv L).symm j
    exact hTascending z.1 z.2
  · intro j
    let z := (section5NatFlattenEquiv L).symm j
    exact hRwidth z.1 z.2
  · intro j
    let z := (section5NatFlattenEquiv L).symm j
    exact hTdiam z.1 z.2

end LeanProofs.GowersSzemeredi
