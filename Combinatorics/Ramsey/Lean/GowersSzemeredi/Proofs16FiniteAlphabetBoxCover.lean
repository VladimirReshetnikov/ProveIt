import GowersSzemeredi.Proofs16FiniteAlphabetMultilinear

/-! Finite-alphabet coverage bounds on boxes and their partitions.
Under the explicit balance and width conditions, no such cover can retain
half of a nonempty box. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem finiteAlphabet_box_cover_bound {N k q : Nat} [NeZero N] [Fact N.Prime]
    (P : Box N (k + 1)) (S : Finset (ZMod N)) (H : Finset (Point N (k + 1)))
    (f : ZMod N → ZMod N) (hf : ∀ y, f y ∈ S)
    (mu : Fin q → Point N (k + 1) → ZMod N) (hmu : ∀ i, IsMultilinear (mu i))
    (beta : Real) (hbeta : 0 ≤ beta)
    (hbalanced : ∀ c : ZMod N,
      (((P.axis (Fin.last k)).carrier.filter (fun y => f y = c)).card : Real) ≤
        beta * (P.axis (Fin.last k)).carrier.card)
    (hsub : H ⊆ P.carrier)
    (hcover : ∀ x ∈ H, ∃ i : Fin q, f (section16Last x) = mu i x)
    (hsmall : (q : Real) * beta ≤ 9 / 32)
    (hwidth : (q : Real) * S.card ≤ ((P.axis (Fin.last k)).carrier.card : Real) / 32) :
    (H.card : Real) ≤ (5 / 16 : Real) * P.carrier.card := by
  have he : P.carrier = lastProductSet (boxInit P).carrier (P.axis (Fin.last k)).carrier :=
    (boxInit_last_product P).1
  have hc := finiteAlphabet_multilinear_cover_five_sixteenths
    (boxInit P).carrier (P.axis (Fin.last k)).carrier S H f (fun y _ => hf y) mu hmu beta hbeta
    hbalanced (by rwa [← he]) hcover hsmall hwidth
  rw [he, lastProductSet_card]
  push_cast
  simpa only [mul_assoc] using hc

theorem finiteAlphabet_box_partition_cover_bound {N k q M : Nat} [NeZero N] [Fact N.Prime]
    (P : Box N (k + 1)) (Q : Fin M → Box N (k + 1)) (hpart : IsBoxPartition Q P)
    (S : Finset (ZMod N)) (H : Finset (Point N (k + 1)))
    (f : ZMod N → ZMod N) (hf : ∀ y, f y ∈ S)
    (mu : Fin M → Fin q → Point N (k + 1) → ZMod N) (hmu : ∀ j i, IsMultilinear (mu j i))
    (beta : Real) (hbeta : 0 ≤ beta)
    (hbalanced : ∀ j c,
      ((((Q j).axis (Fin.last k)).carrier.filter (fun y => f y = c)).card : Real) ≤
        beta * ((Q j).axis (Fin.last k)).carrier.card)
    (hsub : H ⊆ P.carrier)
    (hcover : ∀ j x, x ∈ (Q j).carrier → x ∈ H → ∃ i : Fin q, f (section16Last x) = mu j i x)
    (hsmall : (q : Real) * beta ≤ 9 / 32)
    (hwidth : ∀ j, (q : Real) * S.card ≤ (((Q j).axis (Fin.last k)).carrier.card : Real) / 32) :
    (H.card : Real) ≤ (5 / 16 : Real) * P.carrier.card := by
  classical
  have hcov : H ⊆ Finset.univ.biUnion (fun j => H ∩ (Q j).carrier) := by
    intro x hx
    obtain ⟨j, hj⟩ := (hpart.1 x).mp (hsub hx)
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_inter.mpr ⟨hx, hj⟩⟩
  have hc : (H.card : Real) ≤ ∑ j : Fin M, ((H ∩ (Q j).carrier).card : Real) := by
    exact_mod_cast (Finset.card_le_card hcov).trans Finset.card_biUnion_le
  have hcell (j : Fin M) : ((H ∩ (Q j).carrier).card : Real) ≤ (5 / 16 : Real) * (Q j).carrier.card :=
    finiteAlphabet_box_cover_bound (Q j) S (H ∩ (Q j).carrier) f hf (mu j) (hmu j) beta hbeta
      (hbalanced j) Finset.inter_subset_right
      (fun x hx => hcover j x (Finset.mem_inter.mp hx).2 (Finset.mem_inter.mp hx).1) hsmall (hwidth j)
  calc
    _ ≤ ∑ j : Fin M, ((H ∩ (Q j).carrier).card : Real) := hc
    _ ≤ ∑ j : Fin M, (5 / 16 : Real) * (Q j).carrier.card := Finset.sum_le_sum (fun j _ => hcell j)
    _ = _ := by rw [← Finset.mul_sum, ← Nat.cast_sum, hpart.sum_card]

end LeanProofs.GowersSzemeredi
