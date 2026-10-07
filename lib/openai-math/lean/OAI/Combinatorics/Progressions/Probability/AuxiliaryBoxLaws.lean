import OAI.Combinatorics.Progressions.Geometry.AuxiliaryBoxPartition

namespace OAI

section

namespace Erdos3

theorem refinedResidue_implies_base (M J : ℕ) (u w : ℤ)
    (hw : w ≡ u [ZMOD (M : ℤ)]) (x : ℤ) (hx : x ≡ w [ZMOD (M * J : ℕ)]) :
    x ≡ u [ZMOD (M : ℤ)] :=
  (Int.ModEq.of_dvd (by exact_mod_cast dvd_mul_right M J) hx).trans hw

noncomputable def baseAuxiliaryBoxCell {I : Type*} (a : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (M d : I → ℕ) (hd : ∀ i, 0 < d i)
    (u : I → ℤ) :
    IntegerResidueBox a (fun i => a i + N i) (fun i => (M i : ℤ)) u → AuxiliaryBoxLabels P M d u :=
  boxAuxiliaryCell a N P M d hd u (fun i => (M i : ℤ)) u (fun _ _ hx => hx)

noncomputable def refinedAuxiliaryBoxCell {I : Type*} (a : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (M d J : I → ℕ) (hd : ∀ i, 0 < d i)
    (u w : I → ℤ) (hw : ∀ i, w i ≡ u i [ZMOD (M i : ℤ)]) :
    IntegerResidueBox a (fun i => a i + N i) (fun i => (M i * J i : ℕ)) w → AuxiliaryBoxLabels P M d u :=
  boxAuxiliaryCell a N P M d hd u (fun i => (M i * J i : ℕ)) w
    (fun i => refinedResidue_implies_base (M i) (J i) (u i) (w i) (hw i))

theorem auxiliaryBoxLabels_nonempty {I : Type*} {N : I → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i)) (hP : Nonempty (∀ i, (P i).Label))
    (M d : I → ℕ) (hd : ∀ i, 0 < d i) (u : I → ℤ) :
    Nonempty (AuxiliaryBoxLabels P M d u) := by
  obtain ⟨k⟩ := hP
  exact ⟨fun i => (k i, compatibleAuxResidueOfPoint (M i) (d i) (hd i)
    (u i) (u i) (Int.ModEq.refl (u i)))⟩

theorem baseAuxiliaryBoxCell_card {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (P i).step k = 1) (hpos : ∀ i k, 0 < (P i).length k)
    (M d : I → ℕ) (hd : ∀ i, 0 < d i) (u : I → ℤ) (k : AuxiliaryBoxLabels P M d u) :
    (partitionCell (baseAuxiliaryBoxCell a N P M d hd u) k).card =
      rectangularResidueCount (fun i => intervalCellLower (a i) (P i) (k i).1)
        (fun i => intervalCellUpper (a i) (P i) (k i).1)
        (fun i => (Nat.lcm (M i) (d i) : ℤ)) (fun i => (k i).2.baseValue) :=
  boxAuxiliaryCell_card a N P hstep hpos M d hd u (fun i => (M i : ℤ)) u
    (fun _ _ hx => hx) k (fun i => (Nat.lcm (M i) (d i) : ℤ)) (fun i => (k i).2.baseValue)
    (fun i => (k i).2.baseConstraint_iff)

theorem refinedAuxiliaryBoxCell_card {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (P i).step k = 1) (hpos : ∀ i k, 0 < (P i).length k)
    (M d J : I → ℕ) (hd : ∀ i, 0 < d i) (u w : I → ℤ)
    (hw : ∀ i, w i ≡ u i [ZMOD (M i : ℤ)]) (hcop : ∀ i, (M i * d i).Coprime (J i))
    (k : AuxiliaryBoxLabels P M d u) :
    (partitionCell (refinedAuxiliaryBoxCell a N P M d J hd u w hw) k).card =
      rectangularResidueCount (fun i => intervalCellLower (a i) (P i) (k i).1)
        (fun i => intervalCellUpper (a i) (P i) (k i).1)
        (fun i => (Nat.lcm (M i) (d i) * J i : ℕ))
        (fun i => (k i).2.refinedValue (hcop i) (w i)) :=
  boxAuxiliaryCell_card a N P hstep hpos M d hd u (fun i => (M i * J i : ℕ)) w
    (fun i => refinedResidue_implies_base (M i) (J i) (u i) (w i) (hw i)) k
    (fun i => (Nat.lcm (M i) (d i) * J i : ℕ)) (fun i => (k i).2.refinedValue (hcop i) (w i))
    (fun i => (k i).2.refinedConstraint_iff (hcop i) (w i) (hw i))

end Erdos3

end

end OAI
