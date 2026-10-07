import OAI.Combinatorics.Progressions.Lattices.BoundedPrimeResidual

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem physical_cell_residual_energy {X A ι σ : Type*}
    [Fintype X] [Nonempty X] [Fintype A] [DecidableEq A]
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (C : X → A) (c : A) (e : X → ℝ)
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (b : ℕ) (f : (σ → ℤ) → ℝ) (eta : ℝ)
    (hcontrol : ResiduePhysicalTruncationControl lo N M a hne q b f eta)
    (E : {x // C x = c} ≃ IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a)
    (he : ∀ x : {x // C x = c}, e x.val =
      f (fun k => (E x k).val) - residuePhysicalTruncation lo N M a hne q b f (fun k => (E x k).val)) :
    finiteCellMean (FiniteProbabilityWeights.uniform X) C (fun x => e x ^ 2) c ≤
      (1 + eta * residueTruncationCap ι b eta ^ 2) * (finiteCellWeights (FiniteProbabilityWeights.uniform X) C).weight c := by
  have hmean := Fintype.expect_equiv E (fun x => e x.val ^ 2)
    (fun z => (f (fun k => (z k).val) - residuePhysicalTruncation lo N M a hne q b f
      (fun k => (z k).val)) ^ 2) (fun x => by rw [he x])
  rw [finiteCellMean_uniform_weighted, hmean]
  exact (mul_le_mul_of_nonneg_left hcontrol.2.1
    ((finiteCellWeights (FiniteProbabilityWeights.uniform X) C).nonneg c)).trans_eq (mul_comm _ _)

theorem physical_cell_residual_residue {X A ι σ : Type*}
    [Fintype X] [Nonempty X] [Fintype A] [DecidableEq A]
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (C : X → A) (c : A) (e : X → ℝ)
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (b : ℕ) (f : (σ → ℤ) → ℝ) (eta : ℝ)
    (hcontrol : ResiduePhysicalTruncationControl lo N M a hne q b f eta)
    (E : {x // C x = c} ≃ IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a)
    (he : ∀ x : {x // C x = c}, e x.val =
      f (fun k => (E x k).val) - residuePhysicalTruncation lo N M a hne q b f (fun k => (E x k).val))
    (J : Finset ι) (hJ : J.card ≤ b) (m : ℕ) [NeZero m] (hm : m ∣ ∏ i ∈ J, q i)
    (F : X → σ → ZMod m) (hF : ∀ x : {x // C x = c},
      F x.val = integerVectorResidue m (fun k => (E x k).val)) (r : σ → ZMod m) :
    |finiteCellResidueMean (FiniteProbabilityWeights.uniform X) C F e c r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform X) C).weight c *
        (eta * residueTruncationCap ι b eta / Fintype.card (σ → ZMod m)) := by
  classical
  apply uniform_cell_residue_bound
  have hmean := Fintype.expect_equiv E (fun x => if F x.val = r then e x.val else 0)
    (fun z => (f (fun k => (z k).val) - residuePhysicalTruncation lo N M a hne q b f
      (fun k => (z k).val)) * (if (fun k => ((z k).val : ZMod m)) = r then (1 : ℝ) else 0))
    (fun x => by
      rw [he x, hF x]
      change (if (fun k => ((E x k).val : ZMod m)) = r then _ else 0) = _
      split_ifs <;> simp)
  rw [hmean]
  have h := residuePhysicalTruncation_modulus_error lo N M a hne q hpair hcontrol J hJ m hm r
  simpa only [integerVectorResidue_card, Nat.cast_pow, div_eq_mul_inv] using h

end Erdos3

end

end OAI
