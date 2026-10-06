import GowersSzemeredi.Proofs05MultilinearInduction

/-! # One-polynomial multilinear partitioning -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The complete one-map partition theorem on proper boxes, with the paper's
multilinear exponent and the recurrence-supported explicit threshold. -/
theorem proper_multilinear_partition {N k m : Nat} [NeZero N]
    (P : Box N k) (hP : P.IsProper) (mu : Point N k → ZMod N)
    (hk : 2 ≤ k) (hm : multilinearPartitionThreshold k 1 ≤ m)
    (hmP : m ≤ P.width) (hmu : MultilinearOn P.carrier mu) :
    ∃ M : Nat, ∃ Q : Fin M → Box N k,
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
      ∀ j, (m : Real) ^ multilinearPartitionExponent k 1 ≤ (Q j).width ∧
        diameterAtMostReal ((Q j).carrier.image mu)
          (2 * (m : Real) ^ (-multilinearPartitionExponent k 1) * N) := by
  classical
  obtain ⟨psi, hpsi, heq⟩ := hmu
  obtain ⟨c, hc⟩ := (isMultilinear_iff_multiaffineEval psi).mp hpsi
  have hF : MonomialFamilyClosed (Finset.univ : Finset (Finset (Fin k))) :=
    fun _ _ _ _ => Finset.mem_univ _
  have hcard : (Finset.univ : Finset (Finset (Fin k))).card = 2 ^ k := by simp
  have hthreshold : multilinearHeightThreshold k (2 ^ k) ≤ m := by
    simpa only [multilinearHeightThreshold, multilinearPartitionThreshold, Nat.mul_one] using hm
  obtain ⟨M, Q, hpart, hproper, hwidth, hdiam⟩ :=
    multilinearHeightAt_holds k hk (2 ^ k) N Finset.univ hF hcard c P hP m hthreshold hmP
  have hexp : multilinearHeightExponent k (2 ^ k) = multilinearPartitionExponent k 1 := by
    simp only [multilinearHeightExponent, multilinearPartitionExponent, Nat.mul_one]
  have hC : multilinearHeightCoefficient k (2 ^ k) = 2 := by
    unfold multilinearHeightCoefficient
    push_cast
    field_simp
    norm_num
  refine ⟨M, Q, hpart, hproper, ?_⟩
  intro j
  refine ⟨by simpa only [hexp] using hwidth j, ?_⟩
  have himage : (Q j).carrier.image mu = (Q j).carrier.image (multiaffineEval Finset.univ c) := by
    apply Finset.image_congr
    intro x hx
    exact (heq x (IsPartition.cell_subset hpart j hx)).trans (hc x)
  rw [himage]
  simpa only [hC, hexp] using hdiam j

/-- Lemma 5.10 with geometric widths represented by proper axes. -/
theorem lemma_5_10_holds : lemma_5_10 := by
  intro N k m _ P mu hP hk hm hmP hmu
  exact proper_multilinear_partition P hP mu hk hm hmP hmu

end LeanProofs.GowersSzemeredi
