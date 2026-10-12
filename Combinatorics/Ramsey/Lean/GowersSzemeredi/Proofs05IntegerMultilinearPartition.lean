import GowersSzemeredi.Proofs05IntegerMultilinearInduction

/-! Genuine integer-box Lemma 5.10. Carriers, width powers, recurrence
thresholds and diameter constants are retained exactly. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The complete one-map partition theorem on proper boxes, with the paper's
multilinear exponent and the recurrence-supported explicit threshold. -/
theorem ascending_multilinear_partition {N k m : Nat} [NeZero N]
    (P : Box N k) (hP : P.IsAscendingInteger) (mu : Point N k → ZMod N)
    (hk : 2 ≤ k) (hm : multilinearPartitionThreshold k 1 ≤ m)
    (hmP : m ≤ P.width) (hmu : MultilinearOn P.carrier mu) :
    ∃ M : Nat, ∃ Q : Fin M → Box N k,
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsAscendingInteger) ∧
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
    ascendingMultilinearHeightAt_holds k hk (2 ^ k) N Finset.univ hF hcard c P hP m hthreshold hmP
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

/-- The source's one-map multilinear partition theorem for genuine integer
boxes, with exactly the original width and diameter guarantees. -/
theorem genuine_multilinear_partition {N k m : Nat} [NeZero N]
    (P : Box N k) (hP : P.HasIntegerRepresentatives) (mu : Point N k → ZMod N)
    (hk : 2 ≤ k) (hm : multilinearPartitionThreshold k 1 ≤ m)
    (hmP : m ≤ P.width) (hmu : MultilinearOn P.carrier mu) :
    ∃ M : Nat, ∃ R : Fin M → Box N k,
      IsBoxPartition R P ∧ (∀ j, (R j).IsAscendingInteger) ∧
      ∀ j, (m : Real) ^ multilinearPartitionExponent k 1 ≤ (R j).width ∧
        diameterAtMostReal ((R j).carrier.image mu)
          (2 * (m : Real) ^ (-multilinearPartitionExponent k 1) * N) := by
  obtain ⟨d, Q, hstep, hd, hQ, hcarrier, hwidth, hcommon⟩ := hP.canonical_axes
  let C := integerAxesBox N Q d hstep
  have hC : C.IsAscendingInteger :=
    ⟨d, Q, hd, rfl, fun i => ⟨(hQ i).1, hstep i, (hQ i).2, rfl⟩⟩
  obtain ⟨M, R, hpart, hR, hbounds⟩ := ascending_multilinear_partition C hC mu hk hm
    (by rwa [hwidth]) (by rwa [hcarrier])
  refine ⟨M, R, ?_, hR, hbounds⟩
  change IsPartition (fun j => (R j).carrier) P.carrier
  rw [← hcarrier]
  exact hpart

/-- Lemma 5.10's genuine common-difference integer-box statement. -/
def lemma_5_10_integer_representatives : Prop :=
  ∀ (N k m : Nat) [NeZero N] (P : Box N k) (mu : Point N k → ZMod N),
    P.HasIntegerRepresentatives → 2 ≤ k → multilinearPartitionThreshold k 1 ≤ m →
    m ≤ P.width → MultilinearOn P.carrier mu →
      ∃ M : Nat, ∃ R : Fin M → Box N k,
        IsBoxPartition R P ∧ (∀ j, (R j).HasIntegerRepresentatives) ∧
        ∀ j, (m : Real) ^ multilinearPartitionExponent k 1 ≤ (R j).width ∧
          diameterAtMostReal ((R j).carrier.image mu)
            (2 * (m : Real) ^ (-multilinearPartitionExponent k 1) * N)

theorem lemma_5_10_integer_representatives_holds : lemma_5_10_integer_representatives := by
  intro N k m _ P mu hP hk hm hmP hmu
  obtain ⟨M, R, hpart, hR, hbounds⟩ := genuine_multilinear_partition P hP mu hk hm hmP hmu
  exact ⟨M, R, hpart, fun j => (hR j).toGenuine, hbounds⟩

end LeanProofs.GowersSzemeredi
