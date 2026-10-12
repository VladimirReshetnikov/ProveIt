import GowersSzemeredi.Proofs05IntegerMultilinearPartition
import GowersSzemeredi.Proofs05MultilinearIteration

/-! Genuine integer-box simultaneous multilinear partitioning. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Simultaneous partitioning, including an empty function family as the
induction base. All refinements remain proper. -/
theorem ascending_multilinear_simultaneous (k : Nat) (hk : 2 ≤ k) (q : Nat) :
    ∀ (N m : Nat) [NeZero N] (P : Box N k), P.IsAscendingInteger →
      ∀ mu : Fin q → Point N k → ZMod N,
        multilinearPartitionThreshold k q ≤ m → m ≤ P.width →
        (∀ i, MultilinearOn P.carrier (mu i)) →
        ∃ M : Nat, ∃ Q : Fin M → Box N k,
          IsBoxPartition Q P ∧ (∀ j, (Q j).IsAscendingInteger) ∧
          (∀ j, (m : Real) ^ multilinearPartitionExponent k q ≤ (Q j).width) ∧
          ∀ i j, diameterAtMostReal ((Q j).carrier.image (mu i))
            (2 * (m : Real) ^ (-multilinearPartitionExponent k q) * N) := by
  induction q with
  | zero =>
    intro N m _ P hP mu hm hmP hmu
    refine ⟨1, fun _ => P, ?_, fun _ => hP, ?_, ?_⟩
    · constructor
      · intro x; simp
      · intro i j hij
        exact ((bne_iff_ne.mp hij) (Subsingleton.elim i j)).elim
    · intro j
      simpa [multilinearPartitionExponent] using (show (m : Real) ≤ P.width by exact_mod_cast hmP)
    · intro i; exact Fin.elim0 i
  | succ q ih =>
    intro N m _ P hP mu hm hmP hmu
    have hm1 : multilinearPartitionThreshold k 1 ≤ m :=
      (multilinearPartitionThreshold_mono_q hk (by omega)).trans hm
    obtain ⟨M, Q, hQpart, hQproper, hQbounds⟩ :=
      ascending_multilinear_partition P hP (mu 0) hk hm1 hmP (hmu 0)
    obtain ⟨v, hvT, hvle, hvwidth, hvdiam⟩ := multilinear_iteration_scale hk hm
    have hlocal (i : Fin M) (a : Fin q) : MultilinearOn (Q i).carrier (mu a.succ) := by
      obtain ⟨psi, hpsi, heq⟩ := hmu a.succ
      exact ⟨psi, hpsi, fun x hx => heq x (IsPartition.cell_subset hQpart i hx)⟩
    choose L R hRpart hRproper hRwidth hRdiam using fun i =>
      ih N v (Q i) (hQproper i) (fun a => mu a.succ) hvT (hvle _ (hQbounds i).1) (hlocal i)
    have hfinal (i : Fin M) (j : Fin (L i)) (a : Fin (q + 1)) :
        diameterAtMostReal ((R i j).carrier.image (mu a))
          (2 * (m : Real) ^ (-multilinearPartitionExponent k (q + 1)) * N) := by
      refine Fin.cases ?_ (fun b => ?_) a
      · apply diameterAtMostReal_mono
          (Finset.image_mono _ (IsPartition.cell_subset (hRpart i) j)) (hQbounds i).2
        have hmReal : (1 : Real) ≤ m := by
          have h := (multilinearHeightThreshold_bounds hk (2 ^ k * (q + 1))).1.trans hm
          exact_mod_cast (show 1 ≤ m by omega)
        have hpow := Real.rpow_le_rpow_of_exponent_le hmReal
          (neg_le_neg (multilinearPartitionExponent_succ_le_one (q := q) hk))
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) (Nat.cast_nonneg N)
      · apply diameterAtMostReal_mono (Finset.Subset.refl _) (hRdiam i b j)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvdiam (by norm_num)) (Nat.cast_nonneg N)
    refine ⟨∑ i, L i, boxFlatten L R, boxFlatten_partition P Q L R hQpart hRpart, ?_, ?_, ?_⟩
    · intro j
      let z := (section5NatFlattenEquiv L).symm j
      exact hRproper z.1 z.2
    · intro j
      let z := (section5NatFlattenEquiv L).symm j
      exact hvwidth.trans (hRwidth z.1 z.2)
    · intro a j
      let z := (section5NatFlattenEquiv L).symm j
      exact hfinal z.1 z.2 a

/-- Simultaneous genuine integer-box partitioning, including an empty
function family, with all the original thresholds and numerical bounds. -/
theorem genuine_multilinear_simultaneous (k : Nat) (hk : 2 ≤ k) (q : Nat) :
    ∀ (N m : Nat) [NeZero N] (P : Box N k), P.HasIntegerRepresentatives →
      ∀ mu : Fin q → Point N k → ZMod N,
        multilinearPartitionThreshold k q ≤ m → m ≤ P.width →
        (∀ i, MultilinearOn P.carrier (mu i)) →
        ∃ M : Nat, ∃ R : Fin M → Box N k,
          IsBoxPartition R P ∧ (∀ j, (R j).IsAscendingInteger) ∧
          (∀ j, (m : Real) ^ multilinearPartitionExponent k q ≤ (R j).width) ∧
          ∀ i j, diameterAtMostReal ((R j).carrier.image (mu i))
            (2 * (m : Real) ^ (-multilinearPartitionExponent k q) * N) := by
  intro N m _ P hP mu hm hmP hmu
  obtain ⟨d, Q, hstep, hd, hQ, hcarrier, hwidth, hcommon⟩ := hP.canonical_axes
  let C := integerAxesBox N Q d hstep
  have hC : C.IsAscendingInteger :=
    ⟨d, Q, hd, rfl, fun i => ⟨(hQ i).1, hstep i, (hQ i).2, rfl⟩⟩
  obtain ⟨M, R, hpart, hR, hRwidth, hRdiam⟩ :=
    ascending_multilinear_simultaneous k hk q N m C hC mu hm (by rwa [hwidth])
      (fun i => by rw [hcarrier]; exact hmu i)
  refine ⟨M, R, ?_, hR, hRwidth, hRdiam⟩
  change IsPartition (fun j => (R j).carrier) P.carrier
  rw [← hcarrier]
  exact hpart

/-- Corollary 5.11 with genuine common-difference integer boxes. -/
def corollary_5_11_integer_representatives : Prop :=
  ∀ (N k q m : Nat) [NeZero N] (P : Box N k) (mu : Fin q → Point N k → ZMod N),
    P.HasIntegerRepresentatives → 2 ≤ k → 1 ≤ q →
    multilinearPartitionThreshold k q ≤ m → m ≤ P.width →
    (∀ i, MultilinearOn P.carrier (mu i)) →
      ∃ M : Nat, ∃ R : Fin M → Box N k,
        IsBoxPartition R P ∧ (∀ j, (R j).HasIntegerRepresentatives) ∧
        ∀ i j, (m : Real) ^ multilinearPartitionExponent k q ≤ (R j).width ∧
          diameterAtMostReal ((R j).carrier.image (mu i))
            (2 * (m : Real) ^ (-multilinearPartitionExponent k q) * N)

theorem corollary_5_11_integer_representatives_holds : corollary_5_11_integer_representatives := by
  intro N k q m _ P mu hP hk hq hm hmP hmu
  obtain ⟨M, R, hpart, hR, hwidth, hdiam⟩ :=
    genuine_multilinear_simultaneous k hk q N m P hP mu hm hmP hmu
  exact ⟨M, R, hpart, fun j => (hR j).toGenuine, fun i j => ⟨hwidth j, hdiam i j⟩⟩

end LeanProofs.GowersSzemeredi
