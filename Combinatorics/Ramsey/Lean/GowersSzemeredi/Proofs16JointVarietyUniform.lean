import GowersSzemeredi.Proofs16JointVarietyCover
import GowersSzemeredi.Proofs16FreimanVarietyUniform

/-! Uniform rank controls for simultaneous translated-variety covers.
Zero padding allows different mixed ranks without changing the varieties.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Extend a family of mixed coordinate maps by zero phases. -/
def padFreimanPhases {N r : Nat} (L : Fin r → ZMod N → ZMod N) (R : Nat) :
    Fin R → ZMod N → ZMod N :=
  fun k => if h : k.val < r then L ⟨k.val, h⟩ else fun _ => 0

theorem padFreimanPhases_linear {N r R : Nat} {B : Finset (ZMod N)}
    {L : Fin r → ZMod N → ZMod N} (hL : ∀ k, IsFreimanLinearOn B (L k)) :
    ∀ k, IsFreimanLinearOn B (padFreimanPhases L R k) := by
  intro k
  by_cases h : k.val < r
  · simpa [padFreimanPhases, h] using hL ⟨k.val, h⟩
  · simp only [padFreimanPhases, dif_neg h]
    intro x1 x2 x3 x4 _ _ _ _ _
    simp

/-- Zero padding preserves the full variety, including its half-radius form. -/
theorem bilinearBohrVariety_pad {N r R : Nat} [NeZero N]
    (Gamma Psi : Finset (ZMod N)) (L : Fin r → ZMod N → ZMod N)
    (hr : r ≤ R) {rho : Real} (hrho : 0 ≤ rho) :
    bilinearBohrVariety Gamma Psi (padFreimanPhases L R) rho =
      bilinearBohrVariety Gamma Psi L rho := by
  classical
  ext q
  rw [mem_bilinearBohrVariety_iff, mem_bilinearBohrVariety_iff]
  constructor
  · rintro ⟨hG, hP, hL⟩
    refine ⟨hG, hP, fun k => ?_⟩
    have h := hL ⟨k.val, k.isLt.trans_le hr⟩
    simpa [padFreimanPhases, k.isLt] using h
  · rintro ⟨hG, hP, hL⟩
    refine ⟨hG, hP, fun k => ?_⟩
    by_cases hk : k.val < r
    · simpa [padFreimanPhases, hk] using hL ⟨k.val, hk⟩
    · simp only [padFreimanPhases, dif_neg hk, zero_mul, centeredAbs, ZMod.valMinAbs_zero, Int.natAbs_zero, Nat.cast_zero]
      exact mul_nonneg hrho (Nat.cast_nonneg N)

theorem jointVarietyLinearRank_le {N n S : Nat} (Gamma Psi : Fin n → Finset (ZMod N))
    (h : ∀ i, (Gamma i).card + (Psi i).card ≤ S) :
    jointVarietyLinearRank Gamma Psi ≤ n * S := by
  classical
  calc
    _ ≤ (∑ i, (Gamma i).card) + ∑ i, (Psi i).card :=
      Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
    _ = ∑ i, ((Gamma i).card + (Psi i).card) := (Finset.sum_add_distrib).symm
    _ ≤ ∑ _i : Fin n, S := Finset.sum_le_sum fun i _ => h i
    _ = n * S := by simp

/-- The statement of `exists_uniform_joint_freiman_variety_cover` at fixed constants. -/
def UniformJointFreimanVarietyCoverAt (C p : Nat) : Prop :=
  ∀ (N n S R : Nat) [NeZero N] [Fact N.Prime]
    (Gamma Psi : Fin n → Finset (ZMod N)) (r : Fin n → Nat)
    (L : ∀ i, Fin (r i) → ZMod N → ZMod N)
    (rho : Fin n → Real) (a b : Fin n → ZMod N) (delta : Real),
    0 < delta → (∀ i, delta ≤ rho i) →
    (∀ i, (Gamma i).card + (Psi i).card ≤ S) → (∀ i, r i ≤ R) →
    (∀ i k, IsFreimanLinearOn (bohr (Psi i) (rho i)) (L i k)) →
    ∀ Phi : Fin n → ZMod N × ZMod N → ZMod N,
      (∀ i, IsEBihomomorphism (bilinearBohrVariety (Gamma i) (Psi i) (L i) (rho i)) (Phi i) {0}) →
    ∀ G : Fin n → Finset (Point N 2 × ZMod N),
      (∀ i, IsGraphOver (G i)
        (shiftPairs (bilinearBohrVariety (Gamma i) (Psi i) (L i) (rho i / 2)) (a i) (b i))
        (fun q => Phi i (q.1 - a i, q.2 - b i))) →
      MultiplyLinearWith (fun _ => 9 * n)
        (fun _ => section16CappedWidthExponent
          (section16FreimanVarietyExponent p (n * S) (n * R))
          (section16FreimanVarietyThreshold C p (n * S) (n * R) delta))
        (section16FinsetUnion G)

/-- `exists_uniform_joint_freiman_variety_cover` at the constants of its input. -/
theorem uniformJointFreimanVarietyCoverAt_of {C p : Nat} (hC : 2 ≤ C) (hp : 0 < p)
    (hcover : JointFreimanVarietyCoverAt C p) : UniformJointFreimanVarietyCoverAt C p := by
  classical
  unfold UniformJointFreimanVarietyCoverAt
  intro N n S R _ _ Gamma Psi r L rho a b delta hd hdelta hs hr hL Phi hPhi G hG
  have heq : ∀ i, bilinearBohrVariety (Gamma i) (Psi i) (padFreimanPhases (L i) R) (rho i) =
      bilinearBohrVariety (Gamma i) (Psi i) (L i) (rho i) := fun i =>
    bilinearBohrVariety_pad _ _ _ (hr i) (hd.trans_le (hdelta i)).le
  have heqHalf : ∀ i, bilinearBohrVariety (Gamma i) (Psi i) (padFreimanPhases (L i) R) (rho i / 2) =
      bilinearBohrVariety (Gamma i) (Psi i) (L i) (rho i / 2) := fun i =>
    bilinearBohrVariety_pad _ _ _ (hr i) (by have := hd.trans_le (hdelta i); positivity)
  have hML := hcover N n R Gamma Psi (fun i => padFreimanPhases (L i) R) rho a b delta hd hdelta
    (fun i => padFreimanPhases_linear (hL i)) Phi (fun i => by rw [heq]; exact hPhi i)
    G (fun i => by rw [heqHalf]; exact hG i)
  apply hML.weaken
  · intros; exact le_rfl
  · intros
    exact section16CappedWidthExponent_pos (section16FreimanVarietyExponent_pos hp _ _)
  · intros
    exact section16FreimanVarietyControl_mono (by omega) hp (jointVarietyLinearRank_le Gamma Psi hs)
      le_rfl hd le_rfl

/-- All-box covers uniform over a family with bounded, possibly different
ranks and a common radius lower bound. -/
theorem exists_uniform_joint_freiman_variety_cover :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ (N n S R : Nat) [NeZero N] [Fact N.Prime]
    (Gamma Psi : Fin n → Finset (ZMod N)) (r : Fin n → Nat)
    (L : ∀ i, Fin (r i) → ZMod N → ZMod N)
    (rho : Fin n → Real) (a b : Fin n → ZMod N) (delta : Real),
    0 < delta → (∀ i, delta ≤ rho i) →
    (∀ i, (Gamma i).card + (Psi i).card ≤ S) → (∀ i, r i ≤ R) →
    (∀ i k, IsFreimanLinearOn (bohr (Psi i) (rho i)) (L i k)) →
    ∀ Phi : Fin n → ZMod N × ZMod N → ZMod N,
      (∀ i, IsEBihomomorphism (bilinearBohrVariety (Gamma i) (Psi i) (L i) (rho i)) (Phi i) {0}) →
    ∀ G : Fin n → Finset (Point N 2 × ZMod N),
      (∀ i, IsGraphOver (G i)
        (shiftPairs (bilinearBohrVariety (Gamma i) (Psi i) (L i) (rho i / 2)) (a i) (b i))
        (fun q => Phi i (q.1 - a i, q.2 - b i))) →
      MultiplyLinearWith (fun _ => 9 * n)
        (fun _ => section16CappedWidthExponent
          (section16FreimanVarietyExponent p (n * S) (n * R))
          (section16FreimanVarietyThreshold C p (n * S) (n * R) delta))
        (section16FinsetUnion G) := by
  obtain ⟨C, p, hC, hp, hcover⟩ := exists_joint_freiman_variety_cover
  exact ⟨C, p, hC, hp, uniformJointFreimanVarietyCoverAt_of hC hp hcover⟩

end LeanProofs.GowersSzemeredi
