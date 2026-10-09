import GowersSzemeredi.Proofs16JointVarietyProfile
import GowersSzemeredi.Proofs16PolynomialVarietyCover

/-! Covers of unions of translated Freiman-variety graphs.

Every sufficiently wide cell uses one multilinear map per member. Bounded
fibres give a coarse cover below the threshold. The resulting all-box
cover has at most nine times the family size maps and one capped exponent
with polynomial dependence on the two total phase counts.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem graph_family_fiber_card_le {N n : Nat} [NeZero N]
    (G : Fin n → Finset (Point N 2 × ZMod N))
    (S : Fin n → Finset (ZMod N × ZMod N)) (Phi : Fin n → ZMod N × ZMod N → ZMod N)
    (hG : ∀ i, IsGraphOver (G i) (S i) (Phi i)) (x : Point N 2) :
    ((section16FinsetUnion G).filter fun z => z.1 = x).card ≤ n := by
  classical
  have hsub : ((section16FinsetUnion G).filter fun z => z.1 = x) ⊆
      Finset.univ.biUnion (fun i => (G i).filter fun z => z.1 = x) := by
    intro z hz
    obtain ⟨hz, heq⟩ := Finset.mem_filter.mp hz
    obtain ⟨i, hi, hz⟩ := Finset.mem_biUnion.mp hz
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hz, heq⟩⟩
  calc
    _ ≤ (Finset.univ.biUnion (fun i => (G i).filter fun z => z.1 = x)).card := Finset.card_le_card hsub
    _ ≤ ∑ i, ((G i).filter fun z => z.1 = x).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum fun i _ => (hG i).fiber_card_le_one x
    _ = n := by simp

/-- The statement of `exists_joint_freiman_variety_cover` at fixed constants. -/
def JointFreimanVarietyCoverAt (C p : Nat) : Prop :=
  ∀ (N n r : Nat) [NeZero N] [Fact N.Prime]
    (Gamma Psi : Fin n → Finset (ZMod N)) (L : Fin n → Fin r → ZMod N → ZMod N)
    (rho : Fin n → Real) (a b : Fin n → ZMod N) (delta : Real),
    0 < delta → (∀ i, delta ≤ rho i) →
    (∀ i k, IsFreimanLinearOn (bohr (Psi i) (rho i)) (L i k)) →
    ∀ Phi : Fin n → ZMod N × ZMod N → ZMod N,
      (∀ i, IsEBihomomorphism (bilinearBohrVariety (Gamma i) (Psi i) (L i) (rho i)) (Phi i) {0}) →
    ∀ G : Fin n → Finset (Point N 2 × ZMod N),
      (∀ i, IsGraphOver (G i)
        (shiftPairs (bilinearBohrVariety (Gamma i) (Psi i) (L i) (rho i / 2)) (a i) (b i))
        (fun q => Phi i (q.1 - a i, q.2 - b i))) →
      MultiplyLinearWith (fun _ => 9 * n)
        (fun _ => section16CappedWidthExponent
          (section16FreimanVarietyExponent p (jointVarietyLinearRank Gamma Psi) (n * r))
          (section16FreimanVarietyThreshold C p (jointVarietyLinearRank Gamma Psi) (n * r) delta))
        (section16FinsetUnion G)

/-- `exists_joint_freiman_variety_cover` at the constants of its input. -/
theorem jointFreimanVarietyCoverAt_of {C p : Nat} (hC : 2 ≤ C) (hp : 0 < p)
    (hpartition : JointFreimanVarietyGoodPartitionAt C p) : JointFreimanVarietyCoverAt C p := by
  classical
  unfold JointFreimanVarietyCoverAt
  intro N n r _ _ Gamma Psi L rho a b delta hd hdelta hL Phi hPhi G hG
  let e := section16FreimanVarietyExponent p (jointVarietyLinearRank Gamma Psi) (n * r)
  let T : Real := section16FreimanVarietyThreshold C p (jointVarietyLinearRank Gamma Psi) (n * r) delta
  have he : 0 < e := section16FreimanVarietyExponent_pos hp _ _
  have hlarge : ∀ s : Real, 0 < s → s ≤ 1 →
      LargeBoxMultilinearCover (section16FinsetUnion G) s n e T := by
    intro s hs _ P hP hwide
    obtain ⟨m, Q, hpart, hprop, hw, hg⟩ :=
      hpartition N n r Gamma Psi L rho a b delta hd hdelta hL P hP
        (by dsimp only [T] at hwide; exact_mod_cast hwide)
    choose mu hmu hcov using fun j i => cell_cover_of_good
      ((hPhi i).shift (a i) (b i)) (hG i) (Q j) (hg j i)
    refine ⟨m, n, P.carrier, Q, mu, subset_rfl, ?_, hpart, hprop, le_rfl, hw, hmu, ?_⟩
    · nlinarith [mul_nonneg hs.le (Nat.cast_nonneg P.carrier.card : (0 : Real) ≤ P.carrier.card)]
    · intro j x hx _ y hy
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hy
      exact ⟨i, hcov j i x hx y hi⟩
  have hML := multiplyLinearWith_of_large_box_covers (by decide : 0 < 2) n
    (graph_family_fiber_card_le G _ _ hG) (fun _ => n) (fun _ => e) (fun _ => T)
    (fun _ _ _ => he) hlarge
  have hcount : max (n : Real) ((3^2 * n : Nat) : Real) = 9 * n := by
    rw [show (3^2 * n : Nat) = 9 * n by norm_num, Nat.cast_mul, Nat.cast_ofNat]
    exact max_eq_right (by nlinarith [(Nat.cast_nonneg n : (0 : Real) ≤ n)])
  simpa only [hcount] using hML

/-- A union of translated variety graphs has common all-box controls with
linear map count and a polynomial phase-count exponent. -/
theorem exists_joint_freiman_variety_cover :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ (N n r : Nat) [NeZero N] [Fact N.Prime]
    (Gamma Psi : Fin n → Finset (ZMod N)) (L : Fin n → Fin r → ZMod N → ZMod N)
    (rho : Fin n → Real) (a b : Fin n → ZMod N) (delta : Real),
    0 < delta → (∀ i, delta ≤ rho i) →
    (∀ i k, IsFreimanLinearOn (bohr (Psi i) (rho i)) (L i k)) →
    ∀ Phi : Fin n → ZMod N × ZMod N → ZMod N,
      (∀ i, IsEBihomomorphism (bilinearBohrVariety (Gamma i) (Psi i) (L i) (rho i)) (Phi i) {0}) →
    ∀ G : Fin n → Finset (Point N 2 × ZMod N),
      (∀ i, IsGraphOver (G i)
        (shiftPairs (bilinearBohrVariety (Gamma i) (Psi i) (L i) (rho i / 2)) (a i) (b i))
        (fun q => Phi i (q.1 - a i, q.2 - b i))) →
      MultiplyLinearWith (fun _ => 9 * n)
        (fun _ => section16CappedWidthExponent
          (section16FreimanVarietyExponent p (jointVarietyLinearRank Gamma Psi) (n * r))
          (section16FreimanVarietyThreshold C p (jointVarietyLinearRank Gamma Psi) (n * r) delta))
        (section16FinsetUnion G) := by
  obtain ⟨C, p, hC, hp, hpartition⟩ := exists_joint_freiman_variety_good_partition
  exact ⟨C, p, hC, hp, jointFreimanVarietyCoverAt_of hC hp hpartition⟩

end LeanProofs.GowersSzemeredi
