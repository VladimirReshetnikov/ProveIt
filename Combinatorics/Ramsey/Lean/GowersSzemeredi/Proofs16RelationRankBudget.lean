import GowersSzemeredi.Proofs16NestedRelationKernel
import GowersSzemeredi.Proofs16WeightedBohrFilling

/-! Modulus-independent rank bookkeeping for the Bohr relation iteration.
A fixed cell count bounds the density of each quarter domain from below. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def relationRankStep (theta M : Real) (Q d : Nat) : Nat :=
  d + ⌈16 * ((theta / M) / (Q : Real)^d) ^ (-(2 : Real))⌉₊

theorem relationRankStep_ge (theta M : Real) (Q d : Nat) :
    d ≤ relationRankStep theta M Q d := Nat.le_add_right _ _

theorem relationRankStep_mono {theta M : Real} (htheta : 0 < theta) (hM : 0 < M)
    (Q : Nat) [NeZero Q] : Monotone (relationRankStep theta M Q) := by
  intro a b hab
  apply Nat.add_le_add hab
  apply Nat.ceil_mono
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hQ : (0 : Real) < Q := by exact_mod_cast NeZero.pos Q
  have hp : (Q : Real)^a ≤ (Q : Real)^b := by
    exact_mod_cast Nat.pow_le_pow_right (NeZero.pos Q) hab
  exact Real.rpow_le_rpow_of_nonpos (by positivity)
    (div_le_div_of_nonneg_left (div_pos htheta hM).le (by positivity) hp) (by norm_num)

/-- At a fixed small radius, a failed bad-pair bound refines the domain
with rank at most one explicit step of a recurrence independent of N. -/
theorem bounded_bad_pair_refinement_rank {N Q : Nat} [NeZero N] [NeZero Q] [Fact N.Prime]
    {ι κ : Type*} [Fintype ι] [Fintype κ] (gamma : ι → ZMod N)
    (Gamma : Finset (ZMod N)) {sigma : Real} (hsigma : 0 < sigma)
    (hsigmaMax : sigma ≤ 1 / (8 * Real.pi)) (hQ : 4 ≤ sigma * Q)
    (L : κ → ZMod N → ZMod N) (hL : ∀ j, IsFreimanLinearOn (bohr Gamma sigma) (L j))
    (R : Nat) {theta : Real} (htheta : 0 < theta)
    (hpairs : theta * ((bohr Gamma (sigma / 4)).card : Real)^2 ≤
      (boundedBadRelationPairs gamma (bohr Gamma sigma) L (bohr Gamma (sigma / 4)) R).card) :
    let M : Real := ((2 * R + 1)^(Fintype.card ι + 2 * Fintype.card κ) : Nat)
    ∃ S : Finset (ZMod N), Gamma ⊆ S ∧
      S.card ≤ relationRankStep theta M Q Gamma.card ∧
      bohr S sigma ⊆ bohr Gamma sigma ∧ bohr S (sigma / 4) ⊆ bohr Gamma (sigma / 4) ∧
      relationSubmodule (bohr Gamma sigma) L < relationSubmodule (bohr S sigma) L := by
  let C := bohr Gamma (sigma / 4)
  let M : Real := ((2 * R + 1)^(Fintype.card ι + 2 * Fintype.card κ) : Nat)
  have hC : C.Nonempty := ⟨0, zero_mem_bohr Gamma (by positivity)⟩
  have hM : 0 < M := by dsimp [M]; positivity
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hQpos : (0 : Real) < Q := by exact_mod_cast NeZero.pos Q
  have hNle : (N : Real) ≤ (Q : Real)^Gamma.card * C.card := by
    exact_mod_cast bohr_card_lower Gamma Q (show 1 ≤ sigma / 4 * Q by linarith)
  have hClow : 1 / (Q : Real)^Gamma.card ≤ (C.card : Real) / N := by
    apply (div_le_div_iff₀ (by positivity) hN).mpr
    nlinarith only [hNle]
  have hstep := nested_relation_kernel_of_bounded_bad_pairs gamma Gamma hsigma.le L hL C hC
    (Finset.Subset.refl _) R htheta hpairs
  dsimp only at hstep
  rw [min_eq_left hsigmaMax] at hstep
  obtain ⟨S, hGS, hS, hfull, hquarter, hstrict⟩ := hstep
  refine ⟨S, hGS, ?_, hfull, hquarter, hstrict⟩
  have hratio : (theta / M) / (Q : Real)^Gamma.card ≤ (theta / M) * C.card / N := by
    have h := mul_le_mul_of_nonneg_left hClow (div_pos htheta hM).le
    simpa only [mul_one_div, mul_div_assoc] using h
  have hpow := Real.rpow_le_rpow_of_nonpos (by positivity) hratio (show -(2 : Real) ≤ 0 by norm_num)
  have hcost := mul_le_mul_of_nonneg_left hpow (show (0 : Real) ≤ 16 by norm_num)
  have hceil := Nat.le_ceil (16 * ((theta / M) / (Q : Real)^Gamma.card) ^ (-(2 : Real)))
  have hbound : (S.card : Real) ≤
      Gamma.card + ⌈16 * ((theta / M) / (Q : Real)^Gamma.card) ^ (-(2 : Real))⌉₊ := by
    exact hS.trans (add_le_add_right (hcost.trans hceil) _)
  change S.card ≤ Gamma.card + ⌈16 * ((theta / M) / (Q : Real)^Gamma.card) ^ (-(2 : Real))⌉₊
  exact Nat.cast_le.mp (by simpa only [Nat.cast_add] using hbound)

end LeanProofs.GowersSzemeredi
