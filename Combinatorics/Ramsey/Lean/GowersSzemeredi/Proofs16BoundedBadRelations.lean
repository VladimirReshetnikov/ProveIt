import GowersSzemeredi.Proofs16BadRelationKernel
import GowersSzemeredi.Proofs16BoundedFrequencySpan

/-! The finite bad-pair relation family used in the algebraic regularity
iteration, with a modulus-independent bound on the coefficient count. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def boundedBadRelationPairs {N : Nat} [NeZero N] [Fact N.Prime]
    {ι κ : Type*} [Fintype ι] [Fintype κ] (gamma : ι → ZMod N)
    (D : Finset (ZMod N)) (L : κ → ZMod N → ZMod N) (C : Finset (ZMod N)) (R : Nat) :
    Finset (ZMod N × ZMod N) :=
  (C ×ˢ C).filter fun p => ∃ (nu : ι → centeredBall N R)
    (w v : κ → centeredBall N R),
      ((fun j => (w j : ZMod N)) ∉ relationSubmodule D L ∨
        (fun j => (v j : ZMod N)) ∉ relationSubmodule D L) ∧
      (∑ i, (nu i : ZMod N) * gamma i) + (∑ j, (w j : ZMod N) * L j p.1) +
        (∑ j, (v j : ZMod N) * L j p.2) = 0

/-- The coefficient ball bound also covers radii that wrap around the group. -/
theorem centeredBall_card_le_diameter {N : Nat} [NeZero N] (R : Nat) :
    (centeredBall N R).card ≤ 2 * R + 1 := by
  by_cases hR : 2 * R < N
  · rw [centeredBall_eq_image hR]
    exact Finset.card_image_le.trans (by simp)
  · have h := Finset.card_le_univ (centeredBall N R)
    rw [ZMod.card] at h
    omega

/-- Too many bad bounded pair relations force a strict enlargement of the
relation subspace, with an explicit coefficient-count loss. -/
theorem strict_relation_kernel_of_bounded_bad_pairs {N : Nat} [NeZero N] [Fact N.Prime]
    {ι κ : Type*} [Fintype ι] [Fintype κ] (gamma : ι → ZMod N)
    (Gamma : Finset (ZMod N)) {sigma : Real} (hsigma : 0 ≤ sigma)
    (L : κ → ZMod N → ZMod N) (hL : ∀ j, IsFreimanLinearOn (bohr Gamma sigma) (L j))
    (C : Finset (ZMod N)) (hCne : C.Nonempty) (hC : C ⊆ bohr Gamma (sigma / 4))
    (R : Nat) {theta : Real} (htheta : 0 < theta)
    (hpairs : theta * (C.card : Real)^2 ≤
      (boundedBadRelationPairs gamma (bohr Gamma sigma) L C R).card) :
    ∃ S : Finset (ZMod N),
      (S.card : Real) ≤ 16 *
        ((theta / ((2 * R + 1)^(Fintype.card ι + 2 * Fintype.card κ) : Nat)) * C.card / N) ^ (-(2 : Real)) ∧
      bohr S (1 / (8 * Real.pi)) ⊆ bohr Gamma sigma ∧
      relationSubmodule (bohr Gamma sigma) L < relationSubmodule (bohr S (1 / (8 * Real.pi))) L := by
  let H := (ι → centeredBall N R) × (κ → centeredBall N R) × (κ → centeredBall N R)
  let T : Finset H := Finset.univ.filter fun q =>
    (fun j => (q.2.1 j : ZMod N)) ∉ relationSubmodule (bohr Gamma sigma) L ∨
      (fun j => (q.2.2 j : ZMod N)) ∉ relationSubmodule (bohr Gamma sigma) L
  let P := boundedBadRelationPairs gamma (bohr Gamma sigma) L C R
  have hCpos : (0 : Real) < C.card := by exact_mod_cast hCne.card_pos
  have hPne : P.Nonempty := by
    apply Finset.card_pos.mp
    have hpos : (0 : Real) < P.card := lt_of_lt_of_le (by positivity) hpairs
    exact_mod_cast hpos
  have hTne : T.Nonempty := by
    obtain ⟨p, hp⟩ := hPne
    obtain ⟨nu, w, v, hbad, hrel⟩ := (Finset.mem_filter.mp hp).2
    exact ⟨(nu, w, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩⟩
  have hTcard : T.card ≤ (2 * R + 1)^(Fintype.card ι + 2 * Fintype.card κ) := by
    calc
      _ ≤ Fintype.card H := Finset.card_le_univ T
      _ = (centeredBall N R).card^(Fintype.card ι + 2 * Fintype.card κ) := by
        simp [H, ← pow_add, two_mul]
      _ ≤ _ := Nat.pow_le_pow_left (centeredBall_card_le_diameter R) _
  apply strict_relation_kernel_of_bad_relation_cover_bound Gamma hsigma L hL C hCne hC T hTne
    (fun q j => (q.2.1 j : ZMod N)) (fun q j => (q.2.2 j : ZMod N))
    (fun q => -(∑ i, (q.1 i : ZMod N) * gamma i))
    (fun q hq => (Finset.mem_filter.mp hq).2) P (Finset.filter_subset _ _) _ htheta hpairs
    (by exact_mod_cast hTcard)
  intro p hp
  obtain ⟨nu, w, v, hbad, hrel⟩ := (Finset.mem_filter.mp hp).2
  refine ⟨(nu, w, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩, ?_⟩
  dsimp only
  linear_combination hrel

end LeanProofs.GowersSzemeredi
