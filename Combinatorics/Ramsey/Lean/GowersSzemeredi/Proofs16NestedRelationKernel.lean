import GowersSzemeredi.Proofs16BoundedBadRelations
import GowersSzemeredi.Proofs16VarietyRegularStep

/-! Retain all previous frequencies when refining the relation domain.
This also preserves quarter-radius containment, which full-domain set
containment alone would not guarantee. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Adjoining the kernel spectrum preserves the old frequency set and
quarter domain while still strictly enlarging the relation subspace. -/
theorem nested_relation_kernel_of_bounded_bad_pairs {N : Nat} [NeZero N] [Fact N.Prime]
    {ι κ : Type*} [Fintype ι] [Fintype κ] (gamma : ι → ZMod N)
    (Gamma : Finset (ZMod N)) {sigma : Real} (hsigma : 0 ≤ sigma)
    (L : κ → ZMod N → ZMod N) (hL : ∀ j, IsFreimanLinearOn (bohr Gamma sigma) (L j))
    (C : Finset (ZMod N)) (hCne : C.Nonempty) (hC : C ⊆ bohr Gamma (sigma / 4))
    (R : Nat) {theta : Real} (htheta : 0 < theta)
    (hpairs : theta * (C.card : Real)^2 ≤
      (boundedBadRelationPairs gamma (bohr Gamma sigma) L C R).card) :
    let tau := min sigma (1 / (8 * Real.pi))
    ∃ S : Finset (ZMod N), Gamma ⊆ S ∧
      (S.card : Real) ≤ Gamma.card + 16 *
        ((theta / ((2 * R + 1)^(Fintype.card ι + 2 * Fintype.card κ) : Nat)) * C.card / N) ^ (-(2 : Real)) ∧
      bohr S tau ⊆ bohr Gamma sigma ∧ bohr S (tau / 4) ⊆ bohr Gamma (sigma / 4) ∧
      relationSubmodule (bohr Gamma sigma) L < relationSubmodule (bohr S tau) L := by
  obtain ⟨T, hT, hTB, hstrict⟩ :=
    strict_relation_kernel_of_bounded_bad_pairs gamma Gamma hsigma L hL C hCne hC R htheta hpairs
  let tau := min sigma (1 / (8 * Real.pi))
  have hG : bohr (Gamma ∪ T) tau ⊆ bohr Gamma sigma := by
    rw [bohr_union]
    exact fun x hx => bohr_mono_radius Gamma (min_le_left _ _) (Finset.mem_inter.mp hx).1
  have hquarter : bohr (Gamma ∪ T) (tau / 4) ⊆ bohr Gamma (sigma / 4) := by
    rw [bohr_union]
    exact fun x hx => bohr_mono_radius Gamma (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
      (Finset.mem_inter.mp hx).1
  have hTsub : bohr (Gamma ∪ T) tau ⊆ bohr T (1 / (8 * Real.pi)) := by
    rw [bohr_union]
    exact fun x hx => bohr_mono_radius T (min_le_right _ _) (Finset.mem_inter.mp hx).2
  refine ⟨Gamma ∪ T, Finset.subset_union_left, ?_, hG, hquarter,
    lt_of_lt_of_le hstrict (relationSubmodule_anti hTsub L)⟩
  have hcard : ((Gamma ∪ T).card : Real) ≤ Gamma.card + T.card := by
    exact_mod_cast Finset.card_union_le Gamma T
  linarith

end LeanProofs.GowersSzemeredi
