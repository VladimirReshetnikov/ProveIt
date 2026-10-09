import GowersSzemeredi.Proofs16StrictRelationKernel
import GowersSzemeredi.Proofs16PopularRelationFiber

/-! The regularity increment from a popular relation. Direct fibre averaging
preserves the pair density in the extracted fibre, improving the density
loss over a preliminary collision-pair argument. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A popular matching equation involving a nonrelation creates a nested
Bohr domain with strictly more relations. Its rank loss is inverse-square
in the matching density, rather than in its square. -/
theorem strict_relation_kernel_of_matching_pairs {N : Nat} [NeZero N] [Fact N.Prime]
    {κ : Type*} [Fintype κ] (Gamma : Finset (ZMod N)) {sigma : Real} (hsigma : 0 ≤ sigma)
    (L : κ → ZMod N → ZMod N) (hL : ∀ j, IsFreimanLinearOn (bohr Gamma sigma) (L j))
    (w : κ → ZMod N) (hw : w ∉ relationSubmodule (bohr Gamma sigma) L)
    (C : Finset (ZMod N)) (hCne : C.Nonempty) (hC : C ⊆ bohr Gamma (sigma / 4))
    (g : ZMod N → ZMod N) {theta : Real} (htheta : 0 < theta)
    (hpairs : theta * (C.card : Real)^2 ≤
      (((C ×ˢ C).filter fun p => (∑ j, w j * L j p.1) = g p.2).card : Real)) :
    ∃ S : Finset (ZMod N),
      (S.card : Real) ≤ 16 * (theta * C.card / N) ^ (-(2 : Real)) ∧
      bohr S (1 / (8 * Real.pi)) ⊆ bohr Gamma sigma ∧
      relationSubmodule (bohr Gamma sigma) L < relationSubmodule (bohr S (1 / (8 * Real.pi))) L := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hCpos : (0 : Real) < C.card := by exact_mod_cast hCne.card_pos
  obtain ⟨y, hy, hpop⟩ := exists_popular_matching_fiber C C hCne
    (fun x => ∑ j, w j * L j x) g (by nlinarith only [hpairs])
  let F := C.filter fun x => (∑ j, w j * L j x) = g y
  let alpha := (F.card : Real) / N
  have hFpos : (0 : Real) < F.card := lt_of_lt_of_le (mul_pos htheta hCpos) hpop
  have ha : 0 < alpha := div_pos hFpos hN
  have hcard : (F.card : Real) = alpha * N := by dsimp [alpha]; field_simp
  have hF : F ⊆ bohr Gamma (sigma / 4) := (Finset.filter_subset _ _).trans hC
  have hconst : ∀ x ∈ F, ∑ j, w j * L j x = g y := fun x hx => (Finset.mem_filter.mp hx).2
  obtain ⟨hS, hsub, hstrict⟩ :=
    strict_relation_kernel_of_constant_fiber Gamma hsigma L hL w hw F hF hconst ha hcard
  refine ⟨section7Spectrum F alpha, hS.trans ?_, hsub, hstrict⟩
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Real.rpow_le_rpow_of_nonpos (div_pos (mul_pos htheta hCpos) hN)
    (div_le_div_of_nonneg_right hpop hN.le) (by norm_num)

/-- A popular two-sided linear relation gives the same strict enlargement
when its first coefficient vector is nontrivial on the current domain. -/
theorem strict_relation_kernel_of_many_pairs {N : Nat} [NeZero N] [Fact N.Prime]
    {κ : Type*} [Fintype κ] (Gamma : Finset (ZMod N)) {sigma : Real} (hsigma : 0 ≤ sigma)
    (L : κ → ZMod N → ZMod N) (hL : ∀ j, IsFreimanLinearOn (bohr Gamma sigma) (L j))
    (w v : κ → ZMod N) (z : ZMod N) (hw : w ∉ relationSubmodule (bohr Gamma sigma) L)
    (C : Finset (ZMod N)) (hCne : C.Nonempty) (hC : C ⊆ bohr Gamma (sigma / 4))
    {theta : Real} (htheta : 0 < theta)
    (hpairs : theta * (C.card : Real)^2 ≤
      (((C ×ˢ C).filter fun p => (∑ j, w j * L j p.1) + (∑ j, v j * L j p.2) = z).card : Real)) :
    ∃ S : Finset (ZMod N),
      (S.card : Real) ≤ 16 * (theta * C.card / N) ^ (-(2 : Real)) ∧
      bohr S (1 / (8 * Real.pi)) ⊆ bohr Gamma sigma ∧
      relationSubmodule (bohr Gamma sigma) L < relationSubmodule (bohr S (1 / (8 * Real.pi))) L := by
  apply strict_relation_kernel_of_matching_pairs Gamma hsigma L hL w hw C hCne hC
    (fun y => z - ∑ j, v j * L j y) htheta
  simpa only [eq_sub_iff_add_eq] using hpairs

/-- The cardinality of a two-sided relation is unchanged by exchanging
its coefficient vectors and swapping the two coordinates. -/
theorem linear_relation_pair_card_swap {N : Nat} {κ : Type*} [Fintype κ]
    (C : Finset (ZMod N)) (L : κ → ZMod N → ZMod N) (w v : κ → ZMod N) (z : ZMod N) :
    ((C ×ˢ C).filter fun p => (∑ j, w j * L j p.1) + (∑ j, v j * L j p.2) = z).card =
      ((C ×ˢ C).filter fun p => (∑ j, v j * L j p.1) + (∑ j, w j * L j p.2) = z).card := by
  apply Finset.card_bij (fun (p : ZMod N × ZMod N) _ => p.swap)
  · intro p hp
    obtain ⟨hpC, hpR⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(Finset.mem_product.mp hpC).2, (Finset.mem_product.mp hpC).1⟩, by simpa [add_comm] using hpR⟩
  · intro p hp q hq heq
    exact Prod.swap_injective heq
  · intro p hp
    refine ⟨p.swap, ?_, Prod.swap_swap p⟩
    obtain ⟨hpC, hpR⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(Finset.mem_product.mp hpC).2, (Finset.mem_product.mp hpC).1⟩, by simpa [add_comm] using hpR⟩

/-- It suffices that either side of a popular relation is nontrivial. -/
theorem strict_relation_kernel_of_many_pairs_either {N : Nat} [NeZero N] [Fact N.Prime]
    {κ : Type*} [Fintype κ] (Gamma : Finset (ZMod N)) {sigma : Real} (hsigma : 0 ≤ sigma)
    (L : κ → ZMod N → ZMod N) (hL : ∀ j, IsFreimanLinearOn (bohr Gamma sigma) (L j))
    (w v : κ → ZMod N) (z : ZMod N)
    (hbad : w ∉ relationSubmodule (bohr Gamma sigma) L ∨ v ∉ relationSubmodule (bohr Gamma sigma) L)
    (C : Finset (ZMod N)) (hCne : C.Nonempty) (hC : C ⊆ bohr Gamma (sigma / 4))
    {theta : Real} (htheta : 0 < theta)
    (hpairs : theta * (C.card : Real)^2 ≤
      (((C ×ˢ C).filter fun p => (∑ j, w j * L j p.1) + (∑ j, v j * L j p.2) = z).card : Real)) :
    ∃ S : Finset (ZMod N),
      (S.card : Real) ≤ 16 * (theta * C.card / N) ^ (-(2 : Real)) ∧
      bohr S (1 / (8 * Real.pi)) ⊆ bohr Gamma sigma ∧
      relationSubmodule (bohr Gamma sigma) L < relationSubmodule (bohr S (1 / (8 * Real.pi))) L := by
  rcases hbad with hw | hv
  · exact strict_relation_kernel_of_many_pairs Gamma hsigma L hL w v z hw C hCne hC htheta hpairs
  · apply strict_relation_kernel_of_many_pairs Gamma hsigma L hL v w z hv C hCne hC htheta
    rwa [← linear_relation_pair_card_swap C L w v z]

end LeanProofs.GowersSzemeredi
