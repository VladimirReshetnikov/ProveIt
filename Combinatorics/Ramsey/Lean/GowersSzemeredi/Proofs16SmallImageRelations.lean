import GowersSzemeredi.Proofs16PrimeSmallRange

/-! Small-image relations among local maps become exact after shrinking
their Bohr domains. This uses the prime target and preserves frequencies. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A finite family of Bohr constraints is a Bohr set on the union of
its frequency sets. -/
theorem mem_bohr_family_union {N : Nat} [NeZero N] {κ : Type*} [Fintype κ]
    (T : κ → Finset (ZMod N)) (rho : Real) (y : ZMod N) :
    y ∈ bohr (Finset.univ.biUnion T) rho ↔ ∀ j, y ∈ bohr (T j) rho := by
  constructor
  · intro h j
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro r hr
    exact (Finset.mem_filter.mp h).2 r (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hr⟩)
  · intro h
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro r hr
    obtain ⟨j, _, hr⟩ := Finset.mem_biUnion.mp hr
    exact (Finset.mem_filter.mp (h j)).2 r hr

/-- A bounded-image linear combination is constant on the smaller common
Bohr domain, without changing any frequency set. -/
theorem small_image_combination_constant {N K : Nat} [NeZero N] [Fact N.Prime]
    {κ : Type*} [Fintype κ] (T : κ → Finset (ZMod N))
    (L : κ → ZMod N → ZMod N) (w : κ → ZMod N) {rho : Real} (hrho : 0 ≤ rho)
    (hL : ∀ j, IsFreimanLinearOn (bohr (T j) rho) (L j))
    (himage : ((bohr (Finset.univ.biUnion T) rho).image
      (fun y => ∑ j, w j * L j y)).card ≤ K) (hKN : K < N) :
    ∀ y, (∀ j, y ∈ bohr (T j) (rho / K)) →
      ∑ j, w j * L j y = ∑ j, w j * L j 0 := by
  have hcommon : ∀ j, IsFreimanLinearOn (bohr (Finset.univ.biUnion T) rho) (L j) := by
    intro j a b c d ha hb hc hd heq
    exact hL j a b c d ((mem_bohr_family_union T rho a).mp ha j)
      ((mem_bohr_family_union T rho b).mp hb j) ((mem_bohr_family_union T rho c).mp hc j)
      ((mem_bohr_family_union T rho d).mp hd j) heq
  intro y hy
  exact freiman_small_image_constant _ hrho _ (IsFreimanLinearOn.linear_combination hcommon w)
    himage hKN y ((mem_bohr_family_union T _ y).mpr hy)

/-- The normalized version gives an exact linear relation. -/
theorem small_image_combination_zero {N K : Nat} [NeZero N] [Fact N.Prime]
    {κ : Type*} [Fintype κ] (T : κ → Finset (ZMod N))
    (L : κ → ZMod N → ZMod N) (w : κ → ZMod N) {rho : Real} (hrho : 0 ≤ rho)
    (hL : ∀ j, IsFreimanLinearOn (bohr (T j) rho) (L j)) (hzero : ∀ j, L j 0 = 0)
    (himage : ((bohr (Finset.univ.biUnion T) rho).image
      (fun y => ∑ j, w j * L j y)).card ≤ K) (hKN : K < N) :
    ∀ y, (∀ j, y ∈ bohr (T j) (rho / K)) → ∑ j, w j * L j y = 0 := by
  intro y hy
  simpa only [hzero, mul_zero, Finset.sum_const_zero] using
    small_image_combination_constant T L w hrho hL himage hKN y hy

/-- Any collection of bounded-image relations holds simultaneously on
one shrunken domain; there is no loss depending on the collection size. -/
theorem small_image_relations_submodule {N K : Nat} [NeZero N] [Fact N.Prime]
    {κ : Type*} [Fintype κ] (T : Finset (ZMod N)) (L : κ → ZMod N → ZMod N)
    {rho : Real} (hrho : 0 ≤ rho) (hL : ∀ j, IsFreimanLinearOn (bohr T rho) (L j))
    (R : Set (κ → ZMod N))
    (himage : ∀ w ∈ R, ((bohr T rho).image (fun y => ∑ j, w j * L j y)).card ≤ K)
    (hKN : K < N) :
    R ⊆ relationSubmodule (bohr T (rho / K)) L := by
  intro w hw y hy
  have h := freiman_small_image_constant T hrho _ (IsFreimanLinearOn.linear_combination hL w)
    (himage w hw) hKN y hy
  simpa only [mul_sub, Finset.sum_sub_distrib, sub_eq_zero] using h

end LeanProofs.GowersSzemeredi
