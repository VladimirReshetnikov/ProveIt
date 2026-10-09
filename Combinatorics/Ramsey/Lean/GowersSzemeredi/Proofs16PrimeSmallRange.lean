import GowersSzemeredi.Proofs16FreimanKernelBohr

/-! A small image forces a Freiman-linear map into its kernel after a
radius shrink, when the target is a prime cyclic group. The frequencies
are unchanged. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The first `M` multiples of a point in the radius-`rho/M` Bohr set
remain in the original Bohr set. -/
theorem bohr_nat_multiple_mem {N M : Nat} [NeZero N]
    (T : Finset (ZMod N)) {rho : Real} (hrho : 0 ≤ rho) (hM : 0 < M)
    {y : ZMod N} (hy : y ∈ bohr T (rho / M)) {j : Nat} (hj : j ≤ M) :
    (j : ZMod N) * y ∈ bohr T rho := by
  have hMR : (0 : Real) < M := by exact_mod_cast hM
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  intro r hr
  have hy' := (Finset.mem_filter.mp hy).2 r hr
  have hb : (centeredAbs (r * ((j : ZMod N) * y)) : Real) ≤
      (j : Real) * centeredAbs (r * y) := by
    have h := centeredAbs_natCast_mul_le j (r * y)
    rw [mul_left_comm] at h
    exact_mod_cast h
  have hjR : (j : Real) ≤ M := by exact_mod_cast hj
  calc _ ≤ (j : Real) * centeredAbs (r * y) := hb
    _ ≤ (j : Real) * (rho / M * N) := mul_le_mul_of_nonneg_left hy' (Nat.cast_nonneg _)
    _ ≤ (M : Real) * (rho / M * N) := mul_le_mul_of_nonneg_right hjR (by positivity)
    _ = rho * N := by field_simp

/-- The Freiman identity gives the affine formula along every finite
sequence of multiples which stays inside the domain. -/
theorem IsFreimanLinearOn.nat_multiple {N M : Nat} {B : Finset (ZMod N)}
    {f : ZMod N → ZMod N} (hf : IsFreimanLinearOn B f) {y : ZMod N}
    (hM : 0 < M) (hdom : ∀ j ≤ M, (j : ZMod N) * y ∈ B) :
    ∀ j ≤ M, f ((j : ZMod N) * y) = (j : ZMod N) * (f y - f 0) + f 0 := by
  have h0 : (0 : ZMod N) ∈ B := by simpa using hdom 0 (by omega)
  have hy : y ∈ B := by simpa using hdom 1 hM
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
    have hj' : j ≤ M := by omega
    have h := hf ((j : ZMod N) * y) y (((j + 1 : Nat) : ZMod N) * y) 0
      (hdom j hj') hy (hdom (j + 1) hj) h0 (by push_cast; ring)
    rw [ih hj'] at h
    push_cast at h ⊢
    linear_combination -h

/-- If a Freiman-linear map into a prime cyclic group takes at most `K<N`
values, it is constant on the same Bohr set with radius divided by `K`. -/
theorem freiman_small_image_constant {N K : Nat} [NeZero N] [Fact N.Prime]
    (T : Finset (ZMod N)) {rho : Real} (hrho : 0 ≤ rho)
    (f : ZMod N → ZMod N) (hf : IsFreimanLinearOn (bohr T rho) f)
    (himage : ((bohr T rho).image f).card ≤ K) (hKN : K < N) :
    ∀ y ∈ bohr T (rho / K), f y = f 0 := by
  have hK : 0 < K := (Finset.card_pos.mpr
    ⟨f 0, Finset.mem_image_of_mem f (zero_mem_bohr T hrho)⟩).trans_le himage
  intro y hy
  by_contra hfy
  have hdiff : f y - f 0 ≠ 0 := sub_ne_zero.mpr hfy
  have hdom := fun j hj => bohr_nat_multiple_mem T hrho hK hy (j := j) hj
  have hformula := hf.nat_multiple hK hdom
  have hinj : Function.Injective (fun j : Fin (K + 1) => f ((j.val : ZMod N) * y)) := by
    intro i j hij
    dsimp only at hij
    rw [hformula i.val (by omega), hformula j.val (by omega)] at hij
    have heq : (i.val : ZMod N) = j.val := mul_right_cancel₀ hdiff (add_right_cancel hij)
    have heq' := (ZMod.natCast_eq_natCast_iff' i.val j.val N).mp heq
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heq'
    exact Fin.ext heq'
  have hcard : K + 1 ≤ ((bohr T rho).image f).card := by
    calc K + 1 = (Finset.univ.image (fun j : Fin (K + 1) => f ((j.val : ZMod N) * y))).card := by
          rw [Finset.card_image_of_injective _ hinj]; simp
      _ ≤ _ := Finset.card_le_card (by
        intro v hv
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
        exact Finset.mem_image_of_mem f (hdom j.val (by omega)))
  omega

/-- For normalized maps the constant value is zero. -/
theorem freiman_small_image_zero {N K : Nat} [NeZero N] [Fact N.Prime]
    (T : Finset (ZMod N)) {rho : Real} (hrho : 0 ≤ rho)
    (f : ZMod N → ZMod N) (hf : IsFreimanLinearOn (bohr T rho) f) (hf0 : f 0 = 0)
    (himage : ((bohr T rho).image f).card ≤ K) (hKN : K < N) :
    ∀ y ∈ bohr T (rho / K), f y = 0 := by
  intro y hy
  exact (freiman_small_image_constant T hrho f hf himage hKN y hy).trans hf0

end LeanProofs.GowersSzemeredi
