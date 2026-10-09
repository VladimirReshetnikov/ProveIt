import GowersSzemeredi.Proofs16RefinementKernel
import GowersSzemeredi.Proofs16BohrDenseDifference

/-! A nonzero value on a half-radius domain forces many nonzero values
on the full domain. Extra column constraints can be handled quantitatively. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Translate the half-domain by one nonzero point. Each original point
or its translate has nonzero image, so the nonzero set covers at least half. -/
theorem freiman_nonzero_card_half {N : Nat} [NeZero N]
    (T : Finset (ZMod N)) {r : Real} (hr : 0 ≤ r)
    (f : ZMod N → ZMod N) (hf : IsFreimanLinearOn (bohr T r) f) (hf0 : f 0 = 0)
    {z : ZMod N} (hz : z ∈ bohr T (r/2)) (hfz : f z ≠ 0) :
    (bohr T (r/2)).card ≤ 2*((bohr T r).filter (fun y => f y ≠ 0)).card := by
  let D := (bohr T r).filter (fun y => f y ≠ 0)
  have hhalf : bohr T (r/2) ⊆ bohr T r := bohr_mono_radius T (by linarith)
  have hsub : bohr T (r/2) ⊆ D ∪ D.image (fun y => y-z) := by
    intro x hx
    by_cases hfx : f x = 0
    · have hxz : x+z ∈ bohr T r := bohr_add_half hx hz
      have he := hf x z (x+z) 0 (hhalf hx) (hhalf hz) hxz (zero_mem_bohr T hr) (by simp)
      have hfn : f (x+z) ≠ 0 := by
        intro h
        rw [hfx,h,hf0] at he
        exact hfz (by simpa using he)
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨x+z,Finset.mem_filter.mpr ⟨hxz,hfn⟩,by abel⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hhalf hx,hfx⟩)
  calc _ ≤ (D ∪ D.image (fun y => y-z)).card := Finset.card_le_card hsub
    _ ≤ D.card+(D.image (fun y => y-z)).card := Finset.card_union_le _ _
    _ ≤ D.card+D.card := Nat.add_le_add_left (Finset.card_image_le) _
    _ = _ := by dsimp only [D]; omega

/-- A model nonzero after frequency removal has a nonzero point even
when any extra spectrum of the specified rank is imposed. -/
theorem freiman_nonzero_with_extra_frequencies {N d e : Nat} [NeZero N] [Fact N.Prime]
    (T U : Finset (ZMod N)) (f : ZMod N → ZMod N) {rho r : Real}
    (hrho : 0 < rho) (hr : 0 < r) (hrle : r ≤ rho)
    (hT : T.card ≤ d) (hU : U.card ≤ e)
    (hf : IsFreimanLinearOn (bohr T rho) f) (hf0 : f 0 = 0)
    (hne : ∃ y ∈ bohr T (refinementKernelRadius d e rho (r/2)), f y ≠ 0)
    (hN : refinementKernelCap d e rho (r/2) < N) :
    ∃ z ∈ bohr (T ∪ U) (r/2), f z ≠ 0 := by
  by_contra hn
  push Not at hn
  have hz := freiman_zero_remove_frequencies T U f hrho (by positivity) (by linarith)
    hT hU hf hf0 hn hN
  obtain ⟨y,hy,hfy⟩ := hne
  exact hfy (hz y hy)

/-- Explicit density of nonzero values after imposing extra column spectra. -/
theorem freiman_nonzero_card_with_extra_frequencies {N d e : Nat} [NeZero N] [Fact N.Prime]
    (T U : Finset (ZMod N)) (f : ZMod N → ZMod N) {rho r : Real}
    (hrho : 0 < rho) (hr : 0 < r) (hrle : r ≤ rho)
    (hT : T.card ≤ d) (hU : U.card ≤ e)
    (hf : IsFreimanLinearOn (bohr T rho) f) (hf0 : f 0 = 0)
    (hne : ∃ y ∈ bohr T (refinementKernelRadius d e rho (r/2)), f y ≠ 0)
    (hN : refinementKernelCap d e rho (r/2) < N) :
    N ≤ 2*(refinementCells (r/2))^(d+e)*
      ((bohr (T ∪ U) r).filter (fun y => f y ≠ 0)).card := by
  obtain ⟨z,hz,hfz⟩ := freiman_nonzero_with_extra_frequencies T U f hrho hr hrle hT hU hf hf0 hne hN
  have hdom : bohr (T ∪ U) r ⊆ bohr T rho := by
    intro y hy
    rw [bohr_union] at hy
    exact bohr_mono_radius T hrle (Finset.mem_inter.mp hy).1
  have hf' : IsFreimanLinearOn (bohr (T ∪ U) r) f := hf.mono hdom
  have hhalf := freiman_nonzero_card_half (T ∪ U) hr.le f hf' hf0 hz hfz
  let Q := refinementCells (r/2)
  have hQ : 0 < Q := Nat.ceil_pos.mpr (by positivity)
  letI : NeZero Q := ⟨ne_of_gt hQ⟩
  have hcell : 1 ≤ (r/2)*(Q : Real) := by
    have hc : 1/(r/2) ≤ (Q : Real) := Nat.le_ceil _
    have hh := (div_le_iff₀ (by positivity : (0 : Real) < r/2)).mp hc
    nlinarith only [hh]
  have hcard := bohr_card_lower (T ∪ U) Q hcell
  have hrank : (T ∪ U).card ≤ d+e := (Finset.card_union_le _ _).trans (Nat.add_le_add hT hU)
  calc N ≤ Q^(T ∪ U).card*(bohr (T ∪ U) (r/2)).card := hcard
    _ ≤ Q^(d+e)*(2*((bohr (T ∪ U) r).filter (fun y => f y ≠ 0)).card) :=
      Nat.mul_le_mul (Nat.pow_le_pow_right hQ hrank) hhalf
    _ = _ := by ring

end LeanProofs.GowersSzemeredi
