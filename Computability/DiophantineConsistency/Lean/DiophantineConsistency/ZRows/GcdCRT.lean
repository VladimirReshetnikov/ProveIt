import DiophantineConsistency.ZRows.Intersective19

/-! # Chinese remainders for moduli that need not be coprime, in models of `𝗜𝚺₁`

The interpolation step of the ℤ rows (`ZROWS` toolkit T2) solves two congruences whose moduli
share factors. In every model `V` of `𝗜𝚺₁`, with `g` a gcd certificate of `M` and `N`
(`ArithmeticGcdNormalization.GcdCert`, which exists by `gcd_certificate_exists`):

* `crt_gcd`: if `g ∣ a − b` (in the ring of differences), some natural `x` has
  `x ≡ a (mod M)` and `x ≡ b (mod N)`. With `g = αM + βN` and `a − b = g·k`, the ring
  element `a − αkM = b + βkN` solves both; `ZRowsIntersective19.exists_nat_congr` gives a
  natural representative modulo `M·N`;
* `dvd_sub_of_crt`: conversely every common solution has `g ∣ a − b`;
* `crt_gcd_iff`: the two together. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ZRowsGcdCRT
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing ArithmeticGcdNormalization ModelBetaFunction ModelBoundedForallArith
open ZRowsIntersective19

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **CRT with a common factor**: compatible residues modulo `M` and `N` have a common
natural solution. -/
theorem crt_gcd {M N g a b : V} (hM : 0 < M) (hN : 0 < N) (hg : GcdCert M N g)
    (hab : (ι g : DiffRing V) ∣ ι a - ι b) :
    ∃ x : V, x % M = a % M ∧ x % N = b % N := by
  obtain ⟨u, v, w, z, he⟩ := hg.2.2
  have hbez : (ι g : DiffRing V) = ι M * (ι w - ι u) + ι N * (ι z - ι v) := by
    have := congrArg (ι (V := V)) he
    simp only [map_add, map_mul] at this
    linear_combination this
  obtain ⟨k, hk⟩ := hab
  obtain ⟨x, s, hs⟩ := exists_nat_congr (M * N) (mul_pos hM hN)
    (ι a - ι M * (ι w - ι u) * k)
  rw [map_mul] at hs
  refine ⟨x, ?_, ?_⟩
  · apply mod_eq_of_sub_eq (q := ι N * s - (ι w - ι u) * k)
    linear_combination hs
  · apply mod_eq_of_sub_eq (q := ι M * s + (ι z - ι v) * k)
    linear_combination hs + hk + k * hbez

/-- **Compatibility is necessary**: a common solution forces `g ∣ a − b`. -/
theorem dvd_sub_of_crt {M N g a b x : V} (hg : GcdCert M N g) (hxa : x % M = a % M)
    (hxb : x % N = b % N) : (ι g : DiffRing V) ∣ ι a - ι b := by
  obtain ⟨M', hM'⟩ := hg.1
  obtain ⟨N', hN'⟩ := hg.2.1
  obtain ⟨q1, h1⟩ := ringSub_of_mod_eq hxa
  obtain ⟨q2, h2⟩ := ringSub_of_mod_eq hxb
  refine ⟨ι N' * q2 - ι M' * q1, ?_⟩
  rw [hM', map_mul] at h1
  rw [hN', map_mul] at h2
  linear_combination h2 - h1

theorem crt_gcd_iff {M N g a b : V} (hM : 0 < M) (hN : 0 < N) (hg : GcdCert M N g) :
    (∃ x : V, x % M = a % M ∧ x % N = b % N) ↔ (ι g : DiffRing V) ∣ ι a - ι b :=
  ⟨fun ⟨_, hxa, hxb⟩ => dvd_sub_of_crt hg hxa hxb, crt_gcd hM hN hg⟩

#print axioms crt_gcd
#print axioms dvd_sub_of_crt
#print axioms crt_gcd_iff

end DiophantineConsistency.ZRowsGcdCRT
