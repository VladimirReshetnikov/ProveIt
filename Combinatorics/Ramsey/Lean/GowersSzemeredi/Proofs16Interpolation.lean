import GowersSzemeredi.Proofs16FibreCovers

/-! # Two-anchor interpolation for the lifting step of Lemma 16.10

These results require distinct anchors explicitly. They do not assert the
sampling estimate or the final quantitative comparison in Lemma 16.10.

`section16TwoAnchorLift_cover`, `section16TwoAnchorLift_eq` and
`section16_sampled_slice_cover` are in `Proofs16InterpolationSide`, outside the
final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem IsMultilinear.add {N k : Nat} {f g : Point N k → ZMod N}
    (hf : IsMultilinear f) (hg : IsMultilinear g) :
    IsMultilinear (fun x => f x + g x) := by
  obtain ⟨cf, hf⟩ := hf
  obtain ⟨cg, hg⟩ := hg
  refine ⟨fun e => cf e + cg e, ?_⟩
  intro x
  dsimp only
  rw [hf, hg]
  simp only [add_mul, Finset.sum_add_distrib]

theorem IsMultilinear.const_mul {N k : Nat} {f : Point N k → ZMod N}
    (hf : IsMultilinear f) (a : ZMod N) :
    IsMultilinear (fun x => a * f x) := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨fun e => a * c e, ?_⟩
  intro x
  dsimp only
  rw [hc, Finset.mul_sum]
  simp only [mul_assoc]

/-- A multilinear function remains multilinear when an unused last
coordinate is added. -/
theorem IsMultilinear.lift_last {N k : Nat} {f : Point N k → ZMod N}
    (hf : IsMultilinear f) : IsMultilinear (fun z => f (Fin.init z)) := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨fun e => if e (Fin.last k) then 0 else c (Fin.init e), ?_⟩
  intro z
  dsimp only
  rw [hc]
  rw [← (Fin.snocEquiv (fun _ : Fin (k + 1) => Bool)).sum_comp,
    Fintype.sum_prod_type]
  simp [Fin.snocEquiv, Fin.prod_univ_castSucc, Fin.init]

/-- The interpolant uses the two endpoint functions together, with no
independent choice of a slope cover and an intercept cover. -/
def section16TwoAnchorLift {N k : Nat} (a b : ZMod N)
    (f g : Point N k → ZMod N) (z : Point N (k + 1)) : ZMod N :=
  (a - b)⁻¹ *
    ((f (Fin.init z) + (-1) * g (Fin.init z)) * z (Fin.last k) +
      ((-b) * f (Fin.init z) + a * g (Fin.init z)))

theorem section16TwoAnchorLift_multilinear {N k : Nat} (a b : ZMod N)
    {f g : Point N k → ZMod N} (hf : IsMultilinear f) (hg : IsMultilinear g) :
    IsMultilinear (section16TwoAnchorLift a b f g) := by
  exact (((hf.add (hg.const_mul (-1))).mul_last_coordinate).add
    (((hf.const_mul (-b)).add (hg.const_mul a)).lift_last)).const_mul (a - b)⁻¹

/-- Two distinct values of an affine map determine its value everywhere
on its affine domain. -/
theorem LinearOn.two_anchor_interpolation {N : Nat} [Fact N.Prime]
    {A : Finset (ZMod N)} {f : ZMod N → ZMod N} (hf : LinearOn A f)
    {a b x : ZMod N} (ha : a ∈ A) (hb : b ∈ A) (hx : x ∈ A) (hab : a ≠ b) :
    f x = (a - b)⁻¹ * ((f a + (-1) * f b) * x + ((-b) * f a + a * f b)) := by
  obtain ⟨c, d, hf⟩ := hf
  rw [hf a ha, hf b hb, hf x hx]
  have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
  field_simp
  ring

end LeanProofs.GowersSzemeredi
