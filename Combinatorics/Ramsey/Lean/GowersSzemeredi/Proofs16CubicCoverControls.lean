import GowersSzemeredi.Proofs16PolynomialBaseExponent

/-! Explicit cubic controls for simultaneous Freiman-family covers.
The comparison of exponents is transferred to the actual box covers,
including boxes of width zero, and to the sampled-slice provider. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-- Increase the graph bound and decrease the positive width exponent. -/
theorem MultiplyLinearWith.weaken {N k : Nat} [NeZero N]
    {Q E Q' E' : Real → Real} {Gamma : Finset (Point N k × ZMod N)}
    (h : MultiplyLinearWith Q E Gamma)
    (hQ : ∀ s, 0 < s → s ≤ 1 → Q s ≤ Q' s)
    (hEpos : ∀ s, 0 < s → s ≤ 1 → 0 < E' s)
    (hE : ∀ s, 0 < s → s ≤ 1 → E' s ≤ E s) :
    MultiplyLinearWith Q' E' Gamma := by
  intro s hs hs1 P hP
  obtain ⟨M, q, H, R, mu, hH, hmass, hpart, hproper, hq, hwidth, hmu, hcover⟩ :=
    h s hs hs1 P hP
  refine ⟨M, q, H, R, mu, hH, hmass, hpart, hproper,
    hq.trans (hQ s hs hs1), ?_, hmu, hcover⟩
  intro j
  by_cases hzero : P.width = 0
  · simp only [hzero, Nat.cast_zero, Real.zero_rpow (hEpos s hs hs1).ne']
    exact Nat.cast_nonneg _
  · have hwidth1 : (1 : Real) ≤ P.width := by
      exact_mod_cast (show 1 ≤ P.width by omega)
    exact (Real.rpow_le_rpow_of_exponent_le hwidth1 (hE s hs hs1)).trans (hwidth j)

/-- A polynomial lower control for the simultaneous base exponent. -/
def cubicBaseExponent (q : Nat) (sigma : Real) : Real :=
  (2 : Real) ^ (-(27 : Real)) * sigma ^ 3 / (q : Real) ^ 4

theorem cubicBaseExponent_pos {q : Nat} {sigma : Real} (hq : 0 < q)
    (hs : 0 < sigma) : 0 < cubicBaseExponent q sigma := by
  have hq0 : (0 : Real) < q := by exact_mod_cast hq
  unfold cubicBaseExponent
  positivity

theorem cubicBaseExponent_le_one {q : Nat} {sigma : Real} (hq : 0 < q)
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) : cubicBaseExponent q sigma ≤ 1 :=
  (polyBaseExponent_ge_cubic hq hs hs1).trans (polyBaseExponent_le_one hq hs hs1)

/-- The simultaneous Freiman cover with a purely cubic width exponent. -/
theorem section16_freiman_family_cubic_cover {N q : Nat} [NeZero N] [Fact N.Prime]
    (hq : 0 < q) (B : Fin q → Finset (Point N 1)) (phi : Fin q → Point N 1 → ZMod N)
    (hfreiman : ∀ i, FreimanHom 8 (pointOneDomain (B i)) (pointOneMap (phi i)))
    (Gamma : Finset (Point N 1 × ZMod N))
    (hcover : Gamma ⊆ section16FinsetUnion (fun i => partialGraph (B i) (phi i))) :
    MultiplyLinearWith (fun _ => ((3 * q : Nat) : Real)) (cubicBaseExponent q) Gamma := by
  apply (section16_freiman_family_poly_cover hq B phi hfreiman Gamma hcover).weaken
  · intros; simp
  · intro s hs _; exact cubicBaseExponent_pos hq hs
  · intro s hs hs1; exact polyBaseExponent_ge_cubic hq hs hs1

/-- Concrete sampled-slice covers with graph count independent of the loss
and an explicit cubic exponent. -/
theorem section16_cubic_slice_provider_of_freiman_families {N q : Nat} [Fact N.Prime]
    (hq : 0 < q) (B : Finset (Point N 2)) (phi : Point N 2 → ZMod N)
    (D : ZMod N → Fin q → Finset (Point N 1))
    (f : ZMod N → Fin q → Point N 1 → ZMod N)
    (hfreiman : ∀ t i, FreimanHom 8 (pointOneDomain (D t i)) (pointOneMap (f t i)))
    (hcover : ∀ t, partialGraph (section16FinalCoordinateSection B t)
      (section16FinalCoordinateRestriction phi t) ⊆
        section16FinsetUnion (fun i => partialGraph (D t i) (f t i))) :
    Section16SliceProvider B phi
      (fun r _ => ((3 * (max 1 r * q) : Nat) : Real))
      (fun r => cubicBaseExponent (max 1 r * q)) := by
  intro r sample
  have hp : 0 < max 1 r * q := Nat.mul_pos (by omega) hq
  apply (section16_slice_provider_of_freiman_families hq B phi D f
    hfreiman hcover r sample).weaken
  · intros; exact le_rfl
  · intro s hs _; exact cubicBaseExponent_pos hp hs
  · intro s hs hs1; exact polyBaseExponent_ge_cubic hp hs hs1

theorem section16_cubic_slice_provider_ranges {q : Nat} (hq : 0 < q) :
    Section16SliceProviderRanges
      (fun r _ => ((3 * (max 1 r * q) : Nat) : Real))
      (fun r => cubicBaseExponent (max 1 r * q)) := by
  intro r s _hr hs hs1
  have hp : 0 < max 1 r * q := Nat.mul_pos (by omega) hq
  refine ⟨?_, cubicBaseExponent_pos hp hs, cubicBaseExponent_le_one hp hs hs1⟩
  change (1 : Real) ≤ ((3 * (max 1 r * q) : Nat) : Real)
  exact_mod_cast (show 1 ≤ 3 * (max 1 r * q) by omega)

end LeanProofs.GowersSzemeredi
