import GowersSzemeredi.Proofs16CubicUniformPowerCover
import GowersSzemeredi.Proofs16AllScaleCoverTransfer

/-! All-box multiple multilinearity from cubic slice controls.
Package the uniform large-box affine lift and cap its exponent to cover
short boxes as well. The resulting control functions are explicit; no
comparison to the manuscript's prescribed control functions is asserted. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section16CubicLiftGraphBound (q k : Nat) (sigma theta gamma : Real) : Real :=
  9 * (section16UniformSampleCount sigma theta gamma k : Real) ^ 4 * (q : Real) ^ 2

def section16CubicLiftExponent (q k : Nat) (sigma theta gamma : Real)
    (Qd Ed : Real → Real) : Real :=
  lemma9WidthWithExponent ⌈Qd (sigma / 2)⌉₊ k sigma theta gamma (Ed (sigma / 2)) *
    cubicBaseExponent (section16UniformSampleCount sigma theta gamma k * q) sigma / 4

def section16CubicLiftThreshold (q k : Nat) (sigma theta gamma : Real)
    (Qd Ed : Real → Real) : Real :=
  section16RoundedPowerThreshold (section16Zeta theta gamma k / 2)
    (lemma9WidthWithExponent ⌈Qd (sigma / 2)⌉₊ k sigma theta gamma (Ed (sigma / 2)))
    (cubicBaseExponent (section16UniformSampleCount sigma theta gamma k * q) sigma)

theorem section16CubicLiftExponent_pos {q k : Nat} {sigma theta gamma : Real}
    {Qd Ed : Real → Real} (hq : 0 < q) (hk : 0 < k) (hs : 0 < sigma)
    (ht : 0 < theta) (hg : 0 < gamma) (hEd : 0 < Ed (sigma / 2)) :
    0 < section16CubicLiftExponent q k sigma theta gamma Qd Ed := by
  have he := lemma9WidthWithExponent_pos hk hs ht hg hEd ⌈Qd (sigma / 2)⌉₊
  have ha := cubicBaseExponent_pos
    (Nat.mul_pos (section16UniformSampleCount_pos (theta := theta) (gamma := gamma) k hs) hq) hs
  exact div_pos (mul_pos he ha) (by norm_num)

theorem Section16AllBoxLineCoversWith.cubic_large_box_profile
    {N k q : Nat} [Fact N.Prime] (hq : 0 < q)
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    {theta gamma : Real} {Qd Ed : Real → Real}
    (hline : Section16AllBoxLineCoversWith theta gamma Qd Ed B phi)
    (hslice : Section16SliceProvider B phi
      (fun r _ => ((3 * (max 1 r * q) : Nat) : Real))
      (fun r => cubicBaseExponent (max 1 r * q)))
    (hk : 0 < k) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hEd : ∀ s, 0 < s → s ≤ 1 → 0 < Ed s) :
    ∀ rho : Real, 0 < rho → rho ≤ 1 →
      LargeBoxMultilinearCover (partialGraph B phi) rho
        (section16CubicLiftGraphBound q k (rho / 4) theta gamma)
        (section16CubicLiftExponent q k (rho / 4) theta gamma Qd Ed)
        (section16CubicLiftThreshold q k (rho / 4) theta gamma Qd Ed) := by
  intro rho hrho hrho1 P hP hlarge
  have hs : 0 < rho / 4 := by positivity
  have hsHalf : 0 < rho / 4 / 2 := by positivity
  have hsHalf1 : rho / 4 / 2 ≤ 1 := by linarith
  have he := lemma9WidthWithExponent_pos hk hs ht hg (hEd _ hsHalf hsHalf1) ⌈Qd (rho / 4 / 2)⌉₊
  have ha := cubicBaseExponent_pos
    (Nat.mul_pos (section16UniformSampleCount_pos (theta := theta) (gamma := gamma) k hs) hq) hs
  obtain ⟨n, H, L, Q, mu, hn, hH, hmass, hpart, hproper, hw, hmu, hcover⟩ :=
    hline.uniform_cubic_power_cover hq hslice hk ht ht1 hg hg1 hEd hrho hrho1
      P.width P hP le_rfl
      (section16CubicLiftExponent q k (rho / 4) theta gamma Qd Ed)
      (by dsimp [section16CubicLiftExponent]; nlinarith [mul_pos he ha]) hlarge
  refine ⟨L, n, H, Q, mu, hH, hmass, hpart, hproper, hn, hw, hmu, ?_⟩
  intro j x hx hh y hxy
  obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp hxy
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  exact hcover j z hx hz hh

theorem partialGraph_fiber_card_le_one {N k : Nat}
    (B : Finset (Point N k)) (phi : Point N k → ZMod N) (x : Point N k) :
    ((partialGraph B phi).filter fun z => z.1 = x).card ≤ 1 := by
  classical
  have hsub : (partialGraph B phi).filter (fun z => z.1 = x) ⊆ {(x, phi x)} := by
    intro z hz
    obtain ⟨hz, hx⟩ := Finset.mem_filter.mp hz
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
    change y = x at hx
    subst y
    simp
  simpa using Finset.card_le_card hsub

/-- The cubic affine lift gives explicit multiple-linearity controls on
all proper boxes, including boxes below the large-box threshold. -/
theorem Section16AllBoxLineCoversWith.cubic_multiplyLinearWith
    {N k q : Nat} [Fact N.Prime] (hq : 0 < q)
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    {theta gamma : Real} {Qd Ed : Real → Real}
    (hline : Section16AllBoxLineCoversWith theta gamma Qd Ed B phi)
    (hslice : Section16SliceProvider B phi
      (fun r _ => ((3 * (max 1 r * q) : Nat) : Real))
      (fun r => cubicBaseExponent (max 1 r * q)))
    (hk : 0 < k) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hEd : ∀ s, 0 < s → s ≤ 1 → 0 < Ed s) :
    MultiplyLinearWith
      (fun rho => max (section16CubicLiftGraphBound q k (rho / 4) theta gamma)
        ((3 ^ (k + 1) : Nat) : Real))
      (fun rho => section16CappedWidthExponent
        (section16CubicLiftExponent q k (rho / 4) theta gamma Qd Ed)
        (section16CubicLiftThreshold q k (rho / 4) theta gamma Qd Ed))
      (partialGraph B phi) := by
  have hpos (rho : Real) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
      0 < section16CubicLiftExponent q k (rho / 4) theta gamma Qd Ed :=
    section16CubicLiftExponent_pos hq hk (by positivity) ht hg
      (hEd _ (by positivity) (by linarith))
  simpa only [Nat.mul_one] using
    multiplyLinearWith_of_large_box_covers (by omega : 0 < k + 1) 1
      (partialGraph_fiber_card_le_one B phi)
      (fun rho => section16CubicLiftGraphBound q k (rho / 4) theta gamma)
      (fun rho => section16CubicLiftExponent q k (rho / 4) theta gamma Qd Ed)
      (fun rho => section16CubicLiftThreshold q k (rho / 4) theta gamma Qd Ed) hpos
      (hline.cubic_large_box_profile hq hslice hk ht ht1 hg hg1 hEd)

end LeanProofs.GowersSzemeredi
