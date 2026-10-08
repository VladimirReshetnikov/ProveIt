import GowersSzemeredi.Proofs16ParametricLineExponent

/-! A uniform pure-power affine cover with cubic slice controls.
All exponents, thresholds, and graph budgets depend only on the input
parameters, not on the parent box, its modulus, or the graph counts chosen
inside the line-cover proof. The concrete two-dimensional Freiman-family
provider satisfies the slice hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The parametric line cover and cubic slice provider give a uniform
power-width cover, with a quartic candidate budget and an explicit threshold.
Every exponent below half the product of the line and slice exponents is
allowed. The line-cover and slice-provider hypotheses remain explicit. -/
theorem Section16AllBoxLineCoversWith.uniform_cubic_power_cover
    {N k q : Nat} [Fact N.Prime] (hq : 0 < q)
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    {theta gamma : Real} {Qd Ed : Real → Real}
    (hline : Section16AllBoxLineCoversWith theta gamma Qd Ed B phi)
    (hslice : Section16SliceProvider B phi
      (fun r _ => ((3 * (max 1 r * q) : Nat) : Real))
      (fun r => cubicBaseExponent (max 1 r * q)))
    (hk : 0 < k) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hEd : ∀ s, 0 < s → s ≤ 1 → 0 < Ed s)
    {rho : Real} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (m : Nat) (P : Box N (k + 1)) (hP : P.IsProper) (hm : m ≤ P.width) :
    let sigma := rho / 4
    let R := section16UniformSampleCount sigma theta gamma k
    let e := lemma9WidthWithExponent ⌈Qd (sigma / 2)⌉₊ k sigma theta gamma (Ed (sigma / 2))
    let a := cubicBaseExponent (R * q) sigma
    ∀ b : Real, b < e * a / 2 →
      section16RoundedExponentThreshold (section16Zeta theta gamma k / 2) e a b ≤
        (m : Real) →
      ∃ (n : Nat) (H : Finset (Point N (k + 1))) (L : Nat)
        (Q : Fin L → Box N (k + 1)) (mu : Fin L → Fin n → Point N (k + 1) → ZMod N),
        (n : Real) ≤ 9 * (R : Real) ^ 4 * (q : Real) ^ 2 ∧
        H ⊆ P.carrier ∧ (1 - rho) * (P.carrier.card : Real) ≤ H.card ∧
        IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
        (∀ j, (m : Real) ^ b ≤ (Q j).width) ∧
        (∀ j i, IsMultilinear (mu j i)) ∧
        ∀ j z, z ∈ (Q j).carrier → z ∈ B → z ∈ H → ∃ i, phi z = mu j i z := by
  intro sigma R e a b hb hlarge
  have hs : 0 < sigma := by dsimp [sigma]; positivity
  have hs1 : sigma ≤ 1 := by dsimp [sigma]; linarith
  have hsHalf : 0 < sigma / 2 := by positivity
  have hsHalf1 : sigma / 2 ≤ 1 := by linarith
  have hR : 0 < R := section16UniformSampleCount_pos k hs
  have he : 0 < e := lemma9WidthWithExponent_pos hk hs ht hg (hEd _ hsHalf hsHalf1) _
  have ha : 0 < a := cubicBaseExponent_pos (Nat.mul_pos hR hq) hs
  have hz := (section16Zeta_pos_le_half k ht ht1 hg hg1).1
  have hzHalf : 0 < section16Zeta theta gamma k / 2 := by positivity
  have hm1 : 1 ≤ m := by
    have h := (positivePowerThreshold_one_le 16 (section16Zeta theta gamma k / 2) e).trans
      ((le_max_left _ _).trans hlarge)
    exact_mod_cast h
  obtain ⟨qG, qD, hqG, hqD, n, H, L, Q, mu, hn, hH, hmass,
      hpart, hproper, hw, hmu, hcover⟩ :=
    hline.explicit_multilinear_cover_with hslice (section16_cubic_slice_provider_ranges hq)
      hk ht ht1 hg hg1 (fun s hs hs1 => (hEd s hs hs1).le) hrho hrho1 m P hP hm
  obtain ⟨haLower, hbudget⟩ := section16_cubic_uniform_lift_controls hq hs hqG
  have hquartic :
      max (((3 * (R * q) : Nat) : Real))
        ((R.choose 2 : Real) * ((3 * (R * q) : Nat) : Real) * ((3 * (R * q) : Nat) : Real)) ≤
      9 * (R : Real) ^ 4 * (q : Real) ^ 2 := by
    have h := section16_cubic_candidate_count_le_quartic (r := R) hq
    unfold section16CompressedCandidateCount at h
    rw [show max 1 R = R from max_eq_right hR] at h
    exact_mod_cast h
  refine ⟨n, H, L, Q, mu, (hn.trans hbudget).trans hquartic,
    hH, hmass, hpart, hproper, ?_, hmu, hcover⟩
  have hqD' : qD ≤ ⌈Qd (sigma / 2)⌉₊ := by
    exact_mod_cast hqD.trans (Nat.le_ceil _)
  have hl := lemma9WidthWith_uniform_count (k := k) (sigma := sigma) (theta := theta)
    (gamma := gamma) hm1 hqD' (hEd _ hsHalf hsHalf1).le hz.le
  obtain ⟨hbase, hpower⟩ :=
    section16_rounded_power_width_of_exponent hzHalf he ha hb hl hlarge
  intro j
  exact hpower.trans ((div_le_div_of_nonneg_right
    (Real.sqrt_le_sqrt (Real.rpow_le_rpow_of_exponent_le hbase haLower))
    (by norm_num)).trans (hw j))

end LeanProofs.GowersSzemeredi
