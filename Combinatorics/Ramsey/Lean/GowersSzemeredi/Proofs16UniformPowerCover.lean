import GowersSzemeredi.Proofs16UniformLiftControls

/-! A valid power-width version of the Section 16 affine lift. Both the
graph budget and the positive width exponent are uniform in the parent
box and modulus. The starting width is an explicit finite expression. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The two proved cover premises yield a uniformly bounded collection of
multilinear graphs on boxes of width at least m^e. This retains the actual
quantitative losses; it does not assert the refuted unit-parameter bound. -/
theorem Section16AllBoxLineCovers.uniform_power_cover_of_exponent {N k : Nat} [Fact N.Prime]
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    {theta gamma s : Real}
    (hline : Section16AllBoxLineCovers theta gamma B phi)
    (hsections : FinalCoordinateSectionsMultiplyLinear gamma s B phi)
    (hk : 0 < k) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hs : 1 ≤ s)
    {rho : Real} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (m : Nat) (P : Box N (k + 1)) (hP : P.IsProper) (hm : m ≤ P.width)
    {b : Real} (hb : b < 2 * section16UniformLiftExponent (rho / 4) theta gamma s k)
    (hlarge : section16UniformLiftExponentThreshold (rho / 4) theta gamma s k b ≤ (m : Real)) :
    ∃ (n : Nat) (H : Finset (Point N (k + 1))) (L : Nat)
      (Q : Fin L → Box N (k + 1)) (mu : Fin L → Fin n → Point N (k + 1) → ZMod N),
      (n : Real) ≤ section16UniformLiftGraphBudget (rho / 4) theta gamma s k ∧
      H ⊆ P.carrier ∧ (1 - rho) * (P.carrier.card : Real) ≤ H.card ∧
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
      (∀ j, (m : Real) ^ b ≤ (Q j).width) ∧
      (∀ j i, IsMultilinear (mu j i)) ∧
      ∀ j z, z ∈ (Q j).carrier → z ∈ B → z ∈ H → ∃ i, phi z = mu j i z := by
  let sigma := rho / 4
  have hσ : 0 < sigma := by dsimp [sigma]; positivity
  have hσ1 : sigma ≤ 1 := by dsimp [sigma]; linarith only [hrho1]
  have hm1 : 1 ≤ m := by
    have h : (1 : Real) ≤ section16UniformLiftExponentThreshold (rho / 4) theta gamma s k b :=
      (positivePowerThreshold_one_le _ _ _).trans (le_max_left _ _)
    exact_mod_cast h.trans hlarge
  obtain ⟨qG, qD, hqG, hqD, n, H, L, Q, mu, hn, hH, hmass, hpart, hproper, hw, hmu, hcover⟩ :=
    hline.explicit_multilinear_cover hsections hk hg hg1 hs hrho hrho1 m P hP hm
  obtain ⟨ha, hn'⟩ := section16_uniform_lift_controls hσ hσ1 hg hg1 hs hqG
  refine ⟨n, H, L, Q, mu, hn.trans hn', hH, hmass, hpart, hproper, ?_, hmu, hcover⟩
  have he := section16LineWidthExponent_pos hk hσ ht ht1 hg hg1
    (section16UniformDeltaCount sigma theta gamma k)
  have ha0 := section16UniformSliceExponent_pos (theta := theta) k hσ hg (zero_lt_one.trans_le hs)
  have hz : 0 < section16Zeta theta gamma k / 2 := by unfold section16Zeta; positivity
  have hb' : b < section16LineWidthExponent (section16UniformDeltaCount sigma theta gamma k) k sigma theta gamma *
      section16UniformSliceExponent sigma theta gamma s k / 2 := by
    change b < 2 * (_ * _ / 4) at hb
    nlinarith only [hb]
  obtain ⟨hbase, hpower⟩ := section16_rounded_power_width_of_exponent hz he ha0 hb'
    (section16_uniform_line_width hm1 hqD) hlarge
  intro j
  exact hpower.trans ((div_le_div_of_nonneg_right
    (Real.sqrt_le_sqrt (Real.rpow_le_rpow_of_exponent_le hbase ha)) (by norm_num)).trans (hw j))
/-- A fixed positive exponent for subsequent induction. The general theorem
above also allows every exponent below twice this value, with its own
explicit starting width and the same graph budget. -/
theorem Section16AllBoxLineCovers.uniform_power_cover {N k : Nat} [Fact N.Prime]
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    {theta gamma s : Real}
    (hline : Section16AllBoxLineCovers theta gamma B phi)
    (hsections : FinalCoordinateSectionsMultiplyLinear gamma s B phi)
    (hk : 0 < k) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hs : 1 ≤ s)
    {rho : Real} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (m : Nat) (P : Box N (k + 1)) (hP : P.IsProper) (hm : m ≤ P.width)
    (hlarge : section16UniformLiftThreshold (rho / 4) theta gamma s k ≤ (m : Real)) :
    ∃ (n : Nat) (H : Finset (Point N (k + 1))) (L : Nat)
      (Q : Fin L → Box N (k + 1)) (mu : Fin L → Fin n → Point N (k + 1) → ZMod N),
      (n : Real) ≤ section16UniformLiftGraphBudget (rho / 4) theta gamma s k ∧
      H ⊆ P.carrier ∧ (1 - rho) * (P.carrier.card : Real) ≤ H.card ∧
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
      (∀ j, (m : Real) ^ section16UniformLiftExponent (rho / 4) theta gamma s k ≤ (Q j).width) ∧
      (∀ j i, IsMultilinear (mu j i)) ∧
      ∀ j z, z ∈ (Q j).carrier → z ∈ B → z ∈ H → ∃ i, phi z = mu j i z := by
  have he := section16UniformLiftExponent_pos hk
    (show 0 < rho / 4 by positivity) ht ht1 hg hg1 (zero_lt_one.trans_le hs)
  exact hline.uniform_power_cover_of_exponent hsections hk ht ht1 hg hg1 hs hrho hrho1
    m P hP hm (by linarith only [he]) hlarge

end LeanProofs.GowersSzemeredi
