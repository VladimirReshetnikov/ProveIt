import GowersSzemeredi.Proofs16VarietyCeilingFreeDecomposition

/-! The dimension-three controls with separate indices for the two scales.

The relation pieces of the variety route combine two kinds of deep structure:
* the variety family, at density `c₁ = section16VarietyExtractionDensity γ (θ/4)`;
* the spectrum, at the much smaller density
  `c₂ = section16VarietySpectrumDensity (θ/2) γ`.

With `MilicevicDeepVarietyStructure D` one index `D` serves both. A bound
function `Bnd` (the form the corpus pipeline proves) is matched by a
Milićević index chosen per density. One shared index would overshoot at
`c₁` by a factor growing like `log log(1/(θγ))` (research notes, J.5b).
This module therefore states the controls with an index `D` for the family
and `D₂` for the spectrum:
* `section16VarietyThreePieceExponent2`,
  `section16VarietyThreeCeilingFreeExponent2`;
* `MultiplyLinearWith.variety_three_ceiling_free2`.

The single-index forms are the instances `D₂ = D`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The relation-piece width exponent with family index `D` and spectrum index `D₂`. -/
def section16VarietyThreePieceExponent2 (C p Cv pv Cs ps D D₂ : Nat) (theta gamma rho : Real) :
    Real :=
  section16PolynomialVarietyThreeExponent2 C p Cv pv Cs ps D D₂
    (section16VarietyExtractionCount D gamma (theta / 4))
    (section16VarietyExtractionDensity gamma (theta / 4)) (theta / 2) gamma rho

/-- The ceiling-free width exponent with family index `D` and spectrum index `D₂`. -/
def section16VarietyThreeCeilingFreeExponent2 (C p Cv pv Cs ps D D₂ : Nat)
    (theta gamma : Real) : Real → Real :=
  section16VarietyCeilingFreeExponent C p Cv pv D
    (section16VarietyExtractionCount D gamma (theta / 4))
    (9 * section16VarietySpectrumCount D₂ (theta / 2) gamma)
    (section16VarietyExtractionDensity gamma (theta / 4)) theta gamma
    (section16PolynomialJointVarietyExponent Cs ps
      (section16VarietySpectrumCount D₂ (theta / 2) gamma) D₂
      (section16VarietySpectrumDensity (theta / 2) gamma))

/-- **The ceiling-free conversion with two indices.** -/
theorem MultiplyLinearWith.variety_three_ceiling_free2 {N C p Cv pv Cs ps D D₂ : Nat}
    [NeZero N] {theta gamma : Real} {Gamma : Finset (Point N 3 × ZMod N)}
    (h : MultiplyLinearWith (section16VarietyThreeGraphBound D theta gamma)
      (section16VarietyThreePieceExponent2 C p Cv pv Cs ps D D₂ theta gamma) Gamma)
    (hC : 2 ≤ C) (hp : 0 < p) (hCv : 2 ≤ Cv) (hpv : 0 < pv) (hCs : 2 ≤ Cs) (hps : 0 < ps)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    MultiplyLinearWith (section16VarietyThreeCeilingFreeGraphBound D theta gamma)
      (section16VarietyThreeCeilingFreeExponent2 C p Cv pv Cs ps D D₂ theta gamma) Gamma := by
  obtain ⟨hc, hc1⟩ := section16VarietyExtractionDensity_pos_le_one gamma
    (by positivity : 0 < theta / 4) (by linarith : theta / 4 ≤ 1)
  obtain ⟨hcs, hcs1⟩ := section16VarietySpectrumDensity_pos_le_one
    (by positivity : 0 < theta / 2) (by linarith : theta / 2 ≤ 1) hg hg1
  have hE := section16PolynomialJointVarietyExponent_pos Cs
    (section16VarietySpectrumCount D₂ (theta / 2) gamma) D₂ hps hcs hcs1
  have hE1 := section16PolynomialJointVarietyExponent_le_one hCs hps
    (section16VarietySpectrumCount D₂ (theta / 2) gamma) D₂ hcs hcs1
  apply MultiplyLinearWith.variety_ceiling_free_controls
    (q := 9 * section16VarietySpectrumCount D₂ (theta / 2) gamma)
    (C := C) (p := p) (Cv := Cv) (pv := pv) (D := D)
    _ hC hCv hp hpv hc hc1 ht ht1 hg hg1 hE hE1
  apply h.congr_controls
  · intro rho _ _
    rfl
  · intro rho _ _
    dsimp only [section16VarietyThreePieceExponent2, section16PolynomialVarietyThreeExponent2]
    simp only [Nat.cast_mul, Nat.cast_ofNat]

end LeanProofs.GowersSzemeredi
