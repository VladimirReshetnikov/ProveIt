import GowersSzemeredi.Proofs16UniformPowerCover
import GowersSzemeredi.Proofs16CommonBaseLineCovers

/-! Apply the valid power-width lift to the actual structured pair and
common-base witnesses used in the Section 16 induction. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The genuine common-base construction supplies all the inputs to a
uniform power cover of the all-ones graph. Constants and the starting width
depend only on theta, gamma, rho, and k, not on the structured pair or box.
This proves a large-box contextual lifting statement with its actual
controls, not the source's stronger unit-parameter conclusion. -/
theorem Section16CommonBaseData.uniform_power_cover
    {N k : Nat} [NeZero N] [Fact N.Prime] {theta gamma : Real}
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (D : Section16CommonBaseData theta gamma B phi)
    (h : Section16StructuredPair theta gamma B phi) (hk : 1 ≤ k)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    let s := gamma ^ (-(2 : Int)) * multipleS ((2 : Real) ^ (-(k + 2 : Real)) * theta) gamma k
    ∀ (rho : Real), 0 < rho → rho ≤ 1 →
      ∀ P : Box N (k + 1), P.IsProper →
        section16UniformLiftThreshold (rho / 4) theta gamma s k ≤ (P.width : Real) →
        ∃ (n : Nat) (H : Finset (Point N (k + 1))) (L : Nat)
          (Q : Fin L → Box N (k + 1)) (mu : Fin L → Fin n → Point N (k + 1) → ZMod N),
          (n : Real) ≤ section16UniformLiftGraphBudget (rho / 4) theta gamma s k ∧
          H ⊆ P.carrier ∧ (1 - rho) * (P.carrier.card : Real) ≤ H.card ∧
          IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
          (∀ j, (P.width : Real) ^ section16UniformLiftExponent (rho / 4) theta gamma s k ≤ (Q j).width) ∧
          (∀ j i, IsMultilinear (mu j i)) ∧
          ∀ j z, z ∈ (Q j).carrier → z ∈ section16GoodDomain B (D.H ∩ D.J) D.Y D.x0 →
            z ∈ H → ∃ i, section16PhiOne phi D.x0 z = mu j i z := by
  dsimp only
  intro rho hrho hrho1 P hP hlarge
  obtain ⟨hsections, hline⟩ := D.lifting_cover_inputs h hk ht ht1 hg hg1
  have hs := (section16_face_parameter_lift_reserve k ht ht1 hg hg1).1
  exact hline.uniform_power_cover hsections (by omega) ht ht1 hg hg1
    ((by norm_num : (1 : Real) ≤ 2).trans hs) hrho hrho1 P.width P hP le_rfl hlarge

end LeanProofs.GowersSzemeredi
