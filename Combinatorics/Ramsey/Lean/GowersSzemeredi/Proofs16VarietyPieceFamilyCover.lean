import GowersSzemeredi.Proofs16JointVarietyUniform
import GowersSzemeredi.Proofs16VarietyGreedyCover

/-! Uniform simultaneous covers of the variety-piece class.
The class records bounded structured data; their extraction remains a
separate hypothesis. Arbitrary finite families share one polynomial cover.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The common exponent for `n` pieces with the same structure budget. -/
def section16JointVarietyCoverExponent (C p n D : Nat) (c : Real) : Real :=
  let R := Nat.ceil (milicevicBound D c)
  section16CappedWidthExponent (section16FreimanVarietyExponent p (n * (2 * R)) (n * R))
    (section16FreimanVarietyThreshold C p (n * (2 * R)) (n * R) (Real.exp (-milicevicBound D c)))

theorem section16JointVarietyCoverExponent_pos (C n D : Nat) {p : Nat} (hp : 0 < p) (c : Real) :
    0 < section16JointVarietyCoverExponent C p n D c :=
  section16CappedWidthExponent_pos (section16FreimanVarietyExponent_pos hp _ _)

/-- The variety-piece class has uniform simultaneous all-box covers for
every finite family, without an extraction or oscillation-partition premise. -/
theorem exists_variety_piece_family_cover :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ (N n D : Nat) [NeZero N] [Fact N.Prime] (c : Real)
    (A : Fin n → Finset (ZMod N × ZMod N)) (phi : Fin n → ZMod N × ZMod N → ZMod N),
    (∀ i, IsVarietyPiece D c (phi i) (A i)) →
    ∀ G : Fin n → Finset (Point N 2 × ZMod N),
      (∀ i, IsGraphOver (G i) (A i) (phi i)) →
      MultiplyLinearWith (fun _ => 9 * n)
        (fun _ => section16JointVarietyCoverExponent C p n D c) (section16FinsetUnion G) := by
  classical
  obtain ⟨C, p, hC, hp, hcover⟩ := exists_uniform_joint_freiman_variety_cover
  refine ⟨C, p, hC, hp, ?_⟩
  intro N n D _ _ c A phi hpiece G hG
  choose Gamma Psi r L rho a b Phi hGamma hPsi hr hrho hL hPhi hagree using hpiece
  let R := Nat.ceil (milicevicBound D c)
  have hGammaR : ∀ i, (Gamma i).card ≤ R := fun i => by
    exact_mod_cast (hGamma i).trans (Nat.le_ceil _)
  have hPsiR : ∀ i, (Psi i).card ≤ R := fun i => by
    exact_mod_cast (hPsi i).trans (Nat.le_ceil _)
  have hrR : ∀ i, r i ≤ R := fun i => by
    exact_mod_cast (hr i).trans (Nat.le_ceil _)
  apply hcover N n (2 * R) R Gamma Psi r L rho a b (Real.exp (-milicevicBound D c))
    (Real.exp_pos _) hrho (fun i => by have := hGammaR i; have := hPsiR i; omega)
    hrR hL Phi hPhi G
  intro i z hz
  obtain ⟨hzA, hzPhi⟩ := hG i z hz
  obtain ⟨hv, heq⟩ := hagree i _ hzA
  exact ⟨(mem_shiftPairs _ _ _ _).mpr hv, hzPhi.trans heq⟩

end LeanProofs.GowersSzemeredi
