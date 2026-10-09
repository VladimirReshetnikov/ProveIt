import GowersSzemeredi.Proofs16FreimanVarietyUniform
import GowersSzemeredi.Proofs16DeepAgreement
import GowersSzemeredi.Proofs16CubicStructuredCover

/-! A uniform cover consequence of the deep-agreement structure hypothesis.

Rank and radius bounds give controls depending only on the density and
structure exponent. The selected graph is translated into the original
function's graph with its agreement mass preserved. The deep-agreement
structure assertion remains a hypothesis, not a new axiom or a theorem.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section16DeepVarietyCoverExponent (C p D : Nat) (c : Real) : Real :=
  let R := Nat.ceil (milicevicBound D c)
  section16CappedWidthExponent (section16FreimanVarietyExponent p (2 * R) R)
    (section16FreimanVarietyThreshold C p (2 * R) R (Real.exp (-milicevicBound D c)))

theorem section16DeepVarietyCoverExponent_pos (C D : Nat) {p : Nat} (hp : 0 < p) (c : Real) :
    0 < section16DeepVarietyCoverExponent C p D c :=
  section16CappedWidthExponent_pos (section16FreimanVarietyExponent_pos hp _ _)

/-- Deep agreement, if supplied, gives a dense piece of the original graph
with nine-map all-box controls uniform in its modulus and particular variety. -/
theorem exists_deep_variety_graph_cover :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ D : Nat, MilicevicDeepVarietyStructure D →
    ∀ (N : Nat) [NeZero N] [Fact N.Prime] (A : Finset (ZMod N × ZMod N))
      (phi : ZMod N × ZMod N → ZMod N) (c : Real),
      0 < c → c * (N : Real)^2 ≤ A.card → IsEBihomomorphism A phi {0} →
      ∃ G : Finset (Point N 2 × ZMod N),
        IsGraphOver G A phi ∧
        Real.exp (-milicevicBound D c) * (N : Real)^2 ≤ G.card ∧
        MultiplyLinearWith (fun _ => 9) (fun _ => section16DeepVarietyCoverExponent C p D c) G := by
  classical
  obtain ⟨C, p, hC, hp, hcover⟩ := exists_uniform_freiman_variety_cover
  refine ⟨C, p, hC, hp, ?_⟩
  intro D hD N _ _ A phi c hc hA hphi
  obtain ⟨Gamma, Psi, r, L, rho, s, t, Phi, hGamma, hPsi, hr, hrho, hL, hPhi, hagree⟩ :=
    hD N A phi c hc hA hphi
  let R := Nat.ceil (milicevicBound D c)
  have hGammaR : Gamma.card ≤ R := by exact_mod_cast hGamma.trans (Nat.le_ceil _)
  have hPsiR : Psi.card ≤ R := by exact_mod_cast hPsi.trans (Nat.le_ceil _)
  have hrR : r ≤ R := by exact_mod_cast hr.trans (Nat.le_ceil _)
  let E := varietyAgreement Gamma Psi L (rho / 2) A phi Phi s t
  let f : (ZMod N × ZMod N) → Point N 2 × ZMod N := fun x => (![x.1, x.2], Phi x)
  let G0 := E.image f
  have hf : Function.Injective f := by
    intro a b hab
    apply Prod.ext
    · simpa [f] using congrArg (fun z : Point N 2 × ZMod N => z.1 0) hab
    · simpa [f] using congrArg (fun z : Point N 2 × ZMod N => z.1 1) hab
  have hG0 : IsGraphOver G0 (bilinearBohrVariety Gamma Psi L (rho / 2)) Phi := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    have haV := (Finset.mem_filter.mp ha).1
    exact ⟨by simpa [f] using haV, by simp [f]⟩
  have hML := hcover N Gamma Psi r (2 * R) R L rho (Real.exp (-milicevicBound D c))
    (Real.exp_pos _) hrho (by omega) hrR hL Phi hPhi G0 hG0
  let v : Point N 2 := ![s, t]
  let shift : (Point N 2 × ZMod N) → Point N 2 × ZMod N := fun z => (z.1 + v, z.2)
  let G := G0.image shift
  have hshift : Function.Injective shift := by
    intro a b hab
    exact Prod.ext (add_right_cancel (Prod.mk.inj hab).1) (Prod.mk.inj hab).2
  refine ⟨G, ?_, ?_, hML.translate v⟩
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨_, haA, heq⟩ := Finset.mem_filter.mp ha
    exact ⟨by simpa [shift, f, v] using haA, by simpa [shift, f, v] using heq⟩
  · have hcard : G.card = E.card := by
      dsimp only [G, G0]
      rw [Finset.card_image_of_injective _ hshift, Finset.card_image_of_injective _ hf]
    rw [hcard]
    exact hagree

end LeanProofs.GowersSzemeredi
