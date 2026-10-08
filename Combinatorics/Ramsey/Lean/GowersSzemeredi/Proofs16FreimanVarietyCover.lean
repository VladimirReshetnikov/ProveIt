import GowersSzemeredi.Proofs16FreimanVarietyProfile
import GowersSzemeredi.Proofs16PolynomialVarietyCover

/-! All-box covers on bilinear Bohr varieties with local Freiman phases.

The two-stage partition supplies the large good cells. Coarse covers
supply small boxes. Both inputs are constructed, so no global linearity
or oscillation-partition hypothesis remains. A Freiman bihomomorphism on
the full variety is still an input; its structure-theorem existence is
not asserted here. The recurrence constants C,p remain existential.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Local Freiman coordinate maps suffice for a uniform nine-map cover
of a Freiman bihomomorphism on the deep variety, on every proper box. -/
theorem exists_freiman_variety_cover :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ (N : Nat) [NeZero N] [Fact N.Prime] (Gamma Psi : Finset (ZMod N)) (r : Nat)
    (L : Fin r → ZMod N → ZMod N) (rho : Real), 0 < rho →
    (∀ i, IsFreimanLinearOn (bohr Psi rho) (L i)) →
    ∀ Phi : ZMod N × ZMod N → ZMod N,
      IsEBihomomorphism (bilinearBohrVariety Gamma Psi L rho) Phi {0} →
    ∀ G : Finset (Point N 2 × ZMod N),
      IsGraphOver G (bilinearBohrVariety Gamma Psi L (rho / 2)) Phi →
      MultiplyLinearWith (fun _ => 9)
        (fun _ => section16CappedWidthExponent
          (section16FreimanVarietyExponent p (Gamma.card + Psi.card) r)
          (section16FreimanVarietyThreshold C p (Gamma.card + Psi.card) r rho)) G := by
  classical
  obtain ⟨C, p, hC, hp, hpartition⟩ := exists_freiman_variety_good_partition
  refine ⟨C, p, hC, hp, ?_⟩
  intro N _ _ Gamma Psi r L rho hrho hL Phi hPhi G hG
  let e := section16FreimanVarietyExponent p (Gamma.card + Psi.card) r
  let T : Real := section16FreimanVarietyThreshold C p (Gamma.card + Psi.card) r rho
  have he : 0 < e := section16FreimanVarietyExponent_pos hp _ _
  have hlargeCover : ∀ s : Real, 0 < s → s ≤ 1 → LargeBoxMultilinearCover G s 1 e T := by
    intro s hs _ P hP hlarge
    obtain ⟨M, Q, hpart, hproper, hw, hgood⟩ := hpartition N Gamma Psi r L rho hrho hL P hP (by dsimp only [T] at hlarge; exact_mod_cast hlarge)
    choose mu hmu hcov using fun j => cell_cover_of_good hPhi hG (Q j) (hgood j)
    refine ⟨M, 1, P.carrier, Q, (fun j _ => mu j), subset_rfl, ?_, hpart, hproper,
      by norm_num, hw, (fun j _ => hmu j), ?_⟩
    · nlinarith [mul_nonneg hs.le (Nat.cast_nonneg P.carrier.card : (0 : Real) ≤ P.carrier.card)]
    · intro j x hx _ y hy
      exact ⟨0, hcov j x hx y hy⟩
  have hML := multiplyLinearWith_of_large_box_covers (by decide : 0 < 2) 1
    hG.fiber_card_le_one (fun _ => 1) (fun _ => e) (fun _ => T)
    (fun _ _ _ => he) hlargeCover
  simpa only [show (3 ^ 2 * 1 : Nat) = 9 by decide, Nat.cast_ofNat,
    max_eq_right (by norm_num : (1 : Real) ≤ 9)] using hML

end LeanProofs.GowersSzemeredi
