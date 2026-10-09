import GowersSzemeredi.Proofs16PolynomialVarietyProfile
import GowersSzemeredi.Proofs16AllScaleCoverTransfer

/-! All-box covers on varieties whose mixed phases are globally multilinear.

Above the polynomial threshold, good cells admit one multilinear map.
The existing coarse cover handles smaller boxes with nine maps, after
capping the positive exponent. Thus no all-box oscillation-partition
hypothesis is needed in this case. General Freiman-on-Bohr mixed phases
are not asserted to be globally multilinear.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A relation contained in a graph has at most one point in each fibre. -/
theorem IsGraphOver.fiber_card_le_one {N : Nat}
    {Gamma : Finset (Point N 2 × ZMod N)} {S : Finset (ZMod N × ZMod N)}
    {Phi : ZMod N × ZMod N → ZMod N} (h : IsGraphOver Gamma S Phi) (x : Point N 2) :
    (Gamma.filter fun z => z.1 = x).card ≤ 1 := by
  classical
  have hsub : Gamma.filter (fun z => z.1 = x) ⊆ {(x, Phi (x 0, x 1))} := by
    intro z hz
    obtain ⟨hzG, hzx⟩ := Finset.mem_filter.mp hz
    have hval := (h z hzG).2
    apply Finset.mem_singleton.mpr
    apply Prod.ext hzx
    simpa only [hzx] using hval
  simpa using Finset.card_le_card hsub

/-- A Freiman bihomomorphism on a variety with globally multilinear mixed
phases has a uniform nine-map cover of its deep graph on every proper box. -/
theorem exists_polynomial_variety_cover :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ (N : Nat) [NeZero N] [Fact N.Prime] (Gamma Psi : Finset (ZMod N)) (r : Nat)
    (L : Fin r → ZMod N → ZMod N) (rho : Real), 0 < rho →
    (∀ i, IsMultilinear (fun x : Point N 2 => L i (x 1) * x 0)) →
    ∀ Phi : ZMod N × ZMod N → ZMod N,
      IsEBihomomorphism (bilinearBohrVariety Gamma Psi L rho) Phi {0} →
    ∀ G : Finset (Point N 2 × ZMod N),
      IsGraphOver G (bilinearBohrVariety Gamma Psi L (rho / 2)) Phi →
      MultiplyLinearWith (fun _ => 9)
        (fun _ => section16CappedWidthExponent
          (section16PolynomialVarietyExponent p (Gamma.card + Psi.card + r))
          (section16PolynomialVarietyThreshold C p (Gamma.card + Psi.card + r) rho)) G := by
  classical
  obtain ⟨C, p, hC, hp, hpartition⟩ := exists_polynomial_variety_good_partition
  refine ⟨C, p, hC, hp, ?_⟩
  intro N _ _ Gamma Psi r L rho hrho hL Phi hPhi G hG
  let e := section16PolynomialVarietyExponent p (Gamma.card + Psi.card + r)
  let T : Real := section16PolynomialVarietyThreshold C p (Gamma.card + Psi.card + r) rho
  have he : 0 < e := section16PolynomialVarietyExponent_pos hp _
  have hlargeCover : ∀ s : Real, 0 < s → s ≤ 1 → LargeBoxMultilinearCover G s 1 e T := by
    intro s hs _ P hP hlarge
    obtain ⟨M, Q, hpart, hproper, hw, hgood⟩ := hpartition N Gamma Psi r L rho hrho P hP
      (fun i => ⟨_, hL i, fun _ _ => rfl⟩) (by dsimp only [T] at hlarge; exact_mod_cast hlarge)
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

/-- The mixed-phase hypothesis is discharged for affine coordinate maps. -/
theorem exists_affine_variety_cover :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ (N : Nat) [NeZero N] [Fact N.Prime] (Gamma Psi : Finset (ZMod N)) (r : Nat)
    (a b : Fin r → ZMod N) (rho : Real), 0 < rho →
    ∀ Phi : ZMod N × ZMod N → ZMod N,
      IsEBihomomorphism (bilinearBohrVariety Gamma Psi (fun i y => a i * y + b i) rho) Phi {0} →
    ∀ G : Finset (Point N 2 × ZMod N),
      IsGraphOver G (bilinearBohrVariety Gamma Psi (fun i y => a i * y + b i) (rho / 2)) Phi →
      MultiplyLinearWith (fun _ => 9)
        (fun _ => section16CappedWidthExponent
          (section16PolynomialVarietyExponent p (Gamma.card + Psi.card + r))
          (section16PolynomialVarietyThreshold C p (Gamma.card + Psi.card + r) rho)) G := by
  obtain ⟨C, p, hC, hp, hcover⟩ := exists_polynomial_variety_cover
  refine ⟨C, p, hC, hp, ?_⟩
  intro N _ _ Gamma Psi r a b rho hrho Phi hPhi G hG
  apply hcover N Gamma Psi r (fun i y => a i * y + b i) rho hrho _ Phi hPhi G hG
  intro i
  convert isMultilinear_two (N := N) 0 (b i) 0 (a i) using 1
  funext x
  ring

end LeanProofs.GowersSzemeredi
