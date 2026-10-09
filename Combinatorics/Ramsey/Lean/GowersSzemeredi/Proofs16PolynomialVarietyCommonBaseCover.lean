import GowersSzemeredi.Proofs16PolynomialVarietyFamilyPowerCover
import GowersSzemeredi.Proofs16PolynomialCommonBaseCover

/-! All-box common-base covers with polynomial variety-family controls.
The common-base witnesses supply the spectrum, selection, identity, and
remainder inputs. The finite family property supplies the slice provider.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section16VarietyLiftGraphBound (Q : Nat) (theta gamma rho : Real) : Real :=
  81 * (section16UniformSampleCount (rho / 4) theta gamma 2 : Real)^4 * (Q : Real)^2

def section16PolynomialVarietyLiftExponent (p Cv pv D Q : Nat) (c theta gamma : Real)
    (Qb Eb : Real → Real) (rho : Real) : Real :=
  section16PolynomialLemma9Exponent 2 p (Nat.floor (Qb (rho / 8))) (rho / 4)
    theta gamma (Eb (rho / 8)) *
      section16PolynomialJointVarietyExponent Cv pv
        (section16UniformSampleCount (rho / 4) theta gamma 2 * Q) D c / 4

def section16PolynomialVarietyLiftThreshold (C p Cv pv D Q : Nat) (c theta gamma : Real)
    (Qb Eb : Real → Real) (rho : Real) : Real :=
  section16RoundedPowerThreshold
    (section16Zeta theta gamma 2 / (4 * ((C * (Nat.floor (Qb (rho / 8)) + 1) : Nat) : Real)))
    (section16PolynomialLemma9Exponent 2 p (Nat.floor (Qb (rho / 8))) (rho / 4)
      theta gamma (Eb (rho / 8)))
    (section16PolynomialJointVarietyExponent Cv pv
      (section16UniformSampleCount (rho / 4) theta gamma 2 * Q) D c)

theorem section16PolynomialVarietyLiftExponent_pos {p Cv pv D Q : Nat}
    {c theta gamma rho : Real} {Qb Eb : Real → Real}
    (hp : 0 < p) (hpv : 0 < pv) (hc : 0 < c) (hc1 : c ≤ 1)
    (ht : 0 < theta) (hg : 0 < gamma) (hr : 0 < rho) (hE : 0 < Eb (rho / 8)) :
    0 < section16PolynomialVarietyLiftExponent p Cv pv D Q c theta gamma Qb Eb rho := by
  have he := section16PolynomialLemma9Exponent_pos (by decide : 0 < 2) hp
    (q := Nat.floor (Qb (rho / 8))) (by positivity : 0 < rho / 4) ht hg hE
  have ha := section16PolynomialJointVarietyExponent_pos Cv
    (section16UniformSampleCount (rho / 4) theta gamma 2 * Q) D hpv hc hc1
  exact div_pos (mul_pos he ha) (by norm_num)

/-- Supply the spectrum, selection, identity, and remainder inputs from
common-base geometry and extend the polynomial variety-family lift to every box. -/
theorem exists_polynomial_variety_common_base_cover :
  ∃ C p Cv pv : Nat, 2 ≤ C ∧ 0 < p ∧ 2 ≤ Cv ∧ 0 < pv ∧
  ∀ (N : Nat) [NeZero N] [Fact N.Prime],
    ∀ (theta gamma : Real), 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    ∀ (Qb Eb : Real → Real),
      (∀ s, 0 < s → s ≤ 1 → 0 ≤ Qb s ∧ 0 < Eb s ∧ Eb s ≤ 1) →
    ∀ (B : Finset (Point N 3)) (phi : Point N 3 → ZMod N)
      (data : Section16CommonBaseDataWith theta gamma Qb Eb B phi),
    Section16StructuredPair theta gamma B phi →
    ∀ (D Q : Nat) (c : Real), 0 < Q → 0 < c → c ≤ 1 →
      Section16FinalStackable Q (section16VarietyPieceClass N D c) B phi →
      MultiplyLinearWith
        (fun rho => max (section16VarietyLiftGraphBound Q theta gamma rho)
          ((3 ^ 3 : Nat) : Real))
        (fun rho => section16CappedWidthExponent
          (section16PolynomialVarietyLiftExponent p Cv pv D Q c theta gamma Qb Eb rho)
          (section16PolynomialVarietyLiftThreshold C p Cv pv D Q c theta gamma Qb Eb rho))
        (partialGraph (section16GoodDomain B (data.H ∩ data.J) data.Y data.x0)
          (section16PhiOne phi data.x0)) := by
  obtain ⟨C, p, Cv, pv, hC, hp, hCv, hpv, hcover⟩ := exists_polynomial_variety_family_power_cover
  refine ⟨C, p, Cv, pv, hC, hp, hCv, hpv, ?_⟩
  intro N _ _ theta gamma ht ht1 hg hg1 Qb Eb hQE B phi data h D Q c hQpieces hc hc1 hfamily
  have hpos (rho : Real) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
      0 < section16PolynomialVarietyLiftExponent p Cv pv D Q c theta gamma Qb Eb rho :=
    section16PolynomialVarietyLiftExponent_pos hp hpv hc hc1 ht hg hrho
      (hQE _ (by positivity) (by linarith)).2.1
  have hlargeCover : ∀ rho : Real, 0 < rho → rho ≤ 1 →
      LargeBoxMultilinearCover
        (partialGraph (section16GoodDomain B (data.H ∩ data.J) data.Y data.x0) (section16PhiOne phi data.x0)) rho
        (section16VarietyLiftGraphBound Q theta gamma rho)
        (section16PolynomialVarietyLiftExponent p Cv pv D Q c theta gamma Qb Eb rho)
        (section16PolynomialVarietyLiftThreshold C p Cv pv D Q c theta gamma Qb Eb rho) := by
    intro rho hrho hrho1 P hP hlarge
    obtain ⟨hQ, hE, hE1⟩ := hQE (rho / 8) (by positivity) (by linarith)
    have he := section16PolynomialLemma9Exponent_pos (by decide : 0 < 2) hp
      (q := Nat.floor (Qb (rho / 8))) (by positivity : 0 < rho / 4) ht hg hE
    have ha := section16PolynomialJointVarietyExponent_pos Cv
      (section16UniformSampleCount (rho / 4) theta gamma 2 * Q) D hpv hc hc1
    obtain ⟨n, E, M, S, mu, hn, hEsub, hmass, hpart, hproper, hw, hmu, hcov⟩ :=
      hcover N P.width theta gamma rho ht ht1 hg hg1 hrho hrho1 Qb Eb hQ hE hE1
        B phi data.H data.J (data.H ∩ data.J) data.Y data.phiPrime data.x0 rfl data.spectrum data.selection data.identity
        (h.good_domain_remainder_cover (by decide) ht ht1 hg hg1 (data.H ∩ data.J) data.Y data.x0)
        D Q c hQpieces hc hc1 hfamily P hP le_rfl
        (section16PolynomialVarietyLiftExponent p Cv pv D Q c theta gamma Qb Eb rho)
        (by
          dsimp only [section16PolynomialVarietyLiftExponent, section16PolynomialLemma9Exponent] at he ⊢
          nlinarith [mul_pos he ha]) hlarge
    refine ⟨M, n, E, S, mu, hEsub, hmass, hpart, hproper, hn, hw, hmu, ?_⟩
    intro j x hx hh y hxy
    obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp hxy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact hcov j z hx hz hh
  simpa only [Nat.mul_one] using
    multiplyLinearWith_of_large_box_covers (by omega : 0 < 3) 1
      (partialGraph_fiber_card_le_one _ _)
      (fun rho => section16VarietyLiftGraphBound Q theta gamma rho)
      (fun rho => section16PolynomialVarietyLiftExponent p Cv pv D Q c theta gamma Qb Eb rho)
      (fun rho => section16PolynomialVarietyLiftThreshold C p Cv pv D Q c theta gamma Qb Eb rho)
      hpos hlargeCover

end LeanProofs.GowersSzemeredi
