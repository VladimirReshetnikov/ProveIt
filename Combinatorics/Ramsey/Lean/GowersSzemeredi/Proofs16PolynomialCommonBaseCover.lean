import GowersSzemeredi.Proofs16PolynomialCubicPowerCover
import GowersSzemeredi.Proofs16PolynomialLineExponentComparison
import GowersSzemeredi.Proofs16CubicCommonBase
import GowersSzemeredi.Proofs16CubicAllScaleCover

/-! Polynomial recurrence controls for the actual common-base construction.

The large-box exponent and threshold are uniform in the modulus and graph.
Capping the exponent extends the cover to every proper box. The common-base
witness and cubic slice provider remain explicit inputs here.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section16PolynomialCubicExponent (k p q : Nat) (theta gamma : Real)
    (Qb Eb : Real → Real) (rho : Real) : Real :=
  section16PolynomialLemma9Exponent k p (Nat.floor (Qb (rho / 8))) (rho / 4)
    theta gamma (Eb (rho / 8)) *
      cubicBaseExponent (section16UniformSampleCount (rho / 4) theta gamma k * q) (rho / 4) / 4

def section16PolynomialCubicThreshold (k C p q : Nat) (theta gamma : Real)
    (Qb Eb : Real → Real) (rho : Real) : Real :=
  section16RoundedPowerThreshold
    (section16Zeta theta gamma k / (4 * ((C * (Nat.floor (Qb (rho / 8)) + 1) : Nat) : Real)))
    (section16PolynomialLemma9Exponent k p (Nat.floor (Qb (rho / 8))) (rho / 4)
      theta gamma (Eb (rho / 8)))
    (cubicBaseExponent (section16UniformSampleCount (rho / 4) theta gamma k * q) (rho / 4))

theorem section16PolynomialCubicExponent_pos {k p q : Nat} {theta gamma rho : Real}
    {Qb Eb : Real → Real} (hk : 0 < k) (hp : 0 < p) (hq : 0 < q)
    (ht : 0 < theta) (hg : 0 < gamma) (hr : 0 < rho) (hE : 0 < Eb (rho / 8)) :
    0 < section16PolynomialCubicExponent k p q theta gamma Qb Eb rho := by
  have he := section16PolynomialLemma9Exponent_pos hk hp (q := Nat.floor (Qb (rho / 8)))
    (by positivity : 0 < rho / 4) ht hg hE
  have ha := cubicBaseExponent_pos
    (Nat.mul_pos (section16UniformSampleCount_pos (theta := theta) (gamma := gamma) k
      (by positivity : 0 < rho / 4)) hq) (by positivity : 0 < rho / 4)
  exact div_pos (mul_pos he ha) (by norm_num)

/-- Supply the spectrum, selection, identity, and remainder inputs from
common-base geometry and extend the improved cubic lift to every box. -/
theorem exists_polynomial_common_base_cover (k : Nat) :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ (N : Nat) [NeZero N] [Fact N.Prime], 1 ≤ k →
    ∀ (theta gamma : Real), 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    ∀ (Qb Eb : Real → Real),
      (∀ s, 0 < s → s ≤ 1 → 0 ≤ Qb s ∧ 0 < Eb s ∧ Eb s ≤ 1) →
    ∀ (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
      (D : Section16CommonBaseDataWith theta gamma Qb Eb B phi),
    Section16StructuredPair theta gamma B phi →
    ∀ q : Nat, 0 < q →
      Section16SliceProvider (section16GoodDomain B (D.H ∩ D.J) D.Y D.x0)
        (section16PhiOne phi D.x0)
        (fun t _ => ((3 * (max 1 t * q) : Nat) : Real))
        (fun t => cubicBaseExponent (max 1 t * q)) →
      MultiplyLinearWith
        (fun rho => max (section16CubicLiftGraphBound q k (rho / 4) theta gamma)
          ((3 ^ (k + 1) : Nat) : Real))
        (fun rho => section16CappedWidthExponent
          (section16PolynomialCubicExponent k p q theta gamma Qb Eb rho)
          (section16PolynomialCubicThreshold k C p q theta gamma Qb Eb rho))
        (partialGraph (section16GoodDomain B (D.H ∩ D.J) D.Y D.x0)
          (section16PhiOne phi D.x0)) := by
  obtain ⟨C, p, hC, hp, hcover⟩ := exists_polynomial_cubic_power_cover k
  refine ⟨C, p, hC, hp, ?_⟩
  intro N _ _ hk theta gamma ht ht1 hg hg1 Qb Eb hQE B phi D h q hq hslice
  have hpos (rho : Real) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
      0 < section16PolynomialCubicExponent k p q theta gamma Qb Eb rho :=
    section16PolynomialCubicExponent_pos hk hp hq ht hg hrho
      (hQE _ (by positivity) (by linarith)).2.1
  have hlargeCover : ∀ rho : Real, 0 < rho → rho ≤ 1 →
      LargeBoxMultilinearCover
        (partialGraph (section16GoodDomain B (D.H ∩ D.J) D.Y D.x0) (section16PhiOne phi D.x0)) rho
        (section16CubicLiftGraphBound q k (rho / 4) theta gamma)
        (section16PolynomialCubicExponent k p q theta gamma Qb Eb rho)
        (section16PolynomialCubicThreshold k C p q theta gamma Qb Eb rho) := by
    intro rho hrho hrho1 P hP hlarge
    obtain ⟨hQ, hE, hE1⟩ := hQE (rho / 8) (by positivity) (by linarith)
    have he := section16PolynomialLemma9Exponent_pos hk hp
      (q := Nat.floor (Qb (rho / 8))) (by positivity : 0 < rho / 4) ht hg hE
    have ha := cubicBaseExponent_pos
      (Nat.mul_pos (section16UniformSampleCount_pos (theta := theta) (gamma := gamma) k
        (by positivity : 0 < rho / 4)) hq) (by positivity : 0 < rho / 4)
    obtain ⟨n, E, M, S, mu, hn, hEsub, hmass, hpart, hproper, hw, hmu, hcov⟩ :=
      hcover N P.width hk theta gamma rho ht ht1 hg hg1 hrho hrho1 Qb Eb hQ hE hE1
        B phi D.H D.J (D.H ∩ D.J) D.Y D.phiPrime D.x0 rfl D.spectrum D.selection D.identity
        (h.good_domain_remainder_cover hk ht ht1 hg hg1 (D.H ∩ D.J) D.Y D.x0)
        q hq hslice P hP le_rfl
        (section16PolynomialCubicExponent k p q theta gamma Qb Eb rho)
        (by
          dsimp only [section16PolynomialCubicExponent, section16PolynomialLemma9Exponent] at he ⊢
          nlinarith [mul_pos he ha]) hlarge
    refine ⟨M, n, E, S, mu, hEsub, hmass, hpart, hproper, hn, hw, hmu, ?_⟩
    intro j x hx hh y hxy
    obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp hxy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact hcov j z hx hz hh
  simpa only [Nat.mul_one] using
    multiplyLinearWith_of_large_box_covers (by omega : 0 < k + 1) 1
      (partialGraph_fiber_card_le_one _ _)
      (fun rho => section16CubicLiftGraphBound q k (rho / 4) theta gamma)
      (fun rho => section16PolynomialCubicExponent k p q theta gamma Qb Eb rho)
      (fun rho => section16PolynomialCubicThreshold k C p q theta gamma Qb Eb rho)
      hpos hlargeCover

end LeanProofs.GowersSzemeredi
