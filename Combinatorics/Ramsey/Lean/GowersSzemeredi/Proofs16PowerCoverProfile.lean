import GowersSzemeredi.Proofs16PowerCoverTransport
import GowersSzemeredi.Proofs16GoodGraphGeometry
import GowersSzemeredi.Proofs16ContextualPowerCover
import GowersSzemeredi.Proofs16LargePieceMass

/-! The actual contextual lift supplies a uniform cover profile for one
large subrelation. Its graph budget, power, and threshold remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The proved Section 16 profile, including its minimum parent width.
This is not the source's unit-parameter multiple-linearity predicate. -/
def Section16PowerCoverProfile {N : Nat} [NeZero N] (theta gamma : Real) (k : Nat)
    (Gamma : Finset (Point N (k + 1) × ZMod N)) : Prop :=
  ∀ rho : Real, 0 < rho → rho ≤ 1 →
    let s := gamma ^ (-(2 : Int)) * multipleS ((2 : Real) ^ (-(k + 2 : Real)) * theta) gamma k
    LargeBoxMultilinearCover Gamma rho
      (section16UniformLiftGraphBudget (rho / 4) theta gamma s k)
      (section16UniformLiftExponent (rho / 4) theta gamma s k)
      (section16UniformLiftThreshold (rho / 4) theta gamma s k)

theorem Section16PowerCoverProfile.translate {N k : Nat} [NeZero N] [Fact N.Prime]
    {theta gamma : Real} {Gamma : Finset (Point N (k + 1) × ZMod N)}
    (h : Section16PowerCoverProfile theta gamma k Gamma) (t : Point N (k + 1)) :
    Section16PowerCoverProfile theta gamma k (Gamma.image (fun z => (z.1 + t, z.2))) :=
  fun rho hr hr1 => (h rho hr hr1).translate t

theorem Section16CommonBaseData.power_cover_profile
    {N k : Nat} [NeZero N] [Fact N.Prime] {theta gamma : Real}
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (D : Section16CommonBaseData theta gamma B phi)
    (h : Section16StructuredPair theta gamma B phi) (hk : 1 ≤ k)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    Section16PowerCoverProfile theta gamma k
      (partialGraph (section16GoodDomain B (D.H ∩ D.J) D.Y D.x0) (section16PhiOne phi D.x0)) := by
  intro rho hr hr1
  dsimp only
  intro P hP hlarge
  obtain ⟨q, H, M, Q, mu, hq, hH, hm, hp, hproper, hw, hmu, hc⟩ :=
    D.uniform_power_cover h hk ht ht1 hg hg1 rho hr hr1 P hP hlarge
  refine ⟨M, q, H, Q, mu, hH, hm, hp, hproper, hq, hw, hmu, ?_⟩
  intro j x hx hh y hxy
  obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp hxy
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  exact hc j z hx hz hh

/-- The large piece is chosen once, independently of the requested loss
rho and the parent box. It lies in the original relation with no mass loss. -/
theorem Section16CommonBaseData.large_power_piece
    {N k : Nat} [NeZero N] [Fact N.Prime] {theta gamma : Real}
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (D : Section16CommonBaseData theta gamma B phi)
    (h : Section16StructuredPair theta gamma B phi) (hk : 1 ≤ k)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (Gamma : Finset (Point N (k + 1) × ZMod N)) (hgraph : GraphContained B phi Gamma) :
    ∃ E ⊆ Gamma, (N : Real) ^ (k + 1) / multipleS theta gamma (k + 1) ≤ E.card ∧
      Section16PowerCoverProfile theta gamma k E := by
  refine ⟨section16TranslatedGoodGraph B phi (D.H ∩ D.J) D.Y D.x0,
    section16TranslatedGoodGraph_subset Gamma B phi _ _ _ hgraph, ?_,
    (D.power_cover_profile h hk ht ht1 hg hg1).translate (appendCoordinate D.x0 0)⟩
  rw [section16TranslatedGoodGraph_card]
  exact (section16_common_base_mass_budget ht ht1 hg hg1).trans D.good_mass

end LeanProofs.GowersSzemeredi
