import GowersSzemeredi.Proofs16FourWalkProjection
import GowersSzemeredi.Proofs16MatchedFourWalkIdentity

/-! Many walks between two endpoint sets force many exact mixed
additive column quadruples. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def mixedExactColumnQuadruples {N : Nat} [NeZero N]
    (U V : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) : Finset (Fin 4 → ZMod N) :=
  (exactColumnQuadruples (U ∪ V) T L r).filter
    (fun q => q 0 ∈ U ∧ q 2 ∈ U ∧ q 1 ∈ V ∧ q 3 ∈ V)

/-- Matched walk endpoints satisfy the mixed exact column relation. -/
theorem fourWalk_endpoints_subset_mixed_exact {N d : Nat} [NeZero N] [Fact N.Prime]
    (X U V : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (E : Finset (ZMod N × ZMod N))
    {rho r : Real} (hrho : 0 < rho) (hr : 0 < r) (hrle : r ≤ rho)
    (hT : ∀ x ∈ X, (T x).card ≤ d)
    (hL : ∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x))
    (hzero : ∀ x ∈ X, L x 0 = 0) (hEX : E ⊆ X ×ˢ X)
    (hcoh : ∀ p ∈ E, ∀ q ∈ E, p.1-p.2 = q.1-q.2 → ColumnPairIdentity T L r p q)
    (hN : refinementKernelCap (4*d) (6*d) rho r < N) :
    (fourWalkCollisions (fourWalkFamily E U V)).image fourWalkEndpointTuple ⊆
      mixedExactColumnQuadruples U V T L (refinementKernelRadius (4*d) (6*d) rho r) := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hpW, hsteps⟩ := Finset.mem_filter.mp hp
  obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hpW
  have h1 : (p.1.1.1 ∈ U ∧ p.1.1.2 ∈ V) ∧
      p.1.2 ∈ graphFourWalks (fun a b => (a,b) ∈ E) p.1.1.1 p.1.1.2 := by
    simpa only [fourWalkFamily, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] using hp1
  have h2 : (p.2.1.1 ∈ U ∧ p.2.1.2 ∈ V) ∧
      p.2.2 ∈ graphFourWalks (fun a b => (a,b) ∈ E) p.2.1.1 p.2.1.2 := by
    simpa only [fourWalkFamily, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] using hp2
  have hrel := matched_four_walk_relation X T L E hrho hr hrle hT hL hzero hEX hcoh h1.2 h2.2 hsteps hN
  have hrel' : ColumnPairRelated (U ∪ V) T L (refinementKernelRadius (4*d) (6*d) rho r)
      (p.1.1.1,p.2.1.1) (p.1.1.2,p.2.1.2) :=
    ⟨⟨Finset.mem_union_left _ h1.1.1,Finset.mem_union_left _ h2.1.1⟩,
      ⟨Finset.mem_union_right _ h1.1.2,Finset.mem_union_right _ h2.1.2⟩,hrel.2.2⟩
  refine Finset.mem_filter.mpr ⟨(columnPairRelated_iff_exact _ _ _ _ _ _).mp hrel', ?_⟩
  exact ⟨h1.1.1,h2.1.1,h2.1.2,h1.1.2⟩

/-- Walk density yields additive richness in arbitrary two endpoint sets.
The endpoint identity radius and modulus cost are independent of the
endpoint densities. -/
theorem mixed_exact_quadruples_of_many_walks {N d : Nat} [NeZero N] [Fact N.Prime]
    (X U V : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (E : Finset (ZMod N × ZMod N))
    {rho r beta1 beta2 eta : Real} (hrho : 0 < rho) (hr : 0 < r) (hrle : r ≤ rho)
    (hb1 : 0 ≤ beta1) (hb2 : 0 ≤ beta2) (heta : 0 ≤ eta)
    (hU : beta1*N ≤ (U.card : Real)) (hV : beta2*N ≤ (V.card : Real))
    (hwalk : ∀ u ∈ U, ∀ v ∈ V, eta*(N : Real)^3 ≤
      ((graphFourWalks (fun a b => (a,b) ∈ E) u v).card : Real))
    (hT : ∀ x ∈ X, (T x).card ≤ d)
    (hL : ∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x))
    (hzero : ∀ x ∈ X, L x 0 = 0) (hEX : E ⊆ X ×ˢ X)
    (hcoh : ∀ p ∈ E, ∀ q ∈ E, p.1-p.2 = q.1-q.2 → ColumnPairIdentity T L r p q)
    (hN : refinementKernelCap (4*d) (6*d) rho r < N) :
    (beta1*beta2*eta)^2*(N : Real)^3 ≤
      ((mixedExactColumnQuadruples U V T L (refinementKernelRadius (4*d) (6*d) rho r)).card : Real) := by
  have hprod := mul_le_mul hU hV (by positivity) (Nat.cast_nonneg U.card)
  have hmass : (beta1*beta2*eta)*(N : Real)^5 ≤ (fourWalkFamily E U V).card := by
    have h := mul_le_mul_of_nonneg_right hprod (show 0 ≤ eta*(N : Real)^3 by positivity)
    have hw := fourWalkFamily_mass E U V hwalk
    nlinarith [h]
  have hcount := fourWalk_endpoint_density (fourWalkFamily E U V) (by positivity : 0 ≤ beta1*beta2*eta) hmass
  exact hcount.trans (Nat.cast_le.mpr (Finset.card_le_card
    (fourWalk_endpoints_subset_mixed_exact X U V T L E hrho hr hrle hT hL hzero hEX hcoh hN)))

end LeanProofs.GowersSzemeredi
