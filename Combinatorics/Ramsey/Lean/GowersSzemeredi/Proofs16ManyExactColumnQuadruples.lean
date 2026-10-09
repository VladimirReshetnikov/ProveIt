import GowersSzemeredi.Proofs16SharedWitnessKernel

/-! Dense witness systems have many additive index quadruples whose
column identities hold exactly on one uniform Bohr restriction. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def exactColumnQuadruples {N : Nat} [NeZero N] (X : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (rho : Real) : Finset (Fin 4 → ZMod N) :=
  Finset.univ.filter fun q => (∀ i, q i ∈ X) ∧ IsAdditiveQuadruple q ∧
    ∀ y, (∀ i, y ∈ bohr (T (q i)) rho) →
      L (q 0) y + L (q 1) y = L (q 2) y + L (q 3) y

/-- The shared-witness count transfers to exact identities, with no
additional loss in the number of index quadruples. -/
theorem exact_column_quadruples_count {N d : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
    {rho c theta : Real} (hrho : 0 < rho) (hc : 0 ≤ c) (htheta : 0 < theta)
    (hphi : IsEBihomomorphism A phi {0}) (hsys : IsColumnWitnessSystem A phi X T L W rho)
    (hT : ∀ x ∈ X, (T x).card ≤ d)
    (hL : ∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x))
    (hzero : ∀ x ∈ X, L x 0 = 0)
    (hW : ∀ x ∈ X, c * (N : Real)^4 ≤ (W x).card)
    (hN : sharedWitnessImageCap d rho theta < N) :
    c^4 * (X.card : Real)^4 ≤
      N * ((exactColumnQuadruples X T L (sharedWitnessKernelRadius d rho theta)).card : Real) +
        theta * (N : Real)^4 := by
  have hW' : ∀ x ∈ X, c * Fintype.card (Fin 4 → ZMod N) ≤ (W x).card := by
    simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow] using hW
  have hcount := many_quadruples_common_witnesses X W hc htheta.le hW'
  have hsub : (Finset.univ.filter fun q : Fin 4 → ZMod N => (∀ i, q i ∈ X) ∧
      IsAdditiveQuadruple q ∧ theta * Fintype.card (Fin 4 → ZMod N) ≤ (commonWitnesses W q).card) ⊆
      exactColumnQuadruples X T L (sharedWitnessKernelRadius d rho theta) := by
    intro q hq
    obtain ⟨_, hqX, hqadd, hw⟩ := Finset.mem_filter.mp hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqX, hqadd, ?_⟩
    apply shared_witness_uniform_identity A phi X T L W hrho htheta hphi hsys q hqX hqadd
      (fun i => hT _ (hqX i)) (fun i => hL _ (hqX i)) (fun i => hzero _ (hqX i)) _ hN
    simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow] using hw
  have hcards : ((Finset.univ.filter fun q : Fin 4 → ZMod N => (∀ i, q i ∈ X) ∧
      IsAdditiveQuadruple q ∧ theta * Fintype.card (Fin 4 → ZMod N) ≤ (commonWitnesses W q).card).card : Real) ≤
      (exactColumnQuadruples X T L (sharedWitnessKernelRadius d rho theta)).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hmul := mul_le_mul_of_nonneg_left hcards (Nat.cast_nonneg N)
  linarith only [hcount, hmul]

/-- Fix the shared-witness cutoff to obtain a positive ambient density
of exact column quadruples. -/
theorem many_exact_column_quadruples {N d : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
    {rho c beta : Real} (hrho : 0 < rho) (hc : 0 < c) (hbeta : 0 < beta)
    (hphi : IsEBihomomorphism A phi {0}) (hsys : IsColumnWitnessSystem A phi X T L W rho)
    (hT : ∀ x ∈ X, (T x).card ≤ d)
    (hL : ∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x))
    (hzero : ∀ x ∈ X, L x 0 = 0)
    (hW : ∀ x ∈ X, c * (N : Real)^4 ≤ (W x).card) (hX : beta * N ≤ X.card)
    (hN : sharedWitnessImageCap d rho (c^4 * beta^4 / 2) < N) :
    let theta := c^4 * beta^4 / 2
    0 < sharedWitnessKernelRadius d rho theta ∧
      theta * (N : Real)^3 ≤
        ((exactColumnQuadruples X T L (sharedWitnessKernelRadius d rho theta)).card : Real) := by
  let theta := c^4 * beta^4 / 2
  have ht : 0 < theta := by dsimp [theta]; positivity
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hcount := exact_column_quadruples_count A phi X T L W hrho hc.le ht hphi hsys hT hL hzero hW hN
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ beta * N) hX 4
  have hlow : c^4 * beta^4 * (N : Real)^4 ≤ c^4 * (X.card : Real)^4 := by
    simpa only [mul_pow, mul_assoc] using mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ c^4)
  refine ⟨sharedWitnessKernelRadius_pos d hrho ht, ?_⟩
  apply (mul_le_mul_iff_right₀ hn).mp
  dsimp only [theta] at hcount ⊢
  nlinarith only [hlow, hcount]

end LeanProofs.GowersSzemeredi
