import GowersSzemeredi.Proofs16PrimeGroupSampleSelection
import GowersSzemeredi.Proofs16BohrLowerBound

/-! Claim 6.3's sampling argument for bounded-rank Bohr domains. A single
cell count supplies the density lower bound for every column domain. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem bohr_rank_density_lower {N d q : Nat} [NeZero N] [NeZero q]
    (T : Finset (ZMod N)) {tau : Real} (hT : T.card ≤ d) (hq : 1 ≤ tau*q) :
    (1/(q : Real)^d)*N ≤ ((bohr T tau).card : Real) := by
  have hq0 : (0 : Real) < q := by exact_mod_cast NeZero.pos q
  have hN := (bohr_card_lower T q hq).trans
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (NeZero.pos q) hT))
  have hNR : (N : Real) ≤ (q : Real)^d*(bohr T tau).card := by exact_mod_cast hN
  rw [one_div_mul_eq_div]
  exact (div_le_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hNR)

theorem bohr_sample_selection {N r m d q : Nat} [NeZero N] [Fact N.Prime] [NeZero q]
    (hr : 0 < r) (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    {tau : Real} (hq : 1 ≤ tau*q) (hT : ∀ x ∈ X, (T x).card ≤ d)
    {I : Type*} (Q : Finset I) (Z : I → Finset (ZMod N))
    {b eta epsilon : Real} (hb : 0 < b) (heta : 0 ≤ eta) (he : 0 < epsilon)
    (hX : b*N ≤ (X.card : Real)) (hQ : (Q.card : Real) ≤ (N : Real)^m)
    (hZ : ∀ a ∈ Q, ((Z a).card : Real) ≤ eta*N)
    (hbadBudget : 8*(3 : Real)^r*eta ≤ epsilon*b*(1/(q : Real)^d)^r)
    (hcollisionBudget : 8*(3 : Real)^r ≤ b*(1/(q : Real)^d)^r*N) :
    ∃ e : Fin r → ZMod N, Function.Injective (booleanSampleValue e) ∧
      (Finset.univ.image (booleanSampleValue e)).card = 2^r ∧
      b*(1/(q : Real)^d)^r*N/2 ≤
        ((retainedSampleIndices X (fun x => bohr (T x) tau) e).card : Real) ∧
      ((sampleBadIndices Q Z e).card : Real) ≤ epsilon*(N : Real)^m/2 := by
  have hq0 : (0 : Real) < q := by exact_mod_cast NeZero.pos q
  exact prime_group_sample_selection hr X (fun x => bohr (T x) tau) Q Z hb (by positivity) heta he
    hX (fun x hx => bohr_rank_density_lower (T x) (hT x hx) hq) hQ hZ hbadBudget hcollisionBudget

end LeanProofs.GowersSzemeredi
