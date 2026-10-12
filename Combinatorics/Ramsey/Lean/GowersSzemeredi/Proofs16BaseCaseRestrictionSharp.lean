import GowersSzemeredi.Proofs16BaseCaseRestriction

/-! **Lemma 16.3's restriction at the density its proof gives** (Notes L.16f).

`section16_product_restriction` extracts an order-eight Freiman piece of
density `lemma163Alpha γ θ = 2^(−2000)·(γθ)^10000`. The proof (Corollary 7.6
with energy `γ^8·β`, `β ≥ θ`) gives `2^(−1882)·(γ^8 β)^1164·β`, which is at
least `lemma163AlphaSharp γ θ = 2^(−1882)·γ^9312·θ^1165`. The printed
density rounds this down (`lemma163Alpha_le_sharp`).
* `section16_product_restriction_sharp`: the restriction at
  `lemma163AlphaSharp`; the printed lemma follows by monotonicity
  (`section16_product_restriction_of_sharp`).

In the dimension-two counts of the Fejér route θ is the piece budget, so
the sharp exponent `1165` in place of `10000` would lower the dimension-two
seed from about `2^46` to about `2^43` (Notes L.16f); no headline constant
changes. -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi.BaseCase

/-- The density of Lemma 16.3's restriction, as its proof gives it. -/
def lemma163AlphaSharp (gamma theta : Real) : Real :=
  (2 : Real) ^ (-(1882 : Real)) * gamma ^ (9312 : Nat) * theta ^ (1165 : Nat)

/-- The printed density is at most the sharp one. -/
lemma lemma163Alpha_le_sharp {gamma theta : Real} (hg : 0 ≤ gamma) (hg1 : gamma ≤ 1)
    (ht : 0 ≤ theta) (ht1 : theta ≤ 1) : lemma163Alpha gamma theta ≤ lemma163AlphaSharp gamma theta := by
  unfold lemma163Alpha lemma163AlphaSharp
  have h2 : (2 : Real) ^ (-(2000 : Real)) ≤ (2 : Real) ^ (-(1882 : Real)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hgp : gamma ^ (10000 : Nat) ≤ gamma ^ (9312 : Nat) := pow_le_pow_of_le_one hg hg1 (by norm_num)
  have htp : theta ^ (10000 : Nat) ≤ theta ^ (1165 : Nat) := pow_le_pow_of_le_one ht ht1 (by norm_num)
  rw [mul_pow, ← mul_assoc]
  have h0 : (0 : Real) ≤ (2 : Real) ^ (-(2000 : Real)) := Real.rpow_nonneg (by norm_num) _
  calc (2 : Real) ^ (-(2000 : Real)) * gamma ^ (10000 : Nat) * theta ^ (10000 : Nat)
      ≤ (2 : Real) ^ (-(1882 : Real)) * gamma ^ (9312 : Nat) * theta ^ (1165 : Nat) := by
        gcongr

lemma section16_product_restriction_sharp {N : Nat} [NeZero N]
    (gamma theta : Real) (hgamma : 0 < gamma) (hgammaOne : gamma ≤ 1)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1)
    (hprime : N.Prime) (Gamma : Finset (Point N 1 × ZMod N))
    (hrelation : RelationProductProperty gamma Gamma)
    (B : Finset (Point N 1)) (phi : Point N 1 → ZMod N)
    (hBlarge : theta * N ≤ B.card)
    (hgraph : GraphContained B phi Gamma) :
    ∃ C : BaseCandidate N, IsBaseCandidate Gamma (lemma163AlphaSharp gamma theta) C := by
  classical
  let beta : Real := (B.card : Real) / N
  have hNposNat : 0 < N := NeZero.pos N
  have hNpos : (0 : Real) < N := by exact_mod_cast hNposNat
  have hbeta : 0 < beta := by
    dsimp only [beta]
    have hBpos : (0 : Real) < B.card :=
      (mul_pos htheta hNpos).trans_le hBlarge
    positivity
  have hbetaLower : theta ≤ beta := by
    dsimp only [beta]
    exact (le_div_iff₀ hNpos).2 hBlarge
  have hBcard : (B.card : Real) = beta * N := by
    dsimp only [beta]
    field_simp [hNpos.ne']
  have hproduct := hrelation B phi hgraph
  have hadd0 := productProperty_one_additive gamma B phi hproduct
  have hadd :
      (gamma ^ (8 : Nat) * beta) * (beta * N) ^ 3 ≤
        phiAdditiveCount (pointOneDomain B) (pointOneMap phi) := by
    calc
      (gamma ^ (8 : Nat) * beta) * (beta * N) ^ 3 =
          gamma ^ (8 : Nat) * (N : Real)⁻¹ * (B.card : Real) ^ 4 := by
        rw [hBcard]
        field_simp [hNpos.ne']
      _ ≤ _ := hadd0
  obtain ⟨A, hAB, hAsize, hAfreiman⟩ :=
    corollary_7_6_holds N (pointOneDomain B) (pointOneMap phi) beta
      (gamma ^ (8 : Nat) * beta) hprime hbeta
      (mul_pos (pow_pos hgamma 8) hbeta)
      (by simpa [pointOneDomain_card] using hBcard) hadd
  let B' : Finset (Point N 1) :=
    A.map (pointOneEquiv N).symm.toEmbedding
  have hB'card : B'.card = A.card := by simp [B']
  have hB'sub : B' ⊆ B := by
    intro x hx
    dsimp only [B'] at hx
    rw [Finset.mem_map] at hx
    obtain ⟨z, hzA, hzx⟩ := hx
    have hzB := (mem_pointOneDomain B z).1 (hAB hzA)
    subst x
    change (pointOneEquiv N).symm z ∈ B
    exact hzB
  have hB'graph : GraphContained B' phi Gamma := by
    intro x hx
    exact hgraph x (hB'sub hx)
  have hsize : lemma163AlphaSharp gamma theta * N ≤ B'.card := by
    rw [hB'card]
    refine le_trans ?_ hAsize
    unfold lemma163AlphaSharp
    have hthetaPow : theta ^ (1165 : Nat) ≤ beta ^ (1165 : Nat) :=
      pow_le_pow_left₀ htheta.le hbetaLower 1165
    have hg : gamma ^ (9312 : Nat) = (gamma ^ (8 : Nat)) ^ (1164 : Nat) := by
      rw [← pow_mul]
    have hb : beta ^ (1165 : Nat) = beta ^ (1164 : Nat) * beta := pow_succ beta 1164
    have h2 : (0 : Real) ≤ (2 : Real) ^ (-(1882 : Real)) := Real.rpow_nonneg (by norm_num) _
    calc (2 : Real) ^ (-(1882 : Real)) * gamma ^ (9312 : Nat) * theta ^ (1165 : Nat) * N
        ≤ (2 : Real) ^ (-(1882 : Real)) * gamma ^ (9312 : Nat) * beta ^ (1165 : Nat) * N := by
          gcongr
      _ = (2 : Real) ^ (-(1882 : Real)) * (gamma ^ (8 : Nat) * beta) ^ (1164 : Nat) * beta * N := by
          rw [hg, hb, mul_pow]; ring
  refine ⟨(B', phi), hsize, hB'graph, ?_⟩
  have hdomain : pointOneDomain B' = A := by
    apply Finset.Subset.antisymm
    · intro z hz
      rw [pointOneDomain, Finset.mem_map] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      dsimp only [B'] at hx
      rw [Finset.mem_map] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      simpa using ha
    · intro z hz
      rw [pointOneDomain, Finset.mem_map]
      refine ⟨(pointOneEquiv N).symm z, ?_, by simp⟩
      dsimp only [B']
      rw [Finset.mem_map]
      exact ⟨z, hz, rfl⟩
  rw [hdomain]
  exact hAfreiman


/-- The printed restriction follows from the sharp one. -/
lemma section16_product_restriction_of_sharp {N : Nat} [NeZero N]
    (gamma theta : Real) (hgamma : 0 < gamma) (hgammaOne : gamma ≤ 1)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1)
    (hprime : N.Prime) (Gamma : Finset (Point N 1 × ZMod N))
    (hrelation : RelationProductProperty gamma Gamma)
    (B : Finset (Point N 1)) (phi : Point N 1 → ZMod N)
    (hBlarge : theta * N ≤ B.card)
    (hgraph : GraphContained B phi Gamma) :
    ∃ C : BaseCandidate N, IsBaseCandidate Gamma (lemma163Alpha gamma theta) C := by
  obtain ⟨C, hC, hrest⟩ := section16_product_restriction_sharp gamma theta hgamma hgammaOne htheta
    hthetaOne hprime Gamma hrelation B phi hBlarge hgraph
  refine ⟨C, le_trans ?_ hC, hrest⟩
  exact mul_le_mul_of_nonneg_right
    (lemma163Alpha_le_sharp hgamma.le hgammaOne htheta.le hthetaOne) (Nat.cast_nonneg _)

end LeanProofs.GowersSzemeredi.BaseCase
