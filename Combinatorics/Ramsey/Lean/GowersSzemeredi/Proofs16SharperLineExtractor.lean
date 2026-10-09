import GowersSzemeredi.Proofs16LineFreimanUnconditional
import GowersSzemeredi.Proofs16LineExtractor

/-! Retaining the actual line density in Corollary 7.6 improves the
polynomial line extractor. This is an explicit local bound improvement;
it does not assert a new final Szemeredi threshold. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The line-density factor retained from Corollary 7.6. -/
def section16SharperLineMass (gamma beta : Real) : Real :=
  (2 : Real)^(-(1882 : Real)) * gamma^9312 * beta^1165

theorem section16SharperLineMass_pos {gamma beta : Real}
    (hg : 0 < gamma) (hb : 0 < beta) : 0 < section16SharperLineMass gamma beta := by
  unfold section16SharperLineMass
  positivity

/-- Use the product-property energy at the actual density of the line,
without discarding the density factor in Corollary 7.6. -/
theorem lineExtractor_sharper : LineExtractor section16SharperLineMass := by
  classical
  refine ⟨fun gamma beta hg _ hb => section16SharperLineMass_pos hg hb, ?_⟩
  intro N _ _ gamma hg hg1 R f beta hb hR hLP
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let alpha : Real := (R.card : Real) / N
  have hba : beta ≤ alpha := (le_div_iff₀ hNR).mpr hR
  have ha : 0 < alpha := hb.trans_le hba
  have hcard : (R.card : Real) = alpha * N := by
    dsimp only [alpha]
    field_simp
  have henergy := hLP 1 R (fun _ => 1) (fun _ => Finset.Subset.refl R) (fun _ => zero_le_one)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at henergy
  rw [energy_eq_phiAdditiveCount] at henergy
  have hcount : (gamma^8 * alpha) * (alpha * N)^3 ≤ phiAdditiveCount R f := by
    convert henergy using 1
    rw [hcard]
    field_simp
  obtain ⟨S, hSR, hS, hF⟩ := corollary_7_6_holds N R f alpha (gamma^8 * alpha)
    (Fact.out : N.Prime) ha (mul_pos (pow_pos hg 8) ha) hcard hcount
  refine ⟨S, hSR, ?_, ?_⟩
  · have hpow : beta^1165 ≤ alpha^1165 := pow_le_pow_left₀ hb.le hba 1165
    calc
      section16SharperLineMass gamma beta * N ≤
          (2 : Real)^(-(1882 : Real)) * gamma^9312 * alpha^1165 * N := by
        unfold section16SharperLineMass
        gcongr
      _ = (2 : Real)^(-(1882 : Real)) * (gamma^8 * alpha)^1164 * alpha * N := by
        rw [mul_pow, ← pow_mul]
        norm_num only [Nat.reduceMul]
        rw [show 1165 = 1164 + 1 by rfl, pow_succ]
        ring
      _ ≤ S.card := hS
  · intro y1 y2 y3 y4 h1 h2 h3 h4 hsum
    exact (hF.mono (by norm_num : 2 ≤ 8)).add_eq_add
      (by exact_mod_cast h1) (by exact_mod_cast h2) (by exact_mod_cast h3) (by exact_mod_cast h4) hsum

/-- The sharper extractor dominates the earlier conservative polynomial
on the complete density range used in the construction. -/
theorem lemma163Alpha_le_sharperLineMass {gamma beta : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hb : 0 < beta) (hb1 : beta ≤ 1) :
    BaseCase.lemma163Alpha gamma beta ≤ section16SharperLineMass gamma beta := by
  have hconstant : (2 : Real)^(-(2000 : Real)) ≤ (2 : Real)^(-(1882 : Real)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hgpow : gamma^10000 ≤ gamma^9312 := pow_le_pow_of_le_one hg.le hg1 (by norm_num)
  have hbpow : beta^10000 ≤ beta^1165 := pow_le_pow_of_le_one hb.le hb1 (by norm_num)
  unfold BaseCase.lemma163Alpha section16SharperLineMass
  rw [mul_pow, ← mul_assoc]
  exact mul_le_mul (mul_le_mul hconstant hgpow (by positivity) (by positivity)) hbpow
    (by positivity) (by positivity)

/-- The improved polynomial controls an actual bihomomorphism extraction. -/
theorem densePiece_sharper : DenseBihomPiece (densePieceMassGen section16SharperLineMass) :=
  densePiece_of_lineExtractor lineExtractor_sharper

theorem section16SharperLineMass_le_one {gamma beta : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hb : 0 < beta) (hb1 : beta ≤ 1) :
    section16SharperLineMass gamma beta ≤ 1 := by
  have hconst : (2 : Real)^(-(1882 : Real)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  exact mul_le_one₀ (mul_le_one₀ hconst (by positivity) (pow_le_one₀ hg.le hg1))
    (by positivity) (pow_le_one₀ hb.le hb1)

/-- Retaining line density improves the two-pass extraction mass. -/
theorem densePieceMassGen_le_sharper {gamma theta : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    densePieceMassGen (fun g b => BaseCase.lemma163Alpha g b) gamma theta ≤
      densePieceMassGen section16SharperLineMass gamma theta := by
  let a := BaseCase.lemma163Alpha gamma (theta / 2) * theta / 2 / 2
  let b := section16SharperLineMass gamma (theta / 2) * theta / 2 / 2
  have ha : 0 < a := by
    have h := BaseCase.lemma163Alpha_pos hg (by positivity : 0 < theta / 2)
    exact div_pos (div_pos (mul_pos h ht) (by norm_num)) (by norm_num)
  have hb : 0 < b := by
    have h := section16SharperLineMass_pos hg (by positivity : 0 < theta / 2)
    exact div_pos (div_pos (mul_pos h ht) (by norm_num)) (by norm_num)
  have hab : a ≤ b := by
    have h := lemma163Alpha_le_sharperLineMass hg hg1
      (by positivity : 0 < theta / 2) (by linarith : theta / 2 ≤ 1)
    exact div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h ht.le) (by norm_num)) (by norm_num)
  have hb1 : b ≤ 1 := by
    have h := section16SharperLineMass_le_one hg hg1
      (by positivity : 0 < theta / 2) (by linarith : theta / 2 ≤ 1)
    have hprod := mul_le_one₀ h ht.le ht1
    dsimp only [b]
    linarith
  have houter : BaseCase.lemma163Alpha gamma a ≤ section16SharperLineMass gamma b := by
    apply (lemma163Alpha_le_sharperLineMass hg hg1 ha (hab.trans hb1)).trans
    unfold section16SharperLineMass
    gcongr
  change BaseCase.lemma163Alpha gamma a * a ≤ section16SharperLineMass gamma b * b
  exact mul_le_mul houter hab ha.le (section16SharperLineMass_pos hg hb).le

/-- The improved extraction needs no more bihomomorphism pieces. -/
theorem bihomFamilySize_sharper_le {gamma theta : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    bihomFamilySize (densePieceMassGen section16SharperLineMass) gamma theta ≤
      bihomFamilySize (densePieceMassGen fun g b => BaseCase.lemma163Alpha g b) gamma theta := by
  have hm := (densePiece_polynomial gamma theta hg hg1 ht ht1).1
  have hmass := densePieceMassGen_le_sharper hg hg1 ht ht1
  unfold bihomFamilySize
  exact Nat.add_le_add_right (Nat.ceil_mono
    (div_le_div_of_nonneg_left (by positivity) hm hmass)) 1

end LeanProofs.GowersSzemeredi
