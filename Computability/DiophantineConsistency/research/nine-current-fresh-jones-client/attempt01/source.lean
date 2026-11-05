import DiophantineConsistency.ModelNineRatio
import DiophantineConsistency.ModelNineReduce
import DiophantineConsistency.ModelJonesSyntax
import DiophantineConsistency.QuarticSyntaxFacts
import DiophantineConsistency.NineLightQuartic

/-! # Jones's nine unknowns in every model of `𝗜𝚺₁`

The internal counterpart of `Jones1982.Nine.wset_iff_nine` at input `1`:
for a seed of total degree at most four that does not vanish at
`(1, 0, …, 0)`, the nine-variable syntax `ExecutableJones.expression seed 0`
has a zero in the model iff the seed has a zero with input `1`.

The two directions follow Jones. The evaluated syntax is the combiner of a
free-quantity record (`ModelJonesSyntax`); its vanishing is Jones's four
conditions (`ModelNineConds`); once the margin bounds `g`, the record is
`ModelNineRatio.ofModel` of the packed natural code `RV`
(`ModelMaster.RV_rank`, valid for every base `b > y`), so the ratio stage
(`ModelNineRatio`) and the reduction stage (`ModelNineReduce`) apply.

Specialised to the quartic gate syntax, whose degree and normalization are
`QuarticSyntaxFacts`, this gives the generic Jones-model equivalence directly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.NineFreshJones
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing ModelArithmetic NinePolynomial ArithmeticBinomPascal
  ModelNineReduce ModelMaster ModelPacking ExecutableJones
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section Seed
variable {ν : ℕ} (seed : Expr (Fin (ν + 1)))

/-- `ModelNineReduce.sizes_of_reduced` for an arbitrary base `bN seed ε`. -/
theorem sizes' {ε g : V} (hgb : g < 4 * bN seed ε * (bN seed ε ^ 5) ^ (5 ^ ν)) :
    8 ≤ qV ν (bN seed ε) ^ 16 ∧ qV ν (bN seed ε) ^ 16 ≤ RV seed (bN seed ε) g ∧
      bN seed ε ≤ qV ν (bN seed ε) ^ 16 ∧ bN seed ε ≤ RV seed (bN seed ε) g ∧
      ι (RV seed (bN seed ε) g) =
        NinePolynomial.rankCode (1 : DiffRing V) (indexZ seed 0 : DiffRing V) (ι (bN seed ε))
          (eR seed (ι (bN seed ε))) (ι g) (lR ν (ι (bN seed ε)))
          (qR ν (ι (bN seed ε)) ^ 16) (qR ν (ι (bN seed ε)))
          (ι (bN seed ε) ^ 5 - 2 * (indexZ seed 0 : DiffRing V)) (lamR ν (ι (bN seed ε))) := by
  have hyb := y_lt_bN seed ε
  obtain ⟨hb1, hbB, -, -, -⟩ := v_base seed hyb
  obtain ⟨h9, -, -, -, -⟩ := dr_base seed hyb
  obtain ⟨hL1, -, -, -, -, -, -, -⟩ := L_facts ν
  have hB1 : 1 ≤ bN seed ε ^ 5 := le_trans hb1 hbB
  have hbq : bN seed ε ≤ qV ν (bN seed ε) := by
    rw [qV_eq]
    calc bN seed ε ≤ bN seed ε ^ 5 := hbB
      _ = (bN seed ε ^ 5) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hB1 hL1
  have hqN : qV ν (bN seed ε) ≤ qV ν (bN seed ε) ^ 16 := by
    calc qV ν (bN seed ε) = qV ν (bN seed ε) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (le_trans hb1 hbq) (by omega)
  have hbN : bN seed ε ≤ qV ν (bN seed ε) ^ 16 := le_trans hbq hqN
  have h9N : (9 : DiffRing V) ≤ ι (qV ν (bN seed ε) ^ 16) := le_trans h9 (ι_le_ι.mpr hbN)
  have hN2 : 2 ≤ qV ν (bN seed ε) ^ 16 := by
    apply ι_le_ι.mp
    rw [map_ofNat]
    linarith
  have hNR : qV ν (bN seed ε) ^ 16 ≤ RV seed (bN seed ε) g := by
    unfold RV
    exact centralCode_ge_base hN2
  refine ⟨?_, hNR, hbN, le_trans hbN hNR, RV_rank seed hyb hgb⟩
  apply ι_le_ι.mp
  rw [map_ofNat]
  linarith

/-- The evaluated record of the syntax, once `R` is identified, is `ofModel`. -/
theorem record_eq (a : Fin 9 → V)
    (hR : ι (RV seed (bN seed (a 0)) (a 1 + 1)) =
        NinePolynomial.rankCode (1 : DiffRing V) (indexZ seed 0 : DiffRing V)
          (ι (bN seed (a 0))) (eR seed (ι (bN seed (a 0)))) (ι (a 1 + 1))
          (lR ν (ι (bN seed (a 0)))) (qR ν (ι (bN seed (a 0))) ^ 16) (qR ν (ι (bN seed (a 0))))
          (ι (bN seed (a 0)) ^ 5 - 2 * (indexZ seed 0 : DiffRing V))
          (lamR ν (ι (bN seed (a 0))))) :
    ModelJonesSyntax.mapVars
        (Expr.evalRing (Fin.cons 1 (fun i => ι (a i)) : Fin 10 → DiffRing V))
        (syntaxVars seed (indexZ seed 0) (indexY seed 0)) =
      ModelNineRatio.ofModel (RV seed (bN seed (a 0)) (a 1 + 1)) (qV ν (bN seed (a 0)) ^ 16)
        (bN seed (a 0)) (a 1 + 1) (32 * bN seed (a 0) * (bN seed (a 0) ^ 5) ^ (5 ^ ν))
        (a 2 + 1) (a 3 + 1) (a 4 + 1) (a 5) (a 6 + 1) (a 7 + 1) := by
  rw [ModelJonesSyntax.mapVars_syntaxVars]
  simp only [ModelNineRatio.ofModel, hR, map_add, map_mul, map_pow, map_one, map_ofNat,
    ι_qV, ι_bN, eR, lR, lamR, qR]
  rfl

/-- The margin bounds `g` (`Jones1982.Nine.g_lt_of_marg`). -/
theorem g_lt_of_marg {K C Y g G : DiffRing V} (hG : 0 < G) (hg : 0 ≤ g)
    (h : 0 < K ^ 2 * G - 4 * (C - K * Y) ^ 2 * G - 8 * g * K ^ 2) : 8 * g < G := by
  have hK : K ≠ 0 := by
    rintro rfl
    have : 0 ≤ 4 * (C - 0 * Y) ^ 2 * G := by positivity
    nlinarith
  have hKz : 0 < K ^ 2 := lt_of_le_of_ne (sq_nonneg K) (Ne.symm (pow_ne_zero 2 hK))
  have h1 : 0 ≤ 4 * (C - K * Y) ^ 2 * G := by positivity
  have h2 : 8 * g * K ^ 2 < G * K ^ 2 := by linarith
  exact lt_of_mul_lt_mul_right h2 hKz.le

set_option maxHeartbeats 2000000 in
/-- **Jones's nine unknowns, internally** (at input `1`). -/
theorem nine_iff (hP : seed.toPolynomial.totalDegree ≤ 4)
    (hnorm : seed.eval (fun j : Fin (ν + 1) => if j = 0 then (1 : ℤ) else 0) ≠ 0) :
    (∃ a : Fin 9 → V, (ExecutableJones.expression seed 0).evalRing (fun i => ι (a i)) = 0) ↔
      ∃ w : Fin ν → V,
        seed.evalRing (fun j => ι ((Fin.cons (1 : V) w : Fin (ν + 1) → V) j)) = 0 := by
  constructor
  · rintro ⟨a, ha⟩
    rw [ModelJonesSyntax.evalRing_expression] at ha
    set W := ModelJonesSyntax.mapVars
        (Expr.evalRing (Fin.cons 1 (fun i => ι (a i)) : Fin 10 → DiffRing V))
        (syntaxVars seed (indexZ seed 0) (indexY seed 0)) with hW
    have hc : ModelNineConds.Conds W := (ModelNineConds.model_conds_iff_value W).mpr ⟨a 8, ha⟩
    -- the margin bounds `g`
    have hWg : W.g = ι (a 1 + 1) := by
      rw [hW, ModelJonesSyntax.mapVars_syntaxVars, map_add, map_one]; rfl
    have hWG : W.G = ι (32 * bN seed (a 0) * (bN seed (a 0) ^ 5) ^ (5 ^ ν)) := by
      rw [hW, ModelJonesSyntax.mapVars_syntaxVars]
      simp only [map_mul, map_pow, map_ofNat, ι_bN]
      rfl
    have hb0 : 0 < bN seed (a 0) := lt_of_le_of_lt (Arithmetic.zero_le _) (y_lt_bN seed (a 0))
    have hG0 : 0 < 32 * bN seed (a 0) * (bN seed (a 0) ^ 5) ^ (5 ^ ν) :=
      mul_pos (mul_pos (by norm_num) hb0) (pow_pos (pow_pos hb0 5) _)
    have h8 : 8 * ι (a 1 + 1) < ι (32 * bN seed (a 0) * (bN seed (a 0) ^ 5) ^ (5 ^ ν)) := by
      rw [← hWg, ← hWG]
      exact g_lt_of_marg (by rw [hWG]; exact ι_lt_ι.mpr hG0 |>.trans_eq' (map_zero ι).symm)
        (by rw [hWg]; exact ι_nonneg _) hc.2.2.2
    have hgb : a 1 + 1 < 4 * bN seed (a 0) * (bN seed (a 0) ^ 5) ^ (5 ^ ν) := by
      apply ι_lt_ι.mp
      have e : ι (32 * bN seed (a 0) * (bN seed (a 0) ^ 5) ^ (5 ^ ν)) =
          8 * ι (4 * bN seed (a 0) * (bN seed (a 0) ^ 5) ^ (5 ^ ν)) := by
        simp only [map_mul, map_pow, map_ofNat]; ring
      rw [e] at h8
      linarith
    obtain ⟨hN8, hNR, hbN, hbR, hR⟩ := sizes' seed hgb
    rw [hW, record_eq seed a hR] at hc
    have hR8 : 8 ≤ RV seed (bN seed (a 0)) (a 1 + 1) := le_trans hN8 hNR
    obtain ⟨hdvd, ⟨k, hk⟩, -⟩ := ModelNineRatio.ratio_sound hR8 hN8 hbR hb0 hbN hG0
      (by simp) (by simp) (by simp) (by simp) (by simp) hc
    have hdvd' : (qV ν (bN seed (a 0)) ^ 16) ^ 2 ∣
        binom (2 * RV seed (bN seed (a 0)) (a 1 + 1)) (RV seed (bN seed (a 0)) (a 1 + 1)) := by
      rw [sq]; exact hdvd
    exact mem_of_reduced seed hP hk hgb hdvd'
  · rintro hW
    obtain ⟨ε, g, k, hg0, hb, hgb1, hdvd⟩ := reduced_of_mem seed hP hnorm hW
    have hb0 : 0 < bN seed ε := lt_of_le_of_lt (Arithmetic.zero_le _) (y_lt_bN seed ε)
    have hgb : g < 4 * bN seed ε * (bN seed ε ^ 5) ^ (5 ^ ν) :=
      lt_of_lt_of_le hgb1 (by
        rw [mul_assoc 4]
        exact le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num))
    obtain ⟨hN8, hNR, hbN, hbR, -⟩ := sizes_of_reduced seed hb hgb
    have h32 : 32 * g < 32 * bN seed ε * (bN seed ε ^ 5) ^ (5 ^ ν) := by
      rw [mul_assoc 32]
      exact mul_lt_mul_of_pos_left hgb1 (by norm_num)
    have hdvd' : qV ν (bN seed ε) ^ 16 * qV ν (bN seed ε) ^ 16 ∣
        binom (2 * RV seed (bN seed ε) g) (RV seed (bN seed ε) g) := by
      rw [← sq]; exact hdvd
    obtain ⟨h, s, w, φ, i, j, hh, hs, hw, hi, hj, hc⟩ :=
      ModelNineRatio.ratio_complete (le_trans hN8 hNR) hN8 hbR hb0 hbN h32 hdvd' ⟨k, hb⟩
    obtain ⟨n, hn⟩ := (ModelNineConds.model_conds_iff_value _).mp hc
    have hg1 : 1 ≤ g := pos_iff_one_le.mp hg0
    refine ⟨![ε, g - 1, h - 1, s - 1, w - 1, φ, i - 1, j - 1, n], ?_⟩
    rw [ModelJonesSyntax.evalRing_expression]
    have e1 : g - 1 + 1 = g := tsub_add_cancel_of_le hg1
    have e2 : h - 1 + 1 = h := tsub_add_cancel_of_le (pos_iff_one_le.mp hh)
    have e3 : s - 1 + 1 = s := tsub_add_cancel_of_le (pos_iff_one_le.mp hs)
    have e4 : w - 1 + 1 = w := tsub_add_cancel_of_le (pos_iff_one_le.mp hw)
    have e6 : i - 1 + 1 = i := tsub_add_cancel_of_le (pos_iff_one_le.mp hi)
    have e7 : j - 1 + 1 = j := tsub_add_cancel_of_le (pos_iff_one_le.mp hj)
    have hR := (sizes' seed (ε := ε) (g := g - 1 + 1) (by rw [e1]; exact hgb)).2.2.2.2
    rw [record_eq seed ![ε, g - 1, h - 1, s - 1, w - 1, φ, i - 1, j - 1, n] hR]
    change RefinedPair.value _ _ _ _ (ι n) _ _ _ = 0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val,
      e1, e2, e3, e4, e6, e7]
    exact hn

end Seed

/-- The quartic gate syntax at input `1`, against arbitrary inputs. -/
theorem quartic_one_iff {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    (∃ w : Fin (QuarticCompiler.witnessCount p q) → V,
      (QuarticSyntax.expression p q).evalRing
        (fun j => ι ((Fin.cons (1 : V) w : Fin (QuarticCompiler.witnessCount p q + 1) → V) j)) = 0) ↔
    ∃ v : Fin (QuarticCompiler.witnessCount p q + 1) → V,
      AdaptiveEquationSyntax2011.InternalZero (QuarticSyntax.expression p q) v := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨_, (internalZero_iff _ _).mpr hw⟩
  · intro hv
    obtain ⟨w', hw'⟩ := (QuarticCompiler.exists_residuals_iff p q (1 : V)).mpr
      ((NineLightQuartic.exists_quartic_iff p q).mp hv)
    let v : Fin (QuarticCompiler.witnessCount p q + 1) → V :=
      fun i => QuarticCompiler.semiringAssignment (1 : V) w' ((QuarticCompiler.coordinate p q).symm i)
    have hz : AdaptiveEquationSyntax2011.InternalZero (QuarticSyntax.expression p q) v := by
      apply (NineLightQuartic.zero_iff_residuals p q _).mpr
      simpa only [v, Function.comp_def, Equiv.symm_apply_apply] using hw'
    have hv0 : v 0 = 1 := by
      simp only [v]
      rw [← QuarticCompiler.coordinate_none p q, Equiv.symm_apply_apply]
      rfl
    refine ⟨fun j => v j.succ, ?_⟩
    have hcons : (Fin.cons (1 : V) (fun j => v j.succ) : Fin (QuarticCompiler.witnessCount p q + 1) → V) = v := by
      rw [← hv0]; exact Fin.cons_self_tail v
    rw [hcons]
    exact (internalZero_iff _ _).mp hz

/-- **`JonesModel` holds.** -/
theorem jonesModel (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    (∃ a : Fin 9 → V,
      AdaptiveEquationSyntax2011.InternalZero (ExecutableJones.expression (QuarticSyntax.expression p q) 0) a) ↔
      ∃ v : Fin (QuarticCompiler.witnessCount p q + 1) → V,
        AdaptiveEquationSyntax2011.InternalZero (QuarticSyntax.expression p q) v := by
  have hP := QuarticSyntaxFacts.expression_degree p q
  have hnorm := QuarticSyntaxFacts.expression_normalized p q 1
  rw [← quartic_one_iff p q, ← nine_iff (QuarticSyntax.expression p q) hP hnorm]
  simp only [internalZero_iff]

end DiophantineConsistency.NineFreshJones

#print axioms DiophantineConsistency.NineFreshJones.jonesModel
