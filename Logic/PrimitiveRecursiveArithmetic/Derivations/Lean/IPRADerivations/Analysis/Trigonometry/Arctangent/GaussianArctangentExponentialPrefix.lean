import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentCayleyStep
import IPRADerivations.Analysis.Gamma.GaussianGammaHalfPiName

/-!
# Exact prefixes of the original arctangent quadrature

The prefix is formed from the original factorial-cleared Basel quadrature.
Its increment is the term used in the conjugate Cayley step. Its full
value at the original mesh is the original π observation times (i/2).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentExponentialPrefix

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open BaselQuadrature (Qb uq inst_Qb)
open Products (fact)
open GaussianArctangentCayleyStep (increment incrementCode)
open GaussianArctangentCayleyValues (denominator denominator_positive imaginaryCode)
open GaussianGammaHalfPiName (meshAt clearing)
open ComplexLogarithmRemainder (scale zeroCode oneCode normSq normSq_eval eval_re_code eval_im_code)
open GaussianRationalHorner (qzero qadd qmul ofGaussian ofGaussian_canonical ofGaussian_represents
  canonical_unique qadd_canonical qadd_represents qmul_canonical qmul_represents represents_congr
  represents_rescale positive_product)
open GaussianRationalMetric (bounded bounded_of_cleared)
open GaussianRootAlgebra (equal equal_of_values equal_refl re_add im_add re_mul im_mul
  re_scale im_scale re_zero im_zero re_one im_one)
open GaussianRationalSyntheticDivision (qmul_congr)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.FiniteHausdorff (sum_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (M L : PTm n) : Fm PTm n := le one M ⋏ le (two*(M*M)) L

def total (j M L : PTm n) : PTm n := ap2 (sumF Qb) j (pairT M L)

def prefixValue (j M L : PTm n) : PTm n := ofGaussian (scale (two*total j M L) imaginaryCode) (fact L)

def halfI : PTm n := ofGaussian imaginaryCode two

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (M L : PTm n) :
    (source M L).subst σ = source (Syn.subst σ M) (Syn.subst σ L) := by
  simp [source]

@[simp] theorem subst_total {m : ℕ} (σ : Fin n → PTm m) (j M L : PTm n) :
    Syn.subst σ (total j M L) = total (Syn.subst σ j) (Syn.subst σ M) (Syn.subst σ L) := by
  simp [total]

@[simp] theorem subst_prefixValue {m : ℕ} (σ : Fin n → PTm m) (j M L : PTm n) :
    Syn.subst σ (prefixValue j M L) = prefixValue (Syn.subst σ j) (Syn.subst σ M) (Syn.subst σ L) := by
  simp [prefixValue,imaginaryCode,Products.fact]

private theorem fact_positive (L : PTm n) : Γ ⊢[PRAAx] le one (fact L) :=
  le_congr (.eqRefl _) (AnalyticNumberTheory.Primes.fact_pos L).eqSymm (zero_lt_succ _)

private theorem total_succ (j M L : PTm n) : Γ ⊢[PRAAx]
    total (succ j) M L ≐ total j M L+M*uq j M L :=
  (sum_succ Qb j (pairT M L)).eqTrans (congrAdd (.eqRefl _) (inst_Qb j M L))

private theorem quotient_exact (j M L : PTm n) (hs : Γ ⊢[PRAAx] source M L)
    (hj : Γ ⊢[PRAAx] lt j M) : Γ ⊢[PRAAx] fact L ≐ denominator M j*uq j M L := by
  have hd := RationalIntegerNormalization.positive_form (denominator_positive M j (Prf.andE₁ hs))
  have hjj := le_mul_mono (le_of_lt hj) (le_of_lt hj)
  have hsum : Γ ⊢[PRAAx] le (denominator M j) (two*(M*M)) := by
    unfold denominator
    ipra_le sl hjj
  have hl : Γ ⊢[PRAAx] le (denominator M j) L := le_trans hsum (Prf.andE₂ hs)
  have hv := AnalyticNumberTheory.Primes.dvd_fact (le_congr hd (.eqRefl _) hl)
  exact DiophantineNumberTheory.Coprime.eq_of_dvd' hd (dvd_congr_left hd.eqSymm hv)

theorem prefix_zero (M L : PTm n) : Γ ⊢[PRAAx] prefixValue zero M L ≐ qzero := by
  have hF := fact_positive (Γ := Γ) L
  have eq : Γ ⊢[PRAAx] equal (scale (two*total zero M L) imaginaryCode) (scale (fact L) zeroCode) := by
    have e := natEq (sum_zero (Γ := Γ) Qb (pairT M L))
    apply equal_of_values <;>
      simp only [re_scale,im_scale,re_zero,im_zero,imaginaryCode,eval_re_code,eval_im_code,ZT.toZ_ofNat,total] <;>
      ipra_simps
    · ring
    · rw [e]
      ring
  exact canonical_unique _ _ _ _ (ofGaussian_canonical _ _ hF) (ofGaussian_canonical _ _ (le_refl one)) hF
    (represents_congr (.eqRefl _) eq (.eqRefl _) (ofGaussian_represents _ _ hF))
    (represents_congr (.eqRefl _) (equal_refl _) (one_mul _)
      (represents_rescale qzero zeroCode one (fact L) (ofGaussian_represents _ _ (le_refl one))))

theorem prefix_succ (j M L : PTm n) (hs : Γ ⊢[PRAAx] source M L)
    (hj : Γ ⊢[PRAAx] lt j M) :
    Γ ⊢[PRAAx] prefixValue (succ j) M L ≐ qadd (prefixValue j M L) (increment M j) := by
  let a := scale (two*total j M L) imaginaryCode
  let b := scale (uq j M L) (incrementCode M)
  let c := scale (two*total (succ j) M L) imaginaryCode
  have hF := fact_positive (Γ := Γ) L
  have hd := denominator_positive M j (Prf.andE₁ hs)
  have inc := represents_congr (.eqRefl _) (equal_refl _) (quotient_exact j M L hs hj).eqSymm
    (represents_rescale (increment M j) (incrementCode M) (denominator M j) (uq j M L)
      (ofGaussian_represents _ _ hd))
  have added := qadd_represents (prefixValue j M L) (increment M j) a b (fact L) hF
    (ofGaussian_represents _ _ hF) inc
  have eq : Γ ⊢[PRAAx] equal (ComplexLogarithmRemainder.add a b) c := by
    have e := natEq (total_succ (Γ := Γ) j M L)
    apply equal_of_values <;>
      simp only [a,b,c,re_add,im_add,re_scale,im_scale,imaginaryCode,incrementCode,
        eval_re_code,eval_im_code,ZT.toZ_ofNat] <;> ipra_simps
    · ring
    · rw [e]
      ring
  exact canonical_unique _ _ _ _ (ofGaussian_canonical _ _ hF) (qadd_canonical _ _) hF
    (ofGaussian_represents _ _ hF) (represents_congr (.eqRefl _) eq (.eqRefl _) added)

private theorem estimate_step (j M L : PTm n) (hs : Γ ⊢[PRAAx] source M L)
    (hj : Γ ⊢[PRAAx] lt j M)
    (ih : Γ ⊢[PRAAx] le (M*total j M L) (j*fact L)) :
    Γ ⊢[PRAAx] le (M*total (succ j) M L) (succ j*fact L) := by
  have row : Γ ⊢[PRAAx] le (M*(M*uq j M L)) (fact L) :=
    le_congr (by ipra_ring) (quotient_exact j M L hs hj).eqSymm
      (le_mul_mono (le_add_right (M*M) (j*j)) (le_refl (uq j M L)))
  have eq : Γ ⊢[PRAAx] M*total (succ j) M L ≐ M*total j M L+M*(M*uq j M L) :=
    (congrMul (.eqRefl _) (total_succ j M L)).eqTrans (by ipra_ring)
  exact le_congr eq.eqSymm (by ipra_ring) (sum_mono ih row)

private theorem total_estimate (j M L : PTm n) (hs : Γ ⊢[PRAAx] source M L)
    (hj : Γ ⊢[PRAAx] le j M) : Γ ⊢[PRAAx] le (M*total j M L) (j*fact L) := by
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift M) ⟶
      le (Syn.shift M*total (var 0) (Syn.shift M) (Syn.shift L)) (var 0*fact (Syn.shift L))) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp [Products.fact]
      refine .impI ?_
      have eq := congrMul (.eqRefl M) (sum_zero (Γ := le zero M :: Γ) Qb (pairT M L))
      exact le_congr ((mul_zero M).eqSymm.eqTrans eq.eqSymm) (zero_mul (fact L)).eqSymm (le_refl zero)
    · simp [Products.fact,subst_repl_shift]
      refine .impI ?_
      let IH := le (var 0) (Syn.shift M) ⟶
        le (Syn.shift M*total (var 0) (Syn.shift M) (Syn.shift L)) (var 0*fact (Syn.shift L))
      let Δ := le (succ (var 0)) (Syn.shift M) :: IH :: Γ.map Fm.shift
      have hshift : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift M) (Syn.shift L) := by
        simpa only [Fm.shift,subst_source,Syn.shift] using hs.shift
      have guard : Δ ⊢[PRAAx] lt (var 0) (Syn.shift M) := Prf.hyp0
      have previous : Δ ⊢[PRAAx] le (Syn.shift M*total (var 0) (Syn.shift M) (Syn.shift L))
          (var 0*fact (Syn.shift L)) :=
        .impE Prf.hyp1 (le_of_lt guard)
      exact estimate_step _ _ _ hshift.wk.wk guard previous
  have inst : Γ ⊢[PRAAx] le j M ⟶ le (M*total j M L) (j*fact L) := by
    simpa [Products.fact] using all.allE j
  exact .impE inst hj

theorem prefix_bound (j M L : PTm n) (hs : Γ ⊢[PRAAx] source M L)
    (hj : Γ ⊢[PRAAx] le j M) : Γ ⊢[PRAAx] bounded (prefixValue j M L) two one := by
  let a := scale (two*total j M L) imaginaryCode
  have hF := fact_positive (Γ := Γ) L
  have e := total_estimate j M L hs hj
  have cleared : Γ ⊢[PRAAx] le (total j M L) (fact L) :=
    RationalValueBounds.positive_cancel (Prf.andE₁ hs) (le_trans e (le_mul_mono hj (le_refl _)))
  have b := le_mul_mono (le_refl two) cleared
  have norm : Γ ⊢[PRAAx] normSq a ≐ (two*total j M L)*(two*total j M L) := by
    apply deriveNat
    rw [normSq_eval]
    simp only [a,imaginaryCode,re_scale,im_scale,eval_re_code,eval_im_code,ZT.toZ_ofNat]
    ipra_simps
    ring
  apply bounded_of_cleared _ a (fact L) two one hF (le_refl one) (ofGaussian_represents _ _ hF)
  exact le_congr (norm.eqSymm.eqTrans (by ipra_ring)) (by ipra_ring) (le_mul_mono b b)

theorem original_mesh_source (p : PTm n) : Γ ⊢[PRAAx] source (meshAt p) (clearing p) :=
  .andI (zero_lt_succ _) (le_refl _)

theorem at_pi_observation (p x : PTm n) : Γ ⊢[PRAAx]
    prefixValue (meshAt p) (meshAt p) (clearing p) ≐ qmul halfI (ap2 GaussianGammaHalfPiName.nameF p x) := by
  let M := meshAt p
  let L := clearing p
  let a := scale (two*total M M L) imaginaryCode
  let b := scale (num 4*total M M L) oneCode
  let pi := GaussianGammaHalfPiName.observation p
  have hF := fact_positive (Γ := Γ) L
  have ht : Γ ⊢[PRAAx] le one two := zero_lt_succ one
  have hD := positive_product two (fact L) ht hF
  have lhs := represents_rescale (prefixValue M M L) a (fact L) two (ofGaussian_represents _ _ hF)
  have rhs := qmul_represents halfI pi imaginaryCode b two (fact L) ht hF
    (ofGaussian_represents _ _ ht) (ofGaussian_represents _ _ hF)
  have eq : Γ ⊢[PRAAx] equal (scale two a) (ComplexLogarithmRemainder.mul imaginaryCode b) := by
    apply equal_of_values <;>
      simp only [a,b,re_scale,im_scale,re_mul,im_mul,imaginaryCode,eval_re_code,eval_im_code,
        ZT.toZ_ofNat,re_one,im_one] <;> ipra_simps <;> ring
  exact (canonical_unique _ (qmul halfI pi) _ (two*fact L) (ofGaussian_canonical _ _ hF)
    (qmul_canonical _ _) hD (represents_congr (.eqRefl _) eq (mul_comm _ _) lhs) rhs).eqTrans
    (qmul_congr (.eqRefl _) (GaussianGammaHalfPiName.sample_at p x).eqSymm)

theorem actual_original_arctangent_exponential_prefix_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source (var 1) (var 2) ⟶ (lt (var 0) (var 1) ⟶
        prefixValue (succ (var 0)) (var 1) (var 2) ≐
          qadd (prefixValue (var 0) (var 1) (var 2)) (increment (var 1) (var 0)))) :=
  closeUniv 3 (.impI (.impI (prefix_succ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_original_arctangent_exponential_prefix_bound_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source (var 1) (var 2) ⟶ (le (var 0) (var 1) ⟶
        bounded (prefixValue (var 0) (var 1) (var 2)) two one)) :=
  closeUniv 3 (.impI (.impI (prefix_bound _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_original_arctangent_exponential_mesh_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (prefixValue (meshAt (var 0)) (meshAt (var 0)) (clearing (var 0)) ≐
        qmul halfI (ap2 GaussianGammaHalfPiName.nameF (var 0) (var 1))) :=
  closeUniv 2 (at_pi_observation _ _)

end LeanProofs.IPRA.Analysis.GaussianArctangentExponentialPrefix
