import IPRADerivations.Analysis.Gamma.EulerProducts.GammaCanonicalFactors
import IPRADerivations.Analysis.Logarithm.DyadicComplexLogarithm
import IPRADerivations.Analysis.RationalArithmetic.RationalClosure
import IPRADerivations.Core.LinearCombination

/-!
# A joint finite-query name for the canonical Gamma logarithmic tail

Packet `analysis/gamma_ipra`, finite obligations behind (C3) and (C6).
The samples use actual finite Taylor factors and their computed product
denominators. Both the number of factor indices and the Taylor cutoff grow
according to explicit primitive-recursive precision schedules.

At precision `p`, the sample sums `2^(p+5)*(R²+1)` indices and uses cubic
Taylor length `p+5+2^(p+5)*(R²+1)` at each index. The old-prefix Taylor
error and new-index suffix error are each at most `2^(-p-5)`. Actual
signed quotient rounding at scale `2^(p+4)` produces a PR5 observation
with discrepancy at most `5*2^k` between precisions `p` and `p+k`.
The sample denominators are proved positive from the input denominator.
The sharp finite `R²/N` C6 bound survives with only `2/2^(p+4)` rounding
slack in the observations.

The construction concerns the power-series tail at a rational complex input.
It does not identify that series with an analytic logarithm, prove its
exponential identity, or construct the Euler/Gamma approximants.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GammaCanonicalNames

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GammaCanonicalFactors
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder
  (re im add neg scale zeroCode normSq bounded bounded_add bounded_scale bounded_mono
    normSq_eval normSq_scale eval_re_code eval_im_code congr_normSq subst_bounded)
open LeanProofs.IPRA.Analysis.DyadicComplexLogarithm
  (crossDifference rounded roundedDifference cancel_bounded_scale)
open LeanProofs.IPRA.Analysis.RationalClosure (succ_le_two_pow)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

@[simp] private theorem subst_two {m : ℕ} (σ : Fin n → PTm m) : Syn.subst σ (two : PTm n) = two := by
  simp [two, one]

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem eval_re_eq {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : ZT.toZ Γ (re a) = ZT.toZ Γ (re b) := by
  simp only [re, ZT.toZ]
  rw [natEq (congrFst (congrFst h)), natEq (congrSnd (congrFst h))]

theorem eval_im_eq {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : ZT.toZ Γ (im a) = ZT.toZ Γ (im b) := by
  simp only [im, ZT.toZ]
  rw [natEq (congrFst (congrSnd h)), natEq (congrSnd (congrSnd h))]

theorem sum_count_congr (z B N L D : PTm n) {r s : PTm n} (h : Γ ⊢[PRAAx] r ≐ s) :
    Γ ⊢[PRAAx] finiteSum z B N r L D ≐ finiteSum z B N s L D :=
  congrApp GammaCanonicalFactors.sumF (fun i => by fin_cases i <;> first | exact h | exact .eqRefl _)

theorem summand_index_congr (z B L D : PTm n) {k j : PTm n} (h : Γ ⊢[PRAAx] k ≐ j) :
    Γ ⊢[PRAAx] summand z B k L D ≐ summand z B j L D := by
  have eq := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (summand (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![z,B,k,L,D]) (σ' := ![z,B,j,L,D])
    (fun i => by fin_cases i <;> first | exact h | exact .eqRefl _)
  simpa using eq

theorem norm_scale_commute (A B c : PTm n) :
    Γ ⊢[PRAAx] normSq (scale A (scale B c)) ≐ normSq (scale B (scale A c)) := by
  apply deriveNat
  rw [normSq_eval, normSq_eval]
  simp only [scale, eval_re_code, eval_im_code, ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_mul, map_mul]
  ring

/-- Transfer a cleared norm bound by a proved scalar budget. -/
theorem bounded_budget (c A B R S : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (h : Γ ⊢[PRAAx] bounded (scale A c) S) (budget : Γ ⊢[PRAAx] le (B*S) (A*R)) :
    Γ ⊢[PRAAx] bounded (scale B c) R := by
  have scaled := bounded_scale B h
  have result : Γ ⊢[PRAAx] bounded (scale A (scale B c)) (A*R) :=
    le_congr (norm_scale_commute B A c) (.eqRefl _) (bounded_mono scaled budget)
  exact cancel_bounded_scale hA result

def degreeTerm (z B N i L K D E : PTm n) : PTm n :=
  crossDifference (summand z B (succ (N+i)) L D) (summand z B (succ (N+i)) (L+K) E) D E

def degreeDifference (z B N r L K D E : PTm n) : PTm n :=
  crossDifference (finiteSum z B N r L D) (finiteSum z B N r (L+K) E) D E

@[simp] theorem subst_degreeTerm {m : ℕ} (σ : Fin n → PTm m) (z B N i L K D E : PTm n) :
    Syn.subst σ (degreeTerm z B N i L K D E) = degreeTerm (Syn.subst σ z) (Syn.subst σ B)
      (Syn.subst σ N) (Syn.subst σ i) (Syn.subst σ L) (Syn.subst σ K) (Syn.subst σ D) (Syn.subst σ E) := by
  simp [degreeTerm, crossDifference]
@[simp] theorem subst_degreeDifference {m : ℕ} (σ : Fin n → PTm m) (z B N r L K D E : PTm n) :
    Syn.subst σ (degreeDifference z B N r L K D E) = degreeDifference (Syn.subst σ z) (Syn.subst σ B)
      (Syn.subst σ N) (Syn.subst σ r) (Syn.subst σ L) (Syn.subst σ K) (Syn.subst σ D) (Syn.subst σ E) := by
  simp [degreeDifference, crossDifference]

/-- Exact common-denominator meaning of a degree-comparison summand. -/
theorem degree_term_norm (z B N i L K D E C : PTm n)
    (clearD : Γ ⊢[PRAAx] factorDenominator (B*succ (N+i)) L *
      quo D (factorDenominator (B*succ (N+i)) L) ≐ D)
    (clearE : Γ ⊢[PRAAx] factorDenominator (B*succ (N+i)) (L+K) *
      quo E (factorDenominator (B*succ (N+i)) (L+K)) ≐ E) :
    Γ ⊢[PRAAx] normSq (scale C (degreeTerm z B N i L K D E)) ≐
      normSq (scale (quo D (factorDenominator (B*succ (N+i)) L) *
          quo E (factorDenominator (B*succ (N+i)) (L+K)))
        (scale C (factorDifference z (B*succ (N+i)) L K))) := by
  apply deriveNat
  have d := natEq clearD
  have e := natEq clearE
  rw [normSq_eval, normSq_eval]
  simp only [degreeTerm, crossDifference, summand, factorDifference, add, ComplexLogarithmRemainder.neg, scale,
    eval_re_code, eval_im_code, ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat,
    Q.mk_mul, map_mul] at d e ⊢
  rw [← d, ← e]
  ring

theorem degree_term_bound (z R B N oldCount newCount i L K : PTm n)
    (hz : Γ ⊢[PRAAx] bounded z (R*B)) (hB : Γ ⊢[PRAAx] le one B)
    (hN : Γ ⊢[PRAAx] le one N) (hR : Γ ⊢[PRAAx] le (two*R) N)
    (hi : Γ ⊢[PRAAx] lt i oldCount) (order : Γ ⊢[PRAAx] le oldCount newCount) :
    Γ ⊢[PRAAx] bounded (scale (pw two L) (degreeTerm z B N i L K
      (tailDenominator B N oldCount L) (tailDenominator B N newCount (L+K))))
      (tailDenominator B N oldCount L * tailDenominator B N newCount (L+K)) := by
  let k := succ (N+i)
  let D := tailDenominator B N oldCount L
  let E := tailDenominator B N newCount (L+K)
  have hk : Γ ⊢[PRAAx] le one k := le_trans hN (le_trans (le_add_right _ _) (le_succ_self _))
  have nle : Γ ⊢[PRAAx] le N k := le_trans (le_add_right _ _) (le_succ_self _)
  have radius : Γ ⊢[PRAAx] le (two*(R*B)) (B*k) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl B) (le_trans hR nle))
  have d := tail_quotient_clears B N oldCount L i hB hi
  have e := tail_quotient_clears B N newCount (L+K) i hB (lt_of_lt_of_le hi order)
  have term := bounded_scale (quo D (factorDenominator (B*k) L) * quo E (factorDenominator (B*k) (L+K)))
    (finite_factor_cauchy z (B*k) (R*B) L K hz (positive_product hB hk) radius)
  have scalar : Γ ⊢[PRAAx]
      (quo D (factorDenominator (B*k) L) * quo E (factorDenominator (B*k) (L+K))) *
        (factorDenominator (B*k) L * factorDenominator (B*k) (L+K)) ≐ D*E := by
    have a := natEq d
    have b := natEq e
    apply deriveNat
    simp only [Q.mk_mul, map_mul] at a b ⊢
    rw [← a, ← b]
    ring
  exact le_congr (degree_term_norm z B N i L K D E (pw two L) d e).eqSymm (congrMul scalar scalar) term

theorem degree_zero_norm (z B N L K D E C : PTm n) :
    Γ ⊢[PRAAx] normSq (scale C (degreeDifference z B N zero L K D E)) ≐ zero := by
  apply deriveNat
  rw [normSq_eval]
  simp only [degreeDifference, crossDifference, scale, add, ComplexLogarithmRemainder.neg, eval_re_code, eval_im_code,
    ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat]
  rw [eval_re_eq (GammaCanonicalFactors.sum_zero z B N L D), eval_im_eq (GammaCanonicalFactors.sum_zero z B N L D),
    eval_re_eq (GammaCanonicalFactors.sum_zero z B N (L+K) E), eval_im_eq (GammaCanonicalFactors.sum_zero z B N (L+K) E)]
  simp only [zeroCode, eval_re_code, eval_im_code, ZT.toZ_ofNat, Q.mk_zero, map_zero]
  ring

theorem degree_succ_norm (z B N r L K D E C : PTm n) :
    Γ ⊢[PRAAx] normSq (scale C (degreeDifference z B N (succ r) L K D E)) ≐
      normSq (add (scale C (degreeDifference z B N r L K D E)) (scale C (degreeTerm z B N r L K D E))) := by
  apply deriveNat
  rw [normSq_eval, normSq_eval]
  simp only [degreeDifference, degreeTerm, crossDifference, add, ComplexLogarithmRemainder.neg, scale, eval_re_code, eval_im_code,
    ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat]
  rw [eval_re_eq (GammaCanonicalFactors.sum_succ z B N r L D), eval_im_eq (GammaCanonicalFactors.sum_succ z B N r L D),
    eval_re_eq (GammaCanonicalFactors.sum_succ z B N r (L+K) E), eval_im_eq (GammaCanonicalFactors.sum_succ z B N r (L+K) E)]
  simp only [add, eval_re_code, eval_im_code, ZT.toZ_add]
  ring

#print axioms degree_term_norm
#print axioms degree_term_bound
#print axioms degree_succ_norm

theorem degree_prefix_bound (z R B N oldCount newCount L K : PTm n)
    (hz : Γ ⊢[PRAAx] bounded z (R*B)) (hB : Γ ⊢[PRAAx] le one B)
    (hN : Γ ⊢[PRAAx] le one N) (hR : Γ ⊢[PRAAx] le (two*R) N)
    (order : Γ ⊢[PRAAx] le oldCount newCount) :
    Γ ⊢[PRAAx] bounded (scale (pw two L) (degreeDifference z B N oldCount L K
      (tailDenominator B N oldCount L) (tailDenominator B N newCount (L+K))))
      (oldCount * tailDenominator B N oldCount L * tailDenominator B N newCount (L+K)) := by
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift oldCount) ⟶
      bounded (scale (pw two (Syn.shift L)) (degreeDifference (Syn.shift z) (Syn.shift B) (Syn.shift N) (var 0)
        (Syn.shift L) (Syn.shift K) (tailDenominator (Syn.shift B) (Syn.shift N) (Syn.shift oldCount) (Syn.shift L))
        (tailDenominator (Syn.shift B) (Syn.shift N) (Syn.shift newCount) (Syn.shift L+Syn.shift K))))
        (var 0 * tailDenominator (Syn.shift B) (Syn.shift N) (Syn.shift oldCount) (Syn.shift L) *
          tailDenominator (Syn.shift B) (Syn.shift N) (Syn.shift newCount) (Syn.shift L+Syn.shift K))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, subst_bounded, ComplexLogarithmRemainder.subst_scale,
        subst_ap2, subst_two, subst_degreeDifference, subst_tailDenominator, PTm.subst_add, PTm.subst_mul,
        Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact .impI (le_congr (degree_zero_norm _ _ _ _ _ _ _ _).eqSymm (.eqRefl _) (zero_le _))
    · simp only [Fm.subst_imp, subst_le, subst_bounded, ComplexLogarithmRemainder.subst_scale,
        subst_ap2, subst_two, subst_degreeDifference, subst_tailDenominator, PTm.subst_add, PTm.subst_mul,
        Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      refine .impI ?_
      let D := tailDenominator (Syn.shift B) (Syn.shift N) (Syn.shift oldCount) (Syn.shift L)
      let E := tailDenominator (Syn.shift B) (Syn.shift N) (Syn.shift newCount) (Syn.shift L+Syn.shift K)
      let Δ : List (Fm PTm (n+1)) := le (succ (var 0)) (Syn.shift oldCount) ::
        (le (var 0) (Syn.shift oldCount) ⟶ bounded (scale (pw two (Syn.shift L))
          (degreeDifference (Syn.shift z) (Syn.shift B) (Syn.shift N) (var 0) (Syn.shift L) (Syn.shift K) D E))
          (var 0*D*E)) :: Γ.map Fm.shift
      have previous : Δ ⊢[PRAAx] bounded (scale (pw two (Syn.shift L))
          (degreeDifference (Syn.shift z) (Syn.shift B) (Syn.shift N) (var 0) (Syn.shift L) (Syn.shift K) D E)) (var 0*D*E) :=
        .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      have zbound : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift z) (Syn.shift R*Syn.shift B) := by
        simpa only [Fm.shift, subst_bounded, PTm.subst_mul, Syn.shift] using hz.shift
      have b : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift, Syn.shift] using hB.shift
      have start : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift, Syn.shift] using hN.shift
      have radius : Γ.map Fm.shift ⊢[PRAAx] le (two*Syn.shift R) (Syn.shift N) := by simpa [Fm.shift, Syn.shift] using hR.shift
      have ordered : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift oldCount) (Syn.shift newCount) := by simpa [Fm.shift, Syn.shift] using order.shift
      have term := degree_term_bound (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N)
        (Syn.shift oldCount) (Syn.shift newCount) (var 0) (Syn.shift L) (Syn.shift K)
        zbound.wk.wk b.wk.wk start.wk.wk radius.wk.wk (Prf.hyp0 : Δ ⊢[PRAAx] _) ordered.wk.wk
      have eq : Δ ⊢[PRAAx] var 0*D*E+D*E ≐ succ (var 0)*D*E := by ipra_ring
      exact le_congr (degree_succ_norm _ _ _ _ _ _ _ _ _).eqSymm (congrMul eq eq) (bounded_add previous term)
  have result := Prf.allE oldCount all
  have rule : Γ ⊢[PRAAx] le oldCount oldCount ⟶ bounded (scale (pw two L) (degreeDifference z B N oldCount L K
      (tailDenominator B N oldCount L) (tailDenominator B N newCount (L+K))))
      (oldCount * tailDenominator B N oldCount L * tailDenominator B N newCount (L+K)) := by
    simpa only [Fm.subst_imp, subst_le, subst_bounded, ComplexLogarithmRemainder.subst_scale,
      subst_ap2, subst_two, subst_degreeDifference, subst_tailDenominator, PTm.subst_add, PTm.subst_mul,
      Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using result
  exact .impE rule (le_refl _)

/-! ## Actual splitting of the finite factor-index sum -/

def splitFormula (z B N r s L D : PTm n) : Fm PTm n :=
  ZT.eq (re (finiteSum z B N (r+s) L D))
    (re (add (finiteSum z B N r L D) (finiteSum z B (N+r) s L D))) ⋏
  ZT.eq (im (finiteSum z B N (r+s) L D))
    (im (add (finiteSum z B N r L D) (finiteSum z B (N+r) s L D)))

@[simp] theorem subst_splitFormula {m : ℕ} (σ : Fin n → PTm m) (z B N r s L D : PTm n) :
    (splitFormula z B N r s L D).subst σ = splitFormula (Syn.subst σ z) (Syn.subst σ B)
      (Syn.subst σ N) (Syn.subst σ r) (Syn.subst σ s) (Syn.subst σ L) (Syn.subst σ D) := by
  simp only [splitFormula, Fm.subst_and, ZT.subst_eq, ComplexLogarithmRemainder.subst_re,
    ComplexLogarithmRemainder.subst_im, ComplexLogarithmRemainder.subst_add, subst_finiteSum, PTm.subst_add]

theorem split_zero (z B N r L D : PTm n) : Γ ⊢[PRAAx] splitFormula z B N r zero L D := by
  have count := sum_count_congr (Γ := Γ) z B N L D (add_zero r)
  have empty := GammaCanonicalFactors.sum_zero (Γ := Γ) z B (N+r) L D
  refine .andI ?_ ?_
  · apply ZT.derive
    rw [eval_re_eq count]
    simp only [add, eval_re_code, ZT.toZ_add]
    rw [eval_re_eq empty]
    simp only [zeroCode, eval_re_code, ZT.toZ_ofNat, Q.mk_zero, map_zero]
    ring
  · apply ZT.derive
    rw [eval_im_eq count]
    simp only [add, eval_im_code, ZT.toZ_add]
    rw [eval_im_eq empty]
    simp only [zeroCode, eval_im_code, ZT.toZ_ofNat, Q.mk_zero, map_zero]
    ring

theorem split_step (z B N r s L D : PTm n) (h : Γ ⊢[PRAAx] splitFormula z B N r s L D) :
    Γ ⊢[PRAAx] splitFormula z B N r (succ s) L D := by
  have full := (sum_count_congr (Γ := Γ) z B N L D (add_succ r s)).eqTrans
    (GammaCanonicalFactors.sum_succ z B N (r+s) L D)
  have suffix := GammaCanonicalFactors.sum_succ (Γ := Γ) z B (N+r) s L D
  have index : Γ ⊢[PRAAx] succ (N+(r+s)) ≐ succ ((N+r)+s) := congrSucc (add_assoc _ _ _).eqSymm
  have term := summand_index_congr z B L D index
  have hr := ZT.toZ_eq (Prf.andE₁ h)
  have hi := ZT.toZ_eq (Prf.andE₂ h)
  simp only [add, eval_re_code, eval_im_code, ZT.toZ_add] at hr hi
  refine .andI ?_ ?_
  · apply ZT.derive
    rw [eval_re_eq full]
    simp only [add, eval_re_code, ZT.toZ_add]
    rw [eval_re_eq suffix]
    simp only [add, eval_re_code, ZT.toZ_add]
    rw [eval_re_eq term]
    linear_combination hr
  · apply ZT.derive
    rw [eval_im_eq full]
    simp only [add, eval_im_code, ZT.toZ_add]
    rw [eval_im_eq suffix]
    simp only [add, eval_im_code, ZT.toZ_add]
    rw [eval_im_eq term]
    linear_combination hi

theorem sum_split (z B N r s L D : PTm n) : Γ ⊢[PRAAx] splitFormula z B N r s L D := by
  have all : Γ ⊢[PRAAx] .all (splitFormula (Syn.shift z) (Syn.shift B) (Syn.shift N) (Syn.shift r)
      (var 0) (Syn.shift L) (Syn.shift D)) := by
    refine PRA.qfInd _ ⟨trivial, trivial⟩ ?_ ?_
    · simp only [subst_splitFormula, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact split_zero _ _ _ _ _ _
    · simp only [subst_splitFormula, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      exact split_step _ _ _ _ _ _ _ Prf.hyp0
  simpa only [subst_splitFormula, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE s all

theorem sum_split_re (z B N r s L D : PTm n) :
    ZT.toZ Γ (re (finiteSum z B N (r+s) L D)) = ZT.toZ Γ (re (finiteSum z B N r L D)) +
      ZT.toZ Γ (re (finiteSum z B (N+r) s L D)) := by
  simpa only [add, eval_re_code, ZT.toZ_add] using ZT.toZ_eq (Prf.andE₁ (sum_split (Γ := Γ) z B N r s L D))

theorem sum_split_im (z B N r s L D : PTm n) :
    ZT.toZ Γ (im (finiteSum z B N (r+s) L D)) = ZT.toZ Γ (im (finiteSum z B N r L D)) +
      ZT.toZ Γ (im (finiteSum z B (N+r) s L D)) := by
  simpa only [add, eval_im_code, ZT.toZ_add] using ZT.toZ_eq (Prf.andE₂ (sum_split (Γ := Γ) z B N r s L D))

#print axioms degree_prefix_bound
#print axioms sum_split

theorem power_positive (p : PTm n) : Γ ⊢[PRAAx] le one (pw two p) :=
  le_trans (zero_lt_succ p) (succ_le_two_pow p)

/-- The finite C6 estimate at an arbitrary exact/common-denominator scale. -/
theorem disk_sum_bound (z R B N r L D : PTm n) (hz : Γ ⊢[PRAAx] bounded z (R*B))
    (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N) (hR : Γ ⊢[PRAAx] le (two*R) N) :
    Γ ⊢[PRAAx] bounded (scale N (finiteSum z B N r L D)) (R*R*D) := by
  have radius : Γ ⊢[PRAAx] le (two*(R*B)) (B*N) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl B) hR)
  have original := finite_sum_bound z (R*B) B N r L D hz hB hN radius
  have eq : Γ ⊢[PRAAx] normSq (scale (B*B) (scale N (finiteSum z B N r L D))) ≐
      normSq (scale (B*B*N) (finiteSum z B N r L D)) := by
    apply deriveNat
    rw [normSq_eval, normSq_eval]
    simp only [scale, eval_re_code, eval_im_code, ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_mul, map_mul]
    ring
  have result : Γ ⊢[PRAAx] bounded (scale (B*B) (scale N (finiteSum z B N r L D))) ((B*B)*(R*R*D)) :=
    le_congr eq.eqSymm (by ipra_ring) original
  exact cancel_bounded_scale (positive_product hB hB) result

def jointDifference (z B N r s L K : PTm n) : PTm n :=
  crossDifference (finiteTail z B N r L) (finiteTail z B N (r+s) (L+K))
    (tailDenominator B N r L) (tailDenominator B N (r+s) (L+K))

@[simp] theorem subst_jointDifference {m : ℕ} (σ : Fin n → PTm m) (z B N r s L K : PTm n) :
    Syn.subst σ (jointDifference z B N r s L K) = jointDifference (Syn.subst σ z) (Syn.subst σ B)
      (Syn.subst σ N) (Syn.subst σ r) (Syn.subst σ s) (Syn.subst σ L) (Syn.subst σ K) := by
  simp [jointDifference, crossDifference]

/-- Both Taylor and index differences refer to the actual finiteTail samples. -/
theorem joint_difference_norm (z B N r s L K C : PTm n) :
    Γ ⊢[PRAAx] normSq (scale C (jointDifference z B N r s L K)) ≐
      normSq (add (scale C (degreeDifference z B N r L K
          (tailDenominator B N r L) (tailDenominator B N (r+s) (L+K))))
        (scale (tailDenominator B N r L) (scale C
          (finiteSum z B (N+r) s (L+K) (tailDenominator B N (r+s) (L+K)))))) := by
  apply deriveNat
  rw [normSq_eval, normSq_eval]
  simp only [jointDifference, finiteTail, degreeDifference, crossDifference, add,
    ComplexLogarithmRemainder.neg, scale, eval_re_code, eval_im_code, ZT.toZ_add, ZT.toZ_neg,
    ZT.toZ_mul, ZT.toZ_ofNat]
  rw [sum_split_re z B N r s (L+K) _, sum_split_im z B N r s (L+K) _]
  ring

/-- Derived joint error bound with two explicit numerical budgets. -/
theorem joint_bound (z R B N r s L K U : PTm n) (hz : Γ ⊢[PRAAx] bounded z (R*B))
    (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N) (hR : Γ ⊢[PRAAx] le (two*R) N)
    (degreeBudget : Γ ⊢[PRAAx] le (U*r) (pw two L))
    (indexBudget : Γ ⊢[PRAAx] le (U*R*R) (N+r)) :
    Γ ⊢[PRAAx] bounded (scale U (jointDifference z B N r s L K))
      (two * tailDenominator B N r L * tailDenominator B N (r+s) (L+K)) := by
  let D := tailDenominator B N r L
  let E := tailDenominator B N (r+s) (L+K)
  have degree := degree_prefix_bound z R B N r (r+s) L K hz hB hN hR (le_add_right _ _)
  have degreeScale : Γ ⊢[PRAAx] le (U*(r*D*E)) (pw two L*(D*E)) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono degreeBudget (le_refl (D*E)))
  have head := bounded_budget (degreeDifference z B N r L K D E) (pw two L) U (D*E) (r*D*E)
    (power_positive L) degree degreeScale
  have positive : Γ ⊢[PRAAx] le one (N+r) := le_trans hN (le_add_right _ _)
  have suffix := disk_sum_bound z R B (N+r) s (L+K) E hz hB positive (le_trans hR (le_add_right _ _))
  have indexScale : Γ ⊢[PRAAx] le (U*(R*R*E)) ((N+r)*E) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono indexBudget (le_refl E))
  have tail := bounded_scale D (bounded_budget (finiteSum z B (N+r) s (L+K) E) (N+r) U E (R*R*E)
    positive suffix indexScale)
  have radius : Γ ⊢[PRAAx] D*E+D*E ≐ two*D*E := by ipra_ring
  exact le_congr (joint_difference_norm z B N r s L K U).eqSymm (congrMul radius radius) (bounded_add head tail)

/-! ## Explicit runtime precision schedules -/

def precision (p : PTm n) : PTm n := p + num 5
def count (p R : PTm n) : PTm n := pw two (precision p) * (R*R+one)
def degree (p R : PTm n) : PTm n := precision p + count p R
def gap (p k R : PTm n) : PTm n := monus (count (p+k) R) (count p R)
def degreeGap (p k R : PTm n) : PTm n := k + gap p k R

@[simp] theorem subst_precision {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (precision p) = precision (Syn.subst σ p) := by simp [precision]
@[simp] theorem subst_count {m : ℕ} (σ : Fin n → PTm m) (p R : PTm n) :
    Syn.subst σ (count p R) = count (Syn.subst σ p) (Syn.subst σ R) := by simp [count]
@[simp] theorem subst_degree {m : ℕ} (σ : Fin n → PTm m) (p R : PTm n) :
    Syn.subst σ (degree p R) = degree (Syn.subst σ p) (Syn.subst σ R) := by simp [degree]
@[simp] theorem subst_gap {m : ℕ} (σ : Fin n → PTm m) (p k R : PTm n) :
    Syn.subst σ (gap p k R) = gap (Syn.subst σ p) (Syn.subst σ k) (Syn.subst σ R) := by simp [gap]
@[simp] theorem subst_degreeGap {m : ℕ} (σ : Fin n → PTm m) (p k R : PTm n) :
    Syn.subst σ (degreeGap p k R) = degreeGap (Syn.subst σ p) (Syn.subst σ k) (Syn.subst σ R) := by simp [degreeGap]

theorem precision_add (p k : PTm n) : Γ ⊢[PRAAx] precision (p+k) ≐ precision p+k := by unfold precision; ipra_ring

theorem count_add (p k R : PTm n) : Γ ⊢[PRAAx] count (p+k) R ≐ count p R * pw two k := by
  unfold count
  ipra_lc (𝔞(R)*𝔞(R)+1) * natEq ((congrAp2 powF (precision_add (Γ := Γ) p k) (.eqRefl two)).eqTrans (pw_add two (precision p) k))

theorem count_order (p k R : PTm n) : Γ ⊢[PRAAx] le (count p R) (count (p+k) R) :=
  le_congr (by ipra_ring) (count_add p k R).eqSymm (le_mul_mono (le_refl _) (power_positive k))

theorem count_gap (p k R : PTm n) : Γ ⊢[PRAAx] count (p+k) R ≐ count p R + gap p k R := eq_add_of_le (count_order p k R)

theorem degree_gap (p k R : PTm n) : Γ ⊢[PRAAx] degree (p+k) R ≐ degree p R + degreeGap p k R := by
  unfold degree degreeGap
  ipra_lc natEq (precision_add (Γ := Γ) p k) + natEq (count_gap (Γ := Γ) p k R)

theorem degree_budget (p R : PTm n) : Γ ⊢[PRAAx] le (pw two (precision p) * count p R) (pw two (degree p R)) := by
  have countBound : Γ ⊢[PRAAx] le (count p R) (pw two (count p R)) :=
    le_trans (le_succ_self (count p R)) (succ_le_two_pow (count p R))
  exact le_congr (.eqRefl _) (pw_add two (precision p) (count p R)).eqSymm
    (le_mul_mono (le_refl _) countBound)

theorem index_budget (p R N : PTm n) : Γ ⊢[PRAAx] le (pw two (precision p) * R * R) (N+count p R) :=
  le_trans (le_congr (by ipra_ring) (.eqRefl _)
    (le_mul_mono (le_refl (pw two (precision p))) (le_add_right (R*R) one))) (le_add_left _ _)

#print axioms joint_bound
#print axioms degree_budget
#print axioms index_budget

/-! ## The scheduled rational samples are jointly Cauchy -/

def sample (p z R B N : PTm n) : PTm n := finiteTail z B N (count p R) (degree p R)
def sampleDenominator (p R B N : PTm n) : PTm n := tailDenominator B N (count p R) (degree p R)
def sampleDifference (p k z R B N : PTm n) : PTm n :=
  crossDifference (sample p z R B N) (sample (p+k) z R B N) (sampleDenominator p R B N) (sampleDenominator (p+k) R B N)

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p z R B N : PTm n) :
    Syn.subst σ (sample p z R B N) = sample (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by
  simp only [sample, subst_finiteTail, subst_count, subst_degree]
@[simp] theorem subst_sampleDenominator {m : ℕ} (σ : Fin n → PTm m) (p R B N : PTm n) :
    Syn.subst σ (sampleDenominator p R B N) = sampleDenominator (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by
  simp only [sampleDenominator, subst_tailDenominator, subst_count, subst_degree]
@[simp] theorem subst_sampleDifference {m : ℕ} (σ : Fin n → PTm m) (p k z R B N : PTm n) :
    Syn.subst σ (sampleDifference p k z R B N) = sampleDifference (Syn.subst σ p) (Syn.subst σ k) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [sampleDifference, crossDifference]

theorem finiteTail_args (z B N : PTm n) {r r' L L' : PTm n}
    (hr : Γ ⊢[PRAAx] r ≐ r') (hL : Γ ⊢[PRAAx] L ≐ L') :
    Γ ⊢[PRAAx] finiteTail z B N r L ≐ finiteTail z B N r' L' := by
  have h := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (finiteTail (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![z,B,N,r,L]) (σ' := ![z,B,N,r',L'])
    (fun i => by fin_cases i <;> first | exact hr | exact hL | exact .eqRefl _)
  simpa using h

theorem tailDenominator_args (B N : PTm n) {r r' L L' : PTm n}
    (hr : Γ ⊢[PRAAx] r ≐ r') (hL : Γ ⊢[PRAAx] L ≐ L') :
    Γ ⊢[PRAAx] tailDenominator B N r L ≐ tailDenominator B N r' L' := by
  have h := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (tailDenominator (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![B,N,r,L]) (σ' := ![B,N,r',L'])
    (fun i => by fin_cases i <;> first | exact hr | exact hL | exact .eqRefl _)
  simpa using h

theorem norm_cross_congr (C : PTm n) {a a' b b' D D' E E' : PTm n}
    (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') (hD : Γ ⊢[PRAAx] D ≐ D') (hE : Γ ⊢[PRAAx] E ≐ E') :
    Γ ⊢[PRAAx] normSq (scale C (crossDifference a b D E)) ≐ normSq (scale C (crossDifference a' b' D' E')) := by
  have h := Prf.eqCongr (Ax := PRAAx) (Γ := Γ)
    (normSq (scale (var 0) (crossDifference (var 1) (var 2) (var 3) (var 4))) : PTm 5)
    (σ := ![C,a,b,D,E]) (σ' := ![C,a',b',D',E'])
    (fun i => by fin_cases i <;> first | exact ha | exact hb | exact hD | exact hE | exact .eqRefl _)
  simpa [crossDifference] using h

theorem sample_difference_joint (p k z R B N C : PTm n) :
    Γ ⊢[PRAAx] normSq (scale C (sampleDifference p k z R B N)) ≐
      normSq (scale C (jointDifference z B N (count p R) (gap p k R) (degree p R) (degreeGap p k R))) := by
  exact norm_cross_congr C (.eqRefl _) (finiteTail_args z B N (count_gap p k R) (degree_gap p k R))
    (.eqRefl _) (tailDenominator_args B N (count_gap p k R) (degree_gap p k R))

theorem sample_positive (p R B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (sampleDenominator p R B N) := tailDenominator_positive _ _ _ _ hB

theorem samples_joint_bound (p k z R B N : PTm n) (hz : Γ ⊢[PRAAx] bounded z (R*B))
    (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N) (hR : Γ ⊢[PRAAx] le (two*R) N) :
    Γ ⊢[PRAAx] bounded (scale (pw two (precision p)) (sampleDifference p k z R B N))
      (two * sampleDenominator p R B N * sampleDenominator (p+k) R B N) := by
  have joint := joint_bound z R B N (count p R) (gap p k R) (degree p R) (degreeGap p k R) (pw two (precision p))
    hz hB hN hR (degree_budget p R) (index_budget p R N)
  have later := tailDenominator_args (Γ := Γ) B N (count_gap p k R) (degree_gap p k R)
  have radius := congrMul (.eqRefl (two*sampleDenominator p R B N)) later.eqSymm
  exact le_congr (sample_difference_joint p k z R B N (pw two (precision p))).eqSymm (congrMul radius radius) joint

theorem unit_budget (p : PTm n) :
    Γ ⊢[PRAAx] DyadicComplexLogarithm.unit p * two ≐ pw two (precision p) := by
  have e : Γ ⊢[PRAAx] precision p ≐ succ (DyadicComplexLogarithm.precision p) := by
    unfold precision DyadicComplexLogarithm.precision
    ipra_ring
  exact ((congrAp2 powF e (.eqRefl two)).eqTrans (pw_succ two (DyadicComplexLogarithm.precision p))).eqSymm

/-- Actual jointly scheduled rational samples have a uniform dyadic modulus. -/
theorem samples_cauchy (p k z R B N : PTm n) (hz : Γ ⊢[PRAAx] bounded z (R*B))
    (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N) (hR : Γ ⊢[PRAAx] le (two*R) N) :
    Γ ⊢[PRAAx] bounded (scale (DyadicComplexLogarithm.unit p) (sampleDifference p k z R B N))
      (sampleDenominator p R B N * sampleDenominator (p+k) R B N) := by
  have budget : Γ ⊢[PRAAx] le
      (DyadicComplexLogarithm.unit p * (two*sampleDenominator p R B N*sampleDenominator (p+k) R B N))
      (pw two (precision p) * (sampleDenominator p R B N*sampleDenominator (p+k) R B N)) := by
    refine le_of_eq_add (d := zero) ?_
    ipra_lc -(𝔞(sampleDenominator p R B N)*𝔞(sampleDenominator (p+k) R B N))*natEq (unit_budget (Γ := Γ) p)
  exact bounded_budget _ _ _ _ _ (power_positive (precision p)) (samples_joint_bound p k z R B N hz hB hN hR) budget

#print axioms samples_joint_bound
#print axioms samples_cauchy

/-! ## Actual signed quotient observations of the joint rational samples -/

def observationTerm (p z R B N : PTm n) : PTm n :=
  rounded (sample p z R B N) (sampleDenominator p R B N) (DyadicComplexLogarithm.unit p)
def observationF : PR 5 := PTm.toPR (observationTerm (var 0) (var 1) (var 2) (var 3) (var 4))
def observation (p z R B N : PTm n) : PTm n := app observationF ![p,z,R,B,N]

@[simp] theorem subst_observationTerm {m : ℕ} (σ : Fin n → PTm m) (p z R B N : PTm n) :
    Syn.subst σ (observationTerm p z R B N) = observationTerm (Syn.subst σ p) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [observationTerm]
@[simp] theorem subst_observation {m : ℕ} (σ : Fin n → PTm m) (p z R B N : PTm n) :
    Syn.subst σ (observation p z R B N) = observation (Syn.subst σ p) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by
  change app _ _ = app _ _
  congr 1; funext i; fin_cases i <;> rfl

theorem observation_compute (p z R B N : PTm n) : Γ ⊢[PRAAx] observation p z R B N ≐ observationTerm p z R B N := by
  have h := toPR_eq (Γ := Γ) (observationTerm (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![p,z,R,B,N]
  simpa [observation, observationF] using h

theorem observation_later (p k z R B N : PTm n) :
    Γ ⊢[PRAAx] observation (p+k) z R B N ≐
      rounded (sample (p+k) z R B N) (sampleDenominator (p+k) R B N) (DyadicComplexLogarithm.unit p * pw two k) :=
  (observation_compute _ _ _ _ _).eqTrans
    (DyadicComplexLogarithm.congr_rounded (.eqRefl _) (.eqRefl _) (DyadicComplexLogarithm.unit_add p k))

def discrepancy (p k z R B N : PTm n) : PTm n :=
  add (observation (p+k) z R B N) (ComplexLogarithmRemainder.neg (scale (pw two k) (observation p z R B N)))

@[simp] theorem subst_discrepancy {m : ℕ} (σ : Fin n → PTm m) (p k z R B N : PTm n) :
    Syn.subst σ (discrepancy p k z R B N) = discrepancy (Syn.subst σ p) (Syn.subst σ k) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [discrepancy]

theorem discrepancy_compute (p k z R B N : PTm n) :
    Γ ⊢[PRAAx] discrepancy p k z R B N ≐
      roundedDifference (sample p z R B N) (sample (p+k) z R B N)
        (sampleDenominator p R B N) (sampleDenominator (p+k) R B N) (DyadicComplexLogarithm.unit p) (pw two k) :=
  DyadicComplexLogarithm.congr_add (observation_later p k z R B N)
    (DyadicComplexLogarithm.congr_neg (DyadicComplexLogarithm.congr_scale (observation_compute p z R B N)))

theorem regular_bound (p k z R B N : PTm n) (hz : Γ ⊢[PRAAx] bounded z (R*B))
    (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N) (hR : Γ ⊢[PRAAx] le (two*R) N) :
    Γ ⊢[PRAAx] bounded (discrepancy p k z R B N) (two + num 3 * pw two k) := by
  have rounded := DyadicComplexLogarithm.rounded_comparison
    (sample p z R B N) (sample (p+k) z R B N) (sampleDenominator p R B N) (sampleDenominator (p+k) R B N)
    (DyadicComplexLogarithm.unit p) (pw two k) (sample_positive p R B N hB) (sample_positive (p+k) R B N hB)
    (samples_cauchy p k z R B N hz hB hN hR)
  exact le_congr (congr_normSq (discrepancy_compute p k z R B N)).eqSymm (.eqRefl _) rounded

/-- With observation denominator `2^(p+4)`, this is stronger than the usual
regular-name error budget. No adjacent-rounding premise is assumed. -/
theorem regular_dyadic_bound (p k z R B N : PTm n) (hz : Γ ⊢[PRAAx] bounded z (R*B))
    (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N) (hR : Γ ⊢[PRAAx] le (two*R) N) :
    Γ ⊢[PRAAx] bounded (discrepancy p k z R B N) (num 5 * pw two k) := by
  refine bounded_mono (regular_bound p k z R B N hz hB hN hR) ?_
  refine le_of_eq_add (d := two * monus (pw two k) one) ?_
  ipra_lc 2 * natEq (eq_add_of_le (power_positive (Γ := Γ) k))

theorem observation_precision_congr {p q : PTm n} (z R B N : PTm n) (h : Γ ⊢[PRAAx] p ≐ q) :
    Γ ⊢[PRAAx] observation p z R B N ≐ observation q z R B N :=
  congrApp observationF (fun i => by fin_cases i <;> first | exact h | exact .eqRefl _)

def endpointDifference (p q z R B N : PTm n) : PTm n :=
  add (observation q z R B N) (ComplexLogarithmRemainder.neg (scale (pw two (monus q p)) (observation p z R B N)))

theorem regular_endpoints (p q z R B N : PTm n) (hz : Γ ⊢[PRAAx] bounded z (R*B))
    (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N) (hR : Γ ⊢[PRAAx] le (two*R) N)
    (order : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] bounded (endpointDifference p q z R B N) (num 5 * pw two (monus q p)) := by
  have eq := DyadicComplexLogarithm.congr_add
    (observation_precision_congr z R B N (eq_add_of_le order)) (.eqRefl (ComplexLogarithmRemainder.neg (scale (pw two (monus q p)) (observation p z R B N))))
  exact le_congr (congr_normSq eq).eqSymm (.eqRefl _) (regular_dyadic_bound p (monus q p) z R B N hz hB hN hR)

/-! ## Exact finite-sample connection and the source C6 observation bound -/

def observationError (p z R B N : PTm n) : PTm n :=
  add (scale (sampleDenominator p R B N) (observation p z R B N))
    (ComplexLogarithmRemainder.neg (scale (DyadicComplexLogarithm.unit p) (sample p z R B N)))

theorem observation_rounding (p z R B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (observationError p z R B N) (two * sampleDenominator p R B N) := by
  have eq := DyadicComplexLogarithm.congr_add (Γ := Γ)
    (DyadicComplexLogarithm.congr_scale (C := sampleDenominator p R B N) (observation_compute p z R B N))
    (.eqRefl (ComplexLogarithmRemainder.neg (scale (DyadicComplexLogarithm.unit p) (sample p z R B N))))
  exact le_congr (congr_normSq eq).eqSymm (.eqRefl _)
    (DyadicComplexLogarithm.rounding_bound (sample p z R B N) (sampleDenominator p R B N)
      (DyadicComplexLogarithm.unit p) (sample_positive p R B N hB))

theorem sample_disk_bound (p z R B N : PTm n) (hz : Γ ⊢[PRAAx] bounded z (R*B))
    (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N) (hR : Γ ⊢[PRAAx] le (two*R) N) :
    Γ ⊢[PRAAx] bounded (scale N (sample p z R B N)) (R*R*sampleDenominator p R B N) :=
  rational_disk_tail_bound _ _ _ _ _ _ hz hB hN hR

theorem observation_disk_identity (p z R B N : PTm n) :
    Γ ⊢[PRAAx] normSq (scale (sampleDenominator p R B N) (scale N (observation p z R B N))) ≐
      normSq (add (scale N (observationError p z R B N))
        (scale (DyadicComplexLogarithm.unit p) (scale N (sample p z R B N)))) := by
  apply deriveNat
  rw [normSq_eval, normSq_eval]
  simp only [observationError, add, ComplexLogarithmRemainder.neg, scale, eval_re_code, eval_im_code,
    ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat]
  ring

/-- C6 for the actual dyadic name, with only the proved quotient-rounding
slack `2/2^(p+4)` added to the sharp `R²/N` finite tail budget. -/
theorem observation_disk_bound (p z R B N : PTm n) (hz : Γ ⊢[PRAAx] bounded z (R*B))
    (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N) (hR : Γ ⊢[PRAAx] le (two*R) N) :
    Γ ⊢[PRAAx] bounded (scale N (observation p z R B N)) (R*R*DyadicComplexLogarithm.unit p + two*N) := by
  have first := bounded_scale N (observation_rounding p z R B N hB)
  have second := bounded_scale (DyadicComplexLogarithm.unit p) (sample_disk_bound p z R B N hz hB hN hR)
  have radius : Γ ⊢[PRAAx]
      N*(two*sampleDenominator p R B N) + DyadicComplexLogarithm.unit p*(R*R*sampleDenominator p R B N) ≐
      sampleDenominator p R B N*(R*R*DyadicComplexLogarithm.unit p + two*N) := by ipra_ring
  have combined := le_congr (observation_disk_identity p z R B N).eqSymm (congrMul radius radius) (bounded_add first second)
  exact cancel_bounded_scale (sample_positive p R B N hB) combined

#print axioms observation_compute
#print axioms regular_dyadic_bound
#print axioms regular_endpoints
#print axioms observation_rounding
#print axioms observation_disk_bound

/-! ## Public fixed programs and closed certificates -/

def sampleF : PR 5 := PTm.toPR (sample (var 0) (var 1) (var 2) (var 3) (var 4))
def sampleDenominatorF : PR 4 := PTm.toPR (sampleDenominator (var 0) (var 1) (var 2) (var 3))

theorem sample_at (p z R B N : PTm n) :
    Γ ⊢[PRAAx] app sampleF ![p,z,R,B,N] ≐ sample p z R B N := by
  simpa [sampleF] using toPR_eq (Γ := Γ) (sample (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![p,z,R,B,N]

theorem sampleDenominator_at (p R B N : PTm n) :
    Γ ⊢[PRAAx] app sampleDenominatorF ![p,R,B,N] ≐ sampleDenominator p R B N := by
  simpa [sampleDenominatorF] using toPR_eq (Γ := Γ) (sampleDenominator (var 0) (var 1) (var 2) (var 3) : PTm 4) ![p,R,B,N]

/-- Variables `p,k,R,N`; neither of the cutoff schedules is a metatheoretic
natural number. The two last inequalities are the separate error budgets. -/
def scheduleFormula : Fm PTm 4 :=
  (count (var 0+var 1) (var 2) ≐ count (var 0) (var 2) + gap (var 0) (var 1) (var 2)) ⋏
    ((degree (var 0+var 1) (var 2) ≐ degree (var 0) (var 2) + degreeGap (var 0) (var 1) (var 2)) ⋏
      (le (pw two (precision (var 0)) * count (var 0) (var 2)) (pw two (degree (var 0) (var 2))) ⋏
        le (pw two (precision (var 0)) * var 2 * var 2) (var 3+count (var 0) (var 2))))

theorem joint_schedule_certificate :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 scheduleFormula :=
  closeUniv 4 (.andI (count_gap _ _ _) (.andI (degree_gap _ _ _)
    (.andI (degree_budget _ _) (index_budget _ _ _))))

/-- Variables `p,k,z,R,B,N`; `z/B` is a rational complex input on the
integer-radius disk. This compares the actual finite samples, with both
index and Taylor cutoffs varying at the later precision. -/
def samplesFormula : Fm PTm 6 :=
  bounded (var 2) (var 3*var 4) ⟶ le one (var 4) ⟶ le one (var 5) ⟶ le (two*var 3) (var 5) ⟶
    (le one (sampleDenominator (var 0) (var 3) (var 4) (var 5)) ⋏
      (le one (sampleDenominator (var 0+var 1) (var 3) (var 4) (var 5)) ⋏
        bounded (scale (DyadicComplexLogarithm.unit (var 0))
          (sampleDifference (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))
          (sampleDenominator (var 0) (var 3) (var 4) (var 5) *
            sampleDenominator (var 0+var 1) (var 3) (var 4) (var 5))))

theorem joint_rational_samples_cauchy :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6 samplesFormula := by
  refine closeUniv 6 (.impI (.impI (.impI (.impI ?_))))
  exact .andI (sample_positive _ _ _ _ Prf.hyp1.wk) (.andI (sample_positive _ _ _ _ Prf.hyp1.wk)
    (samples_cauchy _ _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0))

/-- The actual PR5 observation divided by `2^(p+4)` is a regular dyadic
name for the joint power-series tail. This finite-query theorem does not
identify the represented limit with an analytic logarithm or Gamma. -/
def regularFormula : Fm PTm 6 :=
  bounded (var 2) (var 3*var 4) ⟶ le one (var 4) ⟶ le one (var 5) ⟶ le (two*var 3) (var 5) ⟶
    (le one (DyadicComplexLogarithm.unit (var 0)) ⋏
      bounded (discrepancy (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (num 5 * pw two (var 1)))

theorem primitive_recursive_joint_tail_name :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6 regularFormula := by
  refine closeUniv 6 (.impI (.impI (.impI (.impI ?_))))
  exact .andI (power_positive (DyadicComplexLogarithm.precision (var 0)))
    (regular_dyadic_bound _ _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)

/-- Variables `p,q,z,R,B,N`. The precision comparison itself is internal. -/
def endpointsFormula : Fm PTm 6 :=
  bounded (var 2) (var 3*var 4) ⟶ le one (var 4) ⟶ le one (var 5) ⟶ le (two*var 3) (var 5) ⟶
    le (var 0) (var 1) ⟶
      bounded (endpointDifference (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (num 5 * pw two (monus (var 1) (var 0)))

theorem joint_tail_name_ordered_precisions :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6 endpointsFormula := by
  refine closeUniv 6 (.impI (.impI (.impI (.impI (.impI ?_)))))
  exact regular_endpoints _ _ _ _ _ _ Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0

/-- Variables `p,z,R,B,N`. No disk hypothesis is needed for the exact
program equations, or for rounding at a positive computed denominator. -/
def programsFormula : Fm PTm 5 :=
  (app sampleF ![var 0,var 1,var 2,var 3,var 4] ≐ sample (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
    ((app sampleDenominatorF ![var 0,var 2,var 3,var 4] ≐ sampleDenominator (var 0) (var 2) (var 3) (var 4)) ⋏
      (observation (var 0) (var 1) (var 2) (var 3) (var 4) ≐
        rounded (sample (var 0) (var 1) (var 2) (var 3) (var 4))
          (sampleDenominator (var 0) (var 2) (var 3) (var 4)) (DyadicComplexLogarithm.unit (var 0))))

theorem joint_tail_programs :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 programsFormula :=
  closeUniv 5 (.andI (sample_at _ _ _ _ _) (.andI (sampleDenominator_at _ _ _ _) (observation_compute _ _ _ _ _)))

def roundingFormula : Fm PTm 5 :=
  le one (var 3) ⟶
    (le one (sampleDenominator (var 0) (var 2) (var 3) (var 4)) ⋏
      bounded (observationError (var 0) (var 1) (var 2) (var 3) (var 4))
        (two*sampleDenominator (var 0) (var 2) (var 3) (var 4)))

theorem joint_tail_sample_rounding :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 roundingFormula :=
  closeUniv 5 (.impI (.andI (sample_positive _ _ _ _ Prf.hyp0) (observation_rounding _ _ _ _ _ Prf.hyp0)))

def diskFormula : Fm PTm 5 :=
  bounded (var 1) (var 2*var 3) ⟶ le one (var 3) ⟶ le one (var 4) ⟶ le (two*var 2) (var 4) ⟶
    bounded (scale (var 4) (observation (var 0) (var 1) (var 2) (var 3) (var 4)))
      (var 2*var 2*DyadicComplexLogarithm.unit (var 0)+two*var 4)

theorem joint_tail_name_disk_bound :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 diskFormula := by
  refine closeUniv 5 (.impI (.impI (.impI (.impI ?_))))
  exact observation_disk_bound _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0

#print axioms joint_schedule_certificate
#print axioms joint_rational_samples_cauchy
#print axioms primitive_recursive_joint_tail_name
#print axioms joint_tail_name_ordered_precisions
#print axioms joint_tail_programs
#print axioms joint_tail_sample_rounding
#print axioms joint_tail_name_disk_bound

end LeanProofs.IPRA.Analysis.GammaCanonicalNames
