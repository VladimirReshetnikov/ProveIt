import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaCanonicalTailName
import IPRADerivations.Core.CongruenceTactic

/-!
# The original finite canonical Gamma tail and its first factor

Every original quotient multiplier is proved exact on the original
stored horizon. A genuine guarded QF representation induction therefore
identifies the SAME old numerator/denominator program with the actual
Gaussian sum of the SAME normalized old factors. The existing real
finite-sum first-term split then gives a literal canonical-code identity
with the actual successor-start tail and its different own denominator.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCanonicalTailFiniteSplit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (ofGaussian ofGaussian_represents ofGaussian_canonical represents represents_congr
  qzero qadd canonical_unique positive_product)
open GaussianRationalSyntheticDivision (qadd_congr)
open GammaCanonicalFactors (factorNumerator factorDenominator finiteSum finiteTail tailDenominator summand)
open GaussianRationalFiniteSum (sum sum_canonical)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def term (z B k L : PTm n) : PTm n := GammaLogarithmFactorBridge.localFactor z (B*k) L
def data (z B N L : PTm n) : PTm n := pairT z (pairT B (pairT N L))
def body : PTm 2 := term (fstT (var 1)) (fstT (sndT (var 1)))
  (succ (fstT (sndT (sndT (var 1)))+var 0)) (sndT (sndT (sndT (var 1))))
def gaussianSum (z B N r L : PTm n) : PTm n := sum body r (data z B N L)
def value (z B N r L : PTm n) : PTm n := ofGaussian (finiteTail z B N r L) (tailDenominator B N r L)
@[simp] theorem subst_term {l : ℕ} (σ : Fin n → PTm l) (z B k L : PTm n) :
    Syn.subst σ (term z B k L) = term (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ k) (Syn.subst σ L) := by simp [term]
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (z B N L : PTm n) :
    Syn.subst σ (data z B N L) = data (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ L) := by simp [data]
@[simp] theorem subst_gaussianSum {l : ℕ} (σ : Fin n → PTm l) (z B N r L : PTm n) :
    Syn.subst σ (gaussianSum z B N r L) = gaussianSum (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) (Syn.subst σ L) := by simp [gaussianSum]
@[simp] theorem subst_value {l : ℕ} (σ : Fin n → PTm l) (z B N r L : PTm n) :
    Syn.subst σ (value z B N r L) = value (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) (Syn.subst σ L) := by simp [value]

theorem term_index_congr (z B L : PTm n) {i j : PTm n} (h : Γ ⊢[PRAAx] i ≐ j) : Γ ⊢[PRAAx] term z B i L ≐ term z B j L := by
  ipra_congr (term (var 0) (var 1) (var 2) (var 3) : PTm 4) with [.eqRefl z, .eqRefl B, h, .eqRefl L]
theorem body_at (z B N L i : PTm n) : Γ ⊢[PRAAx] inst2 body i (data z B N L) ≐ term z B (succ (N+i)) L := by
  simp only [body,inst2,subst_term,subst_fstT,subst_sndT,PTm.subst_add,ConciseIPRA.PTm.subst_succ,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  simpa only [subst_term,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (term (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![fstT (data z B N L),fstT (sndT (data z B N L)),succ (fstT (sndT (sndT (data z B N L)))+i),sndT (sndT (sndT (data z B N L)))])
      (σ' := ![z,B,succ (N+i),L]) (fun a => by
        fin_cases a
        · exact fst_pair _ _
        · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
        · exact congrSucc (congrAdd ((congrFst ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)) (.eqRefl _))
        · exact (congrSnd ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))
theorem gaussian_sum_zero (z B N L : PTm n) : Γ ⊢[PRAAx] gaussianSum z B N zero L ≐ qzero :=
  GaussianRationalFiniteSum.sum_zero _ _
theorem gaussian_sum_succ (z B N r L : PTm n) : Γ ⊢[PRAAx] gaussianSum z B N (succ r) L ≐
    qadd (gaussianSum z B N r L) (term z B (succ (N+r)) L) :=
  (GaussianRationalFiniteSum.sum_succ _ _ _).eqTrans (qadd_congr (.eqRefl _) (body_at z B N L r))

/-- The actual old quotient is exact inside the original fixed horizon. -/
theorem term_represents (z B N r L i : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hi : Γ ⊢[PRAAx] lt i r) : Γ ⊢[PRAAx]
    represents (term z B (succ (N+i)) L) (summand z B (succ (N+i)) L (tailDenominator B N r L)) (tailDenominator B N r L) := by
  have d := GammaCanonicalFactors.factorDenominator_positive (B*succ (N+i)) L
    (positive_product _ _ hB (zero_lt_succ _))
  exact GaussianRationalSyntheticDivision.rescale_to _ _ _ _ _ (ofGaussian_represents _ _ d)
    (GammaCanonicalFactors.tail_quotient_clears B N r L i hB hi)

def prefixLaw (z B N r L j : PTm n) : Fm PTm n := le j r ⟶
  represents (gaussianSum z B N j L) (finiteSum z B N j L (tailDenominator B N r L)) (tailDenominator B N r L)
@[simp] theorem subst_prefixLaw {l : ℕ} (σ : Fin n → PTm l) (z B N r L j : PTm n) :
    (prefixLaw z B N r L j).subst σ = prefixLaw (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N)
      (Syn.subst σ r) (Syn.subst σ L) (Syn.subst σ j) := by simp [prefixLaw]
theorem prefix_zero (z B N r L : PTm n) : Γ ⊢[PRAAx] prefixLaw z B N r L zero :=
  .impI (represents_congr (gaussian_sum_zero _ _ _ _).wk.eqSymm
    (GaussianRootAlgebra.equal_of_code (GammaCanonicalFactors.sum_zero _ _ _ _ _).wk.eqSymm) (.eqRefl _)
    (GaussianRationalHorner.zero_represents _))
theorem prefix_step (z B N r L j : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ih : Γ ⊢[PRAAx] prefixLaw z B N r L j) : Γ ⊢[PRAAx] prefixLaw z B N r L (succ j) := by
  refine .impI ?_
  have previous := Prf.impE ih.wk (le_trans (le_succ_self j) Prf.hyp0)
  have added := GaussianRationalHorner.qadd_represents _ _ _ _ _
    (GammaCanonicalFactors.tailDenominator_positive B N r L hB.wk) previous
    (term_represents z B N r L j hB.wk Prf.hyp0)
  exact represents_congr (gaussian_sum_succ _ _ _ _ _).eqSymm
    (GaussianRootAlgebra.equal_of_code (GammaCanonicalFactors.sum_succ _ _ _ _ _ _).eqSymm) (.eqRefl _) added

theorem prefix_represents (z B N r L j : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hj : Γ ⊢[PRAAx] le j r) : Γ ⊢[PRAAx]
    represents (gaussianSum z B N j L) (finiteSum z B N j L (tailDenominator B N r L)) (tailDenominator B N r L) := by
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift z) (Syn.shift B) (Syn.shift N) (Syn.shift r) (Syn.shift L) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,⟨trivial,trivial⟩⟩ ?_ ?_
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using prefix_zero (Γ := Γ) z B N r L
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact prefix_step _ _ _ _ _ _ bs.wk Prf.hyp0
  have atj : Γ ⊢[PRAAx] prefixLaw z B N r L j := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE atj hj

/-- Literal CODE equality of normalized outputs, with actual denominators. -/
theorem finite_value_as_sum (z B N r L : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    value z B N r L ≐ gaussianSum z B N r L :=
  canonical_unique _ _ _ _ (ofGaussian_canonical _ _ (GammaCanonicalFactors.tailDenominator_positive B N r L hB))
    (sum_canonical _ _ _) (GammaCanonicalFactors.tailDenominator_positive B N r L hB)
    (ofGaussian_represents _ _ (GammaCanonicalFactors.tailDenominator_positive B N r L hB))
    (prefix_represents z B N r L r hB (le_refl r))

theorem suffix_terms (z B N r L : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.termsEqual (shiftBody body) body r (data z B N L) (data z B (succ N) L) := by
  refine .allI (.impI ?_)
  have left := body_at (Γ := lt (var 0) (Syn.shift r) :: Γ.map Fm.shift)
    (Syn.shift z) (Syn.shift B) (Syn.shift N) (Syn.shift L) (succ (var 0))
  have right := body_at (Γ := lt (var 0) (Syn.shift r) :: Γ.map Fm.shift)
    (Syn.shift z) (Syn.shift B) (succ (Syn.shift N)) (Syn.shift L) (var 0)
  simpa only [inst2_shiftBody,subst_data,Syn.shift,ConciseIPRA.PTm.subst_succ] using
    left.eqTrans ((term_index_congr _ _ _ (by ipra_ring)).eqTrans right.eqSymm)
theorem gaussian_sum_first (z B N r L : PTm n) : Γ ⊢[PRAAx] gaussianSum z B N (succ r) L ≐
    qadd (term z B (succ N) L) (gaussianSum z B (succ N) r L) :=
  (GaussianRationalFiniteSum.sum_shift_first body r (data z B N L)).eqTrans
    (qadd_congr ((body_at z B N L zero).eqTrans (term_index_congr z B L (congrSucc (add_zero N))))
      (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ (suffix_terms z B N r L)))

/-- The actual old finite tail splits at its actual first normalized
factor and successor tail, whose own product denominator is retained. -/
theorem finite_value_first (z B N r L : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    value z B N (succ r) L ≐ qadd (term z B (succ N) L) (value z B (succ N) r L) :=
  (finite_value_as_sum z B N (succ r) L hB).eqTrans ((gaussian_sum_first z B N r L).eqTrans
    (qadd_congr (.eqRefl _) (finite_value_as_sum z B (succ N) r L hB).eqSymm))

theorem value_canonical (z B N r L : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (value z B N r L) :=
  ofGaussian_canonical _ _ (GammaCanonicalFactors.tailDenominator_positive B N r L hB)
/-- Exact finite C6 in the actual Gaussian metric. -/
theorem value_bound (z R B N r L : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalTailName.source z R B N) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (value z B N r L) (R*R) N := by
  have native := GammaCanonicalFactors.rational_disk_tail_bound z R B N r L h.andE₂.andE₂.andE₁ h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₂
  exact GaussianRationalMetric.bounded_of_cleared _ _ _ _ _
    (GammaCanonicalFactors.tailDenominator_positive B N r L h.andE₁) h.andE₂.andE₁
    (ofGaussian_represents _ _ (GammaCanonicalFactors.tailDenominator_positive B N r L h.andE₁))
    (le_congr (ComplexLogarithmRemainder.normSq_scale _ _) (by ipra_ring) native)

def output (z B N r L : PTm n) : PTm n := pairT (value z B N (succ r) L)
  (pairT (term z B (succ N) L) (value z B (succ N) r L))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (z B N r L : PTm n) : PTm n := PTm.app outputF ![z,B,N,r,L]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (z B N r L : PTm n) :
    Syn.subst σ (output z B N r L) = output (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) (Syn.subst σ L) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (z B N r L : PTm n) :
    Syn.subst σ (run z B N r L) = run (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) (Syn.subst σ L) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (z B N r L : PTm n) : Γ ⊢[PRAAx] run z B N r L ≐ output z B N r L := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![z,B,N,r,L]
theorem returned_value (z B N r L : PTm n) : Γ ⊢[PRAAx] fstT (run z B N r L) ≐ value z B N (succ r) L :=
  (congrFst (program_at _ _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_parts (z B N r L : PTm n) : Γ ⊢[PRAAx] sndT (run z B N r L) ≐ pairT (term z B (succ N) L) (value z B (succ N) r L) :=
  (congrSnd (program_at _ _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_first (z B N r L : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run z B N r L)) ≐ term z B (succ N) L :=
  (congrFst (returned_parts _ _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_suffix (z B N r L : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run z B N r L)) ≐ value z B (succ N) r L :=
  (congrSnd (returned_parts _ _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_split (z B N r L : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    fstT (run z B N r L) ≐ qadd (fstT (sndT (run z B N r L))) (sndT (sndT (run z B N r L))) :=
  (returned_value _ _ _ _ _).eqTrans ((finite_value_first z B N r L hB).eqTrans
    (qadd_congr (returned_first _ _ _ _ _).eqSymm (returned_suffix _ _ _ _ _).eqSymm))

theorem actual_old_finite_tail_gaussian_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ value (var 0) (var 1) (var 2) (var 3) (var 4) ≐ gaussianSum (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (finite_value_as_sum _ _ _ _ _ Prf.hyp0))
theorem actual_normalized_old_tail_first_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ value (var 0) (var 1) (var 2) (succ (var 3)) (var 4) ≐
      qadd (term (var 0) (var 1) (succ (var 2)) (var 4)) (value (var 0) (var 1) (succ (var 2)) (var 3) (var 4))) :=
  closeUniv 5 (.impI (finite_value_first _ _ _ _ _ Prf.hyp0))
theorem original_finite_tail_gaussian_C6_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (GaussianGammaCanonicalTailName.source (var 0) (var 1) (var 2) (var 3) ⟶
      GaussianRationalMetric.bounded (value (var 0) (var 2) (var 3) (var 4) (var 5)) (var 1*var 1) (var 3)) :=
  closeUniv 6 (.impI (value_bound _ _ _ _ _ _ Prf.hyp0))
theorem actual_finite_tail_split_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)
theorem original_returned_finite_tail_split_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐
      qadd (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))) :=
  closeUniv 5 (.impI (returned_split _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaCanonicalTailFiniteSplit
