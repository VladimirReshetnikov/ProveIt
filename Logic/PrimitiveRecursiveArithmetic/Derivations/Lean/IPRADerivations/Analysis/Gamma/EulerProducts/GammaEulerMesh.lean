import IPRADerivations.AnalyticNumberTheory.MeshChange
import IPRADerivations.Analysis.Optimization.CubeInfimum.RationalCubeInfimumIntervals
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalSyntheticBounds

/-!
# Exact Euler-constant mesh approximants

The actual sampler is H_N-(H_(KN)-H_K), with its own positive
factorial denominator (KN)!. Literal normalization transports it to any
larger factorial. The synchronous mesh comparison is the sharp finite
inequality behind source Gamma C1, not yet identification of H_(KN)-H_K
with a particular completed logarithm name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GammaEulerMesh

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (S_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.MeshChange (S_denom)
open LeanProofs.IPRA.AnalyticNumberTheory.LogRefinement (log_refine)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos dvd_fact)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Products (fact)
open RationalIntegerNormalization (normalize)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalArithmetic (represents)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def numerator (N K L : PTm n) : ZT n :=
  ⟨S N (fact L)+S K (fact L), S (K*N) (fact L)⟩
def commonSample (N K L : PTm n) : PTm n := normalize (numerator N K L) (fact L)
def sample (N K : PTm n) : PTm n := commonSample N K (K*N)

ipra_subst numerator [ZT.subst, S]
ipra_subst commonSample
ipra_subst sample

theorem factorial_positive (L : PTm n) : Γ ⊢[PRAAx] le one (fact L) :=
  le_congr (.eqRefl _) (fact_pos L).eqSymm (zero_lt_succ _)

theorem common_value (N K L : PTm n) : Γ ⊢[PRAAx] represents (commonSample N K L) (numerator N K L) (fact L) :=
  RationalIntegerNormalization.normalize_preserves_value _ _ (factorial_positive L)

theorem common_canonical (N K L : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (commonSample N K L) :=
  RationalNormalForm.normalize_well_formed _ _ (factorial_positive L)

/-- The computed denominator is changed without changing the literal rational code. -/
theorem sample_at_common (N K L : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hK : Γ ⊢[PRAAx] le one K) (hL : Γ ⊢[PRAAx] le (K*N) L) :
    Γ ⊢[PRAAx] commonSample N K L ≐ sample N K := by
  have hNK : Γ ⊢[PRAAx] le N (K*N) := by ipra_le 𝔞 N*sl hK
  have hKK : Γ ⊢[PRAAx] le K (K*N) := by ipra_le 𝔞 K*sl hN
  have eN := natEq (S_denom hNK hL)
  have eK := natEq (S_denom hKK hL)
  have eKN := natEq (S_denom (le_refl (K*N)) hL)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (common_canonical N K L)
    (common_canonical N K (K*N)) (common_value N K L) (common_value N K (K*N))
    (factorial_positive L) (factorial_positive (K*N))
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [numerator,ZT.toZ]
  ipra_simps
  linear_combination eN+eK-eKN

/-- Every positive small divisor cancels the chosen factorial exactly. -/
theorem factorial_quotient (d L : PTm n) (hd : Γ ⊢[PRAAx] le one d) (hL : Γ ⊢[PRAAx] le d L) :
    Γ ⊢[PRAAx] d*quo (fact L) d ≐ fact L := by
  have pos := pos_of_one_le hd
  have dv := dvd_fact (le_congr pos (.eqRefl _) hL)
  have rem : Γ ⊢[PRAAx] rem (fact L) d ≐ zero := (congrAp2 remF (.eqRefl _) pos).eqTrans dv
  exact ((Prf.andE₁ (div_mod_at (Γ := Γ) (x := fact L) pos)).eqTrans
    ((congrAdd (.eqRefl _) rem).eqTrans (add_zero _))).eqSymm

/-- The two sharp C1 inequalities on one proved exact factorial scale. -/
theorem synchronous_cleared (N M K L : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hNM : Γ ⊢[PRAAx] le N M) (hK : Γ ⊢[PRAAx] le one K)
    (hL : Γ ⊢[PRAAx] le (K*M) L) : Γ ⊢[PRAAx]
    le (S M (fact L)+S (K*N) (fact L)) (S N (fact L)+S (K*M) (fact L)) ⋏
      le (N*M*(S N (fact L)+S (K*M) (fact L)))
        (N*M*(S M (fact L)+S (K*N) (fact L))+monus M N*fact L) := by
  have pN := pos_of_one_le hN
  have hM := le_trans hN hNM
  have pM := pos_of_one_le hM
  have e : Γ ⊢[PRAAx] succ (pred N)+monus M N ≐ M :=
    (congrAdd pN.eqSymm (.eqRefl _)).eqTrans (eq_add_of_le hNM).eqSymm
  have lr := log_refine (pos_of_one_le hK) (le_congr (congrMul (.eqRefl K) e).eqSymm (.eqRefl _) hL)
  have eN := natEq (congrAp2 (sumF hB) pN.eqSymm (.eqRefl (fact L)))
  have eKM := natEq (congrAp2 (sumF hB) (congrMul (.eqRefl K) e) (.eqRefl (fact L)))
  have eKN := natEq (congrAp2 (sumF hB) (congrMul (.eqRefl K) pN.eqSymm) (.eqRefl (fact L)))
  have low : Γ ⊢[PRAAx] le (S M (fact L)+S (K*N) (fact L)) (S N (fact L)+S (K*M) (fact L)) := by
    ipra_le sl lr.andE₁ using linear_combination natEq (congrAp2 (sumF hB) e (.eqRefl (fact L)))+eKN-eKM-eN
  have ep : Γ ⊢[PRAAx] pred N+monus M N ≐ pred M := by
    ipra_lc -natEq pN+natEq pM-natEq (eq_add_of_le hNM)
  have esN := natEq ((congrAp2 (sumF hB) pN (.eqRefl (fact L))).eqTrans
    ((S_succ (pred N) (fact L)).eqTrans (congrAdd (.eqRefl _) (congrAp2 quoF (.eqRefl _) pN.eqSymm))))
  have esM := natEq ((congrAp2 (sumF hB) pM (.eqRefl (fact L))).eqTrans
    ((S_succ (pred M) (fact L)).eqTrans (congrAdd (.eqRefl _) (congrAp2 quoF (.eqRefl _) pM.eqSymm))))
  have up : Γ ⊢[PRAAx] le (S N (fact L)+S (K*M) (fact L)+quo (fact L) M)
      (S M (fact L)+S (K*N) (fact L)+quo (fact L) N) := by
    ipra_le sl lr.andE₂ using linear_combination eKM-eKN-natEq (congrAp2 (sumF hB) ep (.eqRefl (fact L)))-esN+esM
  have mL : Γ ⊢[PRAAx] le M L := le_trans (by ipra_le 𝔞 M*sl hK) hL
  have qN := natEq (factorial_quotient N L hN (le_trans hNM mL))
  have qM := natEq (factorial_quotient M L hM mL)
  have d := natEq (eq_add_of_le hNM)
  refine .andI low ?_
  ipra_le 𝔞 (N*M)*sl up using linear_combination -𝔞 M*qN+𝔞 N*qM-𝔞 (fact L)*d

theorem synchronous_common (N M K L : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hNM : Γ ⊢[PRAAx] le N M) (hK : Γ ⊢[PRAAx] le one K)
    (hL : Γ ⊢[PRAAx] le (K*M) L) : Γ ⊢[PRAAx]
    rationalLE (commonSample M K L) (commonSample N K L) ⋏
      RationalValueBounds.upper (commonSample N K L) (commonSample M K L) (monus M N) (N*M) := by
  have bounds := synchronous_cleared N M K L hN hNM hK hL
  refine .andI ?_ ?_
  · apply RationalArithmetic.order_of_representations _ _ _ _ _ _ (common_value M K L) (common_value N K L)
      (factorial_positive L) (factorial_positive L)
    apply zle_of_toZ (fact L*monus (S N (fact L)+S (K*M) (fact L)) (S M (fact L)+S (K*N) (fact L)))
    have e := natEq (eq_add_of_le bounds.andE₁)
    simp only [ZT.toZ_mul,ZT.toZ_ofNat]
    simp only [numerator,ZT.toZ]
    ipra_simps
    linear_combination -𝔞 (fact L)*e
  · apply RationalCubeInfimumIntervals.upper_of_representations _ _ _ _ _ _ _ _
      (factorial_positive L) (factorial_positive L) (common_value N K L) (common_value M K L)
    apply zle_of_toZ (fact L*monus
      (N*M*(S M (fact L)+S (K*N) (fact L))+monus M N*fact L)
      (N*M*(S N (fact L)+S (K*M) (fact L))))
    have e := natEq (eq_add_of_le bounds.andE₂)
    simp only [ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat]
    simp only [numerator,ZT.toZ]
    ipra_simps
    linear_combination -𝔞 (fact L)*e

/-- Exact C1 on the independently normalized original samples. -/
theorem synchronous_samples (N M K : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hNM : Γ ⊢[PRAAx] le N M) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    rationalLE (sample M K) (sample N K) ⋏
      RationalValueBounds.upper (sample N K) (sample M K) (monus M N) (N*M) := by
  have hM := le_trans hN hNM
  have hKN : Γ ⊢[PRAAx] le (K*N) (K*M) := le_mul_mono (le_refl K) hNM
  have a := sample_at_common N K (K*M) hN hK hKN
  have b := sample_at_common M K (K*M) hM hK (le_refl _)
  have h := synchronous_common N M K (K*M) hN hNM hK (le_refl _)
  exact .andI (rationalLE_congr b a h.andE₁)
    (RationalValueBounds.upper_congr a b (.eqRefl _) (.eqRefl _) h.andE₂)

theorem common_range (N K L : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hK : Γ ⊢[PRAAx] le one K) (hL : Γ ⊢[PRAAx] le (K*N) L) : Γ ⊢[PRAAx]
    rationalLE (GaussianRationalSyntheticBounds.natCode zero) (commonSample N K L) ⋏
      rationalLE (commonSample N K L) (GaussianRationalSyntheticBounds.natCode one) := by
  have pos := pos_of_one_le hN
  have e : Γ ⊢[PRAAx] succ zero+pred N ≐ N := (by ipra_ring : Γ ⊢[PRAAx] succ zero+pred N ≐ succ (pred N)).eqTrans pos.eqSymm
  have lr := log_refine (pos_of_one_le hK) (le_congr (congrMul (.eqRefl K) e).eqSymm (.eqRefl _) hL)
  have ea := natEq (congrAp2 (sumF hB) e (.eqRefl (fact L)))
  have eb := natEq (congrAp2 (sumF hB) (congrMul (.eqRefl K) e) (.eqRefl (fact L)))
  have ec := natEq (congrAp2 (sumF hB) (by ipra_ring : Γ ⊢[PRAAx] K*one ≐ K) (.eqRefl (fact L)))
  have ez := natEq (sum_zero (Γ := Γ) hB (fact L))
  have e1 := natEq (LeanProofs.IPRA.AnalyticNumberTheory.Harmonic.S_one (Γ := Γ) (fact L))
  have epow := natEq (congrAp2 (sumF hB) (pw_zero (Γ := Γ) two) (.eqRefl (fact L)))
  have epred := natEq (congrAp2 (sumF hB) (zero_add (Γ := Γ) (pred N)) (.eqRefl (fact L)))
  have mono := LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev.S_mono (fact L)
    (le_congr (.eqRefl _) pos.eqSymm (le_succ_self (pred N)))
  have nonneg : Γ ⊢[PRAAx] le (S (K*N) (fact L)) (S N (fact L)+S K (fact L)) := by
    ipra_le sl lr.andE₂+sl mono using linear_combination eb-ec+ez-epred
  have upper : Γ ⊢[PRAAx] le (S N (fact L)+S K (fact L)) (S (K*N) (fact L)+fact L) := by
    ipra_le sl lr.andE₁ using linear_combination ea+ec-eb-e1+epow
  refine .andI ?_ ?_
  · apply RationalArithmetic.order_of_representations _ _ _ _ _ _
      (GaussianRationalSyntheticBounds.natCode_represents zero) (common_value N K L)
      (le_refl one) (factorial_positive L)
    apply zle_of_toZ (monus (S N (fact L)+S K (fact L)) (S (K*N) (fact L)))
    have e := natEq (eq_add_of_le nonneg)
    simp only [ZT.toZ_mul,ZT.toZ_ofNat]
    simp only [numerator,ZT.toZ]
    ipra_simps
    linear_combination -e
  · apply RationalArithmetic.order_of_representations _ _ _ _ _ _ (common_value N K L)
      (GaussianRationalSyntheticBounds.natCode_represents one) (factorial_positive L) (le_refl one)
    apply zle_of_toZ (monus (S (K*N) (fact L)+fact L) (S N (fact L)+S K (fact L)))
    have e := natEq (eq_add_of_le upper)
    simp only [ZT.toZ_mul,ZT.toZ_ofNat]
    simp only [numerator,ZT.toZ]
    ipra_simps
    linear_combination -e

theorem sample_range (N K : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    rationalLE (GaussianRationalSyntheticBounds.natCode zero) (sample N K) ⋏
      rationalLE (sample N K) (GaussianRationalSyntheticBounds.natCode one) :=
  common_range N K (K*N) hN hK (le_refl _)

def sampleF : PR 2 := PTm.toPR (sample (var 0) (var 1))
def run (N K : PTm n) : PTm n := ap2 sampleF N K

theorem program_at (N K : PTm n) : Γ ⊢[PRAAx] run N K ≐ sample N K := by
  simpa [run,sampleF,ap2] using toPR_eq (Γ := Γ) (sample (var 0) (var 1) : PTm 2) ![N,K]

theorem actual_mesh_gamma_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ sample (var 0) (var 1)) := closeUniv 2 (program_at _ _)

theorem original_synchronous_C1_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ le (var 0) (var 1) ⟶ le one (var 2) ⟶
      rationalLE (sample (var 1) (var 2)) (sample (var 0) (var 2)) ⋏
      RationalValueBounds.upper (sample (var 0) (var 2)) (sample (var 1) (var 2))
        (monus (var 1) (var 0)) (var 0*var 1)) :=
  closeUniv 3 (.impI (.impI (.impI (synchronous_samples _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem original_mesh_gamma_range_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ le one (var 1) ⟶
      rationalLE (GaussianRationalSyntheticBounds.natCode zero) (sample (var 0) (var 1)) ⋏
      rationalLE (sample (var 0) (var 1)) (GaussianRationalSyntheticBounds.natCode one)) :=
  closeUniv 2 (.impI (.impI (sample_range _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GammaEulerMesh
