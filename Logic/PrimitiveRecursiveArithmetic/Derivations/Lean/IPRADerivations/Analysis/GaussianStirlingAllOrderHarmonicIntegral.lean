import IPRADerivations.Analysis.RationalReciprocalPowerTail
import IPRADerivations.Analysis.RationalHarmonicInterval
import IPRADerivations.Analysis.RationalNonnegativePowers

/-!
# Exact harmonic interval on an arbitrary rational grid

The finite rational sum of the reciprocals of consecutive grid integers
is the original factorial-scale harmonic interval. This identifies the
literal first-power summand needed by the first-order Stirling
partial-fraction decomposition.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderHarmonicIntegral

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB inst2_h)
open GammaEulerMesh (factorial_positive factorial_quotient)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product)
open RationalReciprocalPowerTail (tail tail_zero tail_succ reciprocalPower)
open RationalArithmetic (add)
open RationalIntegerNormalization (normalize normalize_preserves_value)
open RationalNormalForm (normalize_well_formed)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def numerator (N L T : PTm n) : ZT n := ⟨S (N+L) (fact T),S N (fact T)⟩
def value (N L T : PTm n) : PTm n := normalize (numerator N L T) (fact T)

@[simp] theorem subst_numerator {l : ℕ} (σ : Fin n → PTm l) (N L T : PTm n) :
    (numerator N L T).subst σ = numerator (Syn.subst σ N) (Syn.subst σ L) (Syn.subst σ T) :=
  by simp [numerator,ZT.subst,S]
@[simp] theorem subst_value {l : ℕ} (σ : Fin n → PTm l) (N L T : PTm n) :
    Syn.subst σ (value N L T) = value (Syn.subst σ N) (Syn.subst σ L) (Syn.subst σ T) :=
  by simp [value]

private theorem value_zero (N T : PTm n) : Γ ⊢[PRAAx] value N zero T ≐ fraction zero one := by
  have hF := factorial_positive (Γ := Γ) T
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (normalize_well_formed _ _ hF)
    (normalize_well_formed _ _ (le_refl one)) (normalize_preserves_value _ _ hF)
    (fraction_represents _ _ (le_refl one)) hF (le_refl one)
  apply ZT.derive (u := numerator N zero T*ZT.ofNat one) (v := ZT.ofNat zero*ZT.ofNat (fact T))
  have ee := natEq (congrAp2 (sumF hB) (add_zero (Γ := Γ) N) (.eqRefl (fact T)))
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [numerator,ZT.toZ]
  ipra_simps
  rw [ee]
  ring

private theorem value_succ (N L T : PTm n) (h : Γ ⊢[PRAAx] le (N+succ L) T) :
    Γ ⊢[PRAAx] add (value N L T) (reciprocalPower one (succ (N+L))) ≐ value N (succ L) T := by
  let F := fact T
  let j := succ (N+L)
  have hF : Γ ⊢[PRAAx] le one F := factorial_positive T
  have hj : Γ ⊢[PRAAx] le one j := zero_lt_succ _
  have hT : Γ ⊢[PRAAx] le j T := le_congr (add_succ N L) (.eqRefl _) h
  have ej := RationalNonnegativePowers.fraction_congr (.eqRefl one) (pw_one (Γ := Γ) j)
  refine (RationalAlgebra.add_congr (.eqRefl _) ej).eqTrans ?_
  have d := positive_product _ _ hF hj
  refine RationalFiniteSum.canonical_equal
    (add (value N L T) (fraction one j)) (value N (succ L) T) _ _ _ _
    (RationalArithmetic.add_guard _ _) (normalize_well_formed _ _ hF)
    (RationalRepresentations.represents_add _ _ _ _ _ _ (normalize_preserves_value _ _ hF)
      (fraction_represents _ _ hj)) (normalize_preserves_value _ _ hF) d hF ?_
  have e : Γ ⊢[PRAAx] S (N+succ L) F ≐ S (N+L) F+quo F j := by
    refine (congrAp2 (sumF hB) (add_succ N L) (.eqRefl _)).eqTrans ((sum_succ' hB _ _).eqTrans ?_)
    rw [inst2_h]
    exact .eqRefl _
  have eq := natEq (factorial_quotient j T hj hT)
  have eS := natEq e
  apply ZT.derive (u := (numerator N L T*ZT.ofNat j+ZT.ofNat one*ZT.ofNat F)*ZT.ofNat F)
    (v := numerator N (succ L) T*ZT.ofNat (F*j))
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
  simp only [numerator,ZT.toZ]
  ipra_simps
  linear_combination -𝔞(F)*eq-𝔞(F)*𝔞(j)*eS

def intervalLaw (N L T : PTm n) : Fm PTm n :=
  le (N+L) T ⟶ tail one N L ≐ value N L T

@[simp] theorem subst_intervalLaw {l : ℕ} (σ : Fin n → PTm l) (N L T : PTm n) :
    (intervalLaw N L T).subst σ = intervalLaw (Syn.subst σ N) (Syn.subst σ L) (Syn.subst σ T) :=
  by simp [intervalLaw]

theorem sum_at_factorial (N L T : PTm n) (h : Γ ⊢[PRAAx] le (N+L) T) :
    Γ ⊢[PRAAx] tail one N L ≐ value N L T := by
  have all : Γ ⊢[PRAAx] .all (intervalLaw (Syn.shift N) (var 0) (Syn.shift T)) := by
    refine PRA.qfInd _ ⟨trivial,trivial⟩ ?_ ?_
    · simp only [subst_intervalLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI ((tail_zero one N).eqTrans (value_zero N T).eqSymm)
    · simp only [subst_intervalLaw,subst_repl_shift]
      refine .impI ?_
      let N' := Syn.shift N
      let T' := Syn.shift T
      let Δ := le (N'+succ (var 0)) T' :: intervalLaw N' (var 0) T' :: Γ.map Fm.shift
      have below : Δ ⊢[PRAAx] le (N'+var 0) (N'+succ (var 0)) :=
        le_of_eq_add (d := one) (by ipra_ring)
      have ih := Prf.impE (Prf.hyp1 : Δ ⊢[PRAAx] intervalLaw N' (var 0) T')
        (le_trans below Prf.hyp0)
      exact (tail_succ one N' (var 0)).eqTrans
        ((RationalAlgebra.add_congr ih (.eqRefl _)).eqTrans (value_succ N' (var 0) T' Prf.hyp0))
  have ih : Γ ⊢[PRAAx] intervalLaw N L T := by
    simpa only [subst_intervalLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE L
  exact .impE ih h

theorem sum_at_original (A B Q : PTm n) :
    Γ ⊢[PRAAx] tail one (Q*A) (Q*B) ≐ RationalHarmonicInterval.interval (A+B) A Q := by
  let T := RationalHarmonicInterval.horizon (A+B) A Q
  have e : Γ ⊢[PRAAx] Q*A+Q*B ≐ Q*(A+B) := by ipra_ring
  have hb := le_congr e.eqSymm (.eqRefl _) (RationalHarmonicInterval.left_horizon (A+B) A Q)
  refine (sum_at_factorial (Q*A) (Q*B) T hb).eqTrans ?_
  have hF := factorial_positive (Γ := Γ) T
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (normalize_well_formed _ _ hF) (RationalHarmonicInterval.common_canonical (A+B) A Q T)
    (normalize_preserves_value _ _ hF) (RationalHarmonicInterval.common_value (A+B) A Q T) hF hF
  have eq := natEq (congrAp2 (sumF hB) e (.eqRefl (fact T)))
  apply ZT.derive (u := numerator (Q*A) (Q*B) T*ZT.ofNat (fact T))
    (v := RationalHarmonicInterval.numerator (A+B) A Q T*ZT.ofNat (fact T))
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [numerator,RationalHarmonicInterval.numerator,ZT.toZ]
  rw [eq]

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderHarmonicIntegral
