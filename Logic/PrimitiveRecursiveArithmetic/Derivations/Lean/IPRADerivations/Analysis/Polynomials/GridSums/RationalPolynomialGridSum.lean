import IPRADerivations.Analysis.RationalArithmetic.Powers.RationalPowerMoments
import IPRADerivations.Analysis.Series.BernoulliBounds
import IPRADerivations.Foundations.NumeralPrimes

/-!
# Literal rational polynomial grid sums

The scalar fold of a sampled polynomial is the cleared linear
combination of the actual natural power sums. The grid denominator
is fixed during the whole prefix.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.RationalPolynomialGridSum

open_ipra
open BernoulliBounds (pv zint toZ_zint)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product)
open RationalAlgebra (add_congr)
open RationalArithmetic (multiply)
open RationalFiniteSum (sum term canonical_equal)
open RationalIntegerNormalization (normalize normalize_preserves_value)
open RationalNormalForm (normalize_well_formed)
open RationalPowerMoments (naturalSum)

variable {n d : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" x:max => Groth.ι (Q.mk Γ x)

def rowDen (d D : ℕ) (M : PTm n) : PTm n := num D * pw M (num d)

def body (a : Fin (d+1) → ℤ) (D : ℕ) : PTm 2 :=
  normalize (pv a (var 0) (var 1)) (rowDen d D (var 1))

def prefixNumerator (a : Fin (d+1) → ℤ) (N M : PTm n) : ZT n :=
  ZT.sumFin fun i => zint (a i)*ZT.ofNat (naturalSum (num i) N*pw M (num (d-i)))

private theorem subst_sumFin {l k : ℕ} (σ : Fin n → PTm l) (f : Fin k → ZT n) :
    (ZT.sumFin f).subst σ = ZT.sumFin (fun i => (f i).subst σ) := by
  induction k with
  | zero => simp [ZT.sumFin, ZT.natLit]
  | succ k ih => simp only [ZT.sumFin,ZT.subst_add,ih]

ipra_subst rowDen [pw]

ipra_subst prefixNumerator [subst_sumFin, zint, ZT.natLit, pw]

theorem body_at (a : Fin (d+1) → ℤ) (D : ℕ) (i M : PTm n) :
    term (body a D) i M = normalize (pv a i M) (rowDen d D M) := by
  simp [body,term,inst2,pv,subst_sumFin,zint,ZT.natLit,pw]

theorem denominator_positive (d D : ℕ) (hD : 0 < D) (M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] le one (rowDen d D M) :=
  positive_product _ _ (Foundations.NumeralPrimes.num_le hD) (GaussianFactorBudget.power_positive _ _ hM)

private theorem prefix_zero (a : Fin (d+1) → ℤ) (M : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (prefixNumerator a zero M) (ZT.ofNat zero) := by
  have h (i : Fin (d+1)) : 𝔞(naturalSum (num i) zero) = 0 := by
    simpa [naturalSum] using natEq (LeanProofs.IPRA.sum_zero (Γ := Γ) PowerSums.Bq (num i : PTm n))
  apply ZT.derive
  simp [prefixNumerator,ZT.toZ_mul,toZ_zint,ZT.toZ_ofNat,Q.mk_mul,map_mul,h]

private theorem prefix_succ (a : Fin (d+1) → ℤ) (N M : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (prefixNumerator a (succ N) M) (prefixNumerator a N M+pv a N M) := by
  have h (i : Fin (d+1)) : 𝔞(naturalSum (num i) (succ N)) = 𝔞(naturalSum (num i) N)+𝔞(pw N (num i)) := by
    have e := LeanProofs.IPRA.sum_succ (Γ := Γ) PowerSums.Bq N (num i : PTm n)
    change Γ ⊢[PRAAx] naturalSum (num i) (succ N) ≐ naturalSum (num i) N+inst2 PowerSums.Bq N (num i) at e
    rw [PowerSums.inst2_B] at e
    simpa [naturalSum,Q.mk_add,map_add] using natEq e
  apply ZT.derive
  simp only [prefixNumerator,pv,ZT.toZ_add,ZT.toZ_sumFin,ZT.toZ_mul,toZ_zint,ZT.toZ_ofNat,
    Q.mk_mul,map_mul,h]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

def foldLaw (a : Fin (d+1) → ℤ) (D : ℕ) (N M : PTm n) : Fm PTm n :=
  sum (body a D) N M ≐ normalize (prefixNumerator a N M) (rowDen d D M)

ipra_subst foldLaw

private theorem fold_zero (a : Fin (d+1) → ℤ) (D : ℕ) (hD : 0 < D) (M : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx] foldLaw a D zero M := by
  have hE := denominator_positive d D hD M hM
  refine ((RationalFiniteSum.sum_zero (body a D) M).eqTrans
    RationalReciprocalPowerTail.zero_fraction.eqSymm).eqTrans ?_
  apply canonical_equal _ _ _ _ _ _
    (normalize_well_formed _ _ (le_refl one)) (normalize_well_formed _ _ hE)
    (fraction_represents _ _ (le_refl one)) (normalize_preserves_value _ _ hE) (le_refl one) hE
  apply ZT.derive
  simp [ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_eq (prefix_zero (Γ := Γ) a M)]

private theorem fold_succ (a : Fin (d+1) → ℤ) (D : ℕ) (hD : 0 < D) (N M : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (ih : Γ ⊢[PRAAx] foldLaw a D N M) :
    Γ ⊢[PRAAx] foldLaw a D (succ N) M := by
  let E := rowDen d D M
  let x := prefixNumerator a N M
  let y := pv a N M
  let z := prefixNumerator a (succ N) M
  have hE := denominator_positive d D hD M hM
  have hEE := positive_product _ _ hE hE
  have vX := normalize_preserves_value (Γ := Γ) x E hE
  have vY := normalize_preserves_value (Γ := Γ) y E hE
  have vZ := normalize_preserves_value (Γ := Γ) z E hE
  have h := (RationalFiniteSum.sum_succ (body a D) N M).eqTrans
    (add_congr ih (show Γ ⊢[PRAAx] term (body a D) N M ≐ normalize y E from by rw [body_at]; exact .eqRefl _))
  refine h.eqTrans ?_
  apply canonical_equal _ _ _ _ _ _
    (RationalArithmetic.add_guard _ _) (normalize_well_formed _ _ hE)
    (RationalRepresentations.represents_add _ _ _ _ _ _ vX vY) vZ hEE hE
  apply ZT.derive
  have hz : ZT.toZ Γ z = ZT.toZ Γ x + ZT.toZ Γ y := by
    simpa only [z,x,y,ZT.toZ_add] using ZT.toZ_eq (prefix_succ (Γ := Γ) a N M)
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat,Q.mk_mul,map_mul,hz]
  ring

theorem fold_eq (a : Fin (d+1) → ℤ) (D : ℕ) (hD : 0 < D) (N M : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx] foldLaw a D N M := by
  have all : Γ ⊢[PRAAx] .all (foldLaw a D (var 0) (Syn.shift M)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_foldLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using fold_zero a D hD M hM
    · simp only [subst_foldLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact fold_succ a D hD _ (Syn.shift M) (by
        apply Prf.wk
        simpa [Fm.shift,Syn.shift,one] using hM.shift) Prf.hyp0
  simpa only [subst_foldLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem actual_literal_polynomial_grid_fold_closed (a : Fin (d+1) → ℤ) (D : ℕ) (hD : 0 < D) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (le one (var 1) ⟶ foldLaw a D (var 0) (var 1)) :=
  closeUniv 2 (.impI (fold_eq a D hD _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.RationalPolynomialGridSum
