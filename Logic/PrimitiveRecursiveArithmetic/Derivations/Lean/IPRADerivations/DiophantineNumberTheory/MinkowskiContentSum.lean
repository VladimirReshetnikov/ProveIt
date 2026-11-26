import IPRADerivations.Analysis.RationalArithmetic.RationalNormalForm
import IPRADerivations.Core.ProdLemmas
import IPRADerivations.Core.Header

/-!
# Exact clearing of the actual rational box-content sum

The numerator program uses `E' = E*q_j + p_j*D` and the denominator is the
actual product of the independent positive `q_j`.  The integer counts use
the actual finite sum.  Pointwise identities `q_j*c_j = K*p_j` imply the
derived global identity `D*sum(c_j) = K*E`.  Thus the original rational
threshold `E>D` gives the integer pigeonhole threshold `sum(c_j)>K`.

The fixed summand bodies are schema parameters.  List length, common
scale and persistent numerical input are internal.  No global count or
threshold identity is an input.  The rational-box application must derive
the pointwise identities for its actual product widths.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiContentSum

open_ipra
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (positive_form)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (one_le_of_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def denominator (Q : PTm 2) (N x : PTm n) : PTm n := ap2 (prodF Q) N x
def count (C : PTm 2) (N x : PTm n) : PTm n := ap2 (sumF C) N x
def numeratorStep (P Q : PTm 2) : PTm 3 :=
  var 1*Syn.subst ![var 0,var 2] Q + Syn.subst ![var 0,var 2] P*denominator Q (var 0) (var 2)
def numeratorF (P Q : PTm 2) : PR 2 := rec2 zero (numeratorStep P Q)
def numerator (P Q : PTm 2) (N x : PTm n) : PTm n := ap2 (numeratorF P Q) N x

@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (Q : PTm 2) (N x : PTm n) :
    Syn.subst σ (denominator Q N x) = denominator Q (Syn.subst σ N) (Syn.subst σ x) := subst_ap2 _ _ _ _
@[simp] theorem subst_count {m : ℕ} (σ : Fin n → PTm m) (C : PTm 2) (N x : PTm n) :
    Syn.subst σ (count C N x) = count C (Syn.subst σ N) (Syn.subst σ x) := subst_ap2 _ _ _ _
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (P Q : PTm 2) (N x : PTm n) :
    Syn.subst σ (numerator P Q N x) = numerator P Q (Syn.subst σ N) (Syn.subst σ x) := subst_ap2 _ _ _ _

theorem numerator_zero (P Q : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] numerator P Q zero x ≐ zero := by
  simpa only [numerator,numeratorF,ConciseIPRA.PTm.subst_zero] using
    rec2_zero (Γ := Γ) zero (numeratorStep P Q) x

theorem numerator_succ (P Q : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] numerator P Q (succ N) x ≐
      numerator P Q N x*inst2 Q N x+inst2 P N x*denominator Q N x := by
  have h := rec2_succ (Γ := Γ) zero (numeratorStep P Q) N x
  have e : Syn.subst ![N,numerator P Q N x,x] (numeratorStep P Q) =
      numerator P Q N x*inst2 Q N x+inst2 P N x*denominator Q N x := by
    have ρ : (fun i : Fin 2 => Syn.subst ![N,numerator P Q N x,x] (![var 0,var 2] i)) = ![N,x] := by
      funext i; fin_cases i <;> rfl
    simp only [numeratorStep,PTm.subst_add,PTm.subst_mul,Syn.subst_subst,
      subst_denominator,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons,ρ]
    rfl
  exact e ▸ h

def clearing (C P Q : PTm 2) (N K x : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶
    (inst2 Q (var 0) (Syn.shift x)*inst2 C (var 0) (Syn.shift x) ≐
      Syn.shift K*inst2 P (var 0) (Syn.shift x)))
def positiveDenominators (Q : PTm 2) (N x : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ le one (inst2 Q (var 0) (Syn.shift x)))

@[simp] theorem subst_clearing {m : ℕ} (σ : Fin n → PTm m) (C P Q : PTm 2) (N K x : PTm n) :
    (clearing C P Q N K x).subst σ = clearing C P Q (Syn.subst σ N) (Syn.subst σ K) (Syn.subst σ x) := by
  simp only [clearing,Fm.subst_all,Fm.subst_imp,Fm.subst_eq,subst_lt,PTm.subst_mul,
    subst_inst2,Syn.subst_var,Syn.up_zero,Syn.up_succ,Syn.subst_shift,Syn.shift_subst]

theorem clearing_at (C P Q : PTm 2) (N K x j : PTm n)
    (h : Γ ⊢[PRAAx] clearing C P Q N K x) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] inst2 Q j x*inst2 C j x ≐ K*inst2 P j x := by
  have r : Γ ⊢[PRAAx] lt j N ⟶ (inst2 Q j x*inst2 C j x ≐ K*inst2 P j x) := by
    simpa only [clearing,Fm.subst_imp,Fm.subst_eq,subst_lt,PTm.subst_mul,subst_inst2,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE j h
  exact .impE r hj

theorem sum_clearing (C P Q : PTm 2) (N K x : PTm n)
    (h : Γ ⊢[PRAAx] clearing C P Q N K x) :
    Γ ⊢[PRAAx] denominator Q N x*count C N x ≐ K*numerator P Q N x := by
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift N) ⟶
      (denominator Q (var 0) (Syn.shift x)*count C (var 0) (Syn.shift x) ≐
        Syn.shift K*numerator P Q (var 0) (Syn.shift x))) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [Fm.subst_imp,Fm.subst_eq,subst_le,PTm.subst_mul,subst_denominator,
        subst_count,subst_numerator,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      refine .impI ?_
      exact (congrMul (.eqRefl _) (sum_zero C x)).eqTrans ((mul_zero _).eqTrans
        ((mul_zero _).eqSymm.eqTrans (congrMul (.eqRefl _) (numerator_zero P Q x).eqSymm)))
    · simp only [Fm.subst_imp,Fm.subst_eq,subst_le,PTm.subst_mul,subst_denominator,
        subst_count,subst_numerator,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let IH : Fm PTm (n+1) := le (var 0) (Syn.shift N) ⟶
        (denominator Q (var 0) (Syn.shift x)*count C (var 0) (Syn.shift x) ≐
          Syn.shift K*numerator P Q (var 0) (Syn.shift x))
      let Δ : List (Fm PTm (n+1)) := le (succ (var 0)) (Syn.shift N) :: IH :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] denominator Q (var 0) (Syn.shift x)*count C (var 0) (Syn.shift x) ≐
          Syn.shift K*numerator P Q (var 0) (Syn.shift x) :=
        .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      have contract : Γ.map Fm.shift ⊢[PRAAx] clearing C P Q (Syn.shift N) (Syn.shift K) (Syn.shift x) := by
        simpa only [Fm.shift,subst_clearing,Syn.shift] using h.shift
      have pt := natEq (clearing_at C P Q _ _ _ (var 0) contract.wk.wk
        (Prf.hyp0 : Δ ⊢[PRAAx] _))
      have i := natEq ih
      have dp : Δ ⊢[PRAAx] denominator Q (succ (var 0)) (Syn.shift x) ≐
          denominator Q (var 0) (Syn.shift x)*inst2 Q (var 0) (Syn.shift x) := prod_succ Q _ _
      have cp : Δ ⊢[PRAAx] count C (succ (var 0)) (Syn.shift x) ≐
          count C (var 0) (Syn.shift x)+inst2 C (var 0) (Syn.shift x) := sum_succ C _ _
      have d := natEq dp
      have c := natEq cp
      have p := natEq (numerator_succ (Γ := Δ) P Q (var 0) (Syn.shift x))
      apply deriveNat (Γ := Δ)
      ipra_simps
      rw [d,c,p]
      linear_combination 𝔞(inst2 Q (var 0) (Syn.shift x))*i+
        𝔞(denominator Q (var 0) (Syn.shift x))*pt
  have r : Γ ⊢[PRAAx] le N N ⟶ (denominator Q N x*count C N x ≐ K*numerator P Q N x) := by
    simpa only [Fm.subst_imp,Fm.subst_eq,subst_le,PTm.subst_mul,subst_denominator,
      subst_count,subst_numerator,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE N all
  exact .impE r (le_refl _)

theorem denominator_positive (Q : PTm 2) (N x : PTm n)
    (h : Γ ⊢[PRAAx] positiveDenominators Q N x) : Γ ⊢[PRAAx] le one (denominator Q N x) := by
  apply one_le_of_pos
  apply prod_pos_bounded Q x N
  refine .allI (.impI ?_)
  have all := h.allOpen
  have pos := Prf.impE all.wk Prf.hyp0
  exact positive_form pos

/-- The strict rational threshold yields the actual integer count
threshold. Positivity of `K` is explicit, since it will be `m^n`. -/
theorem strict_count (C P Q : PTm 2) (N K x : PTm n)
    (h : Γ ⊢[PRAAx] clearing C P Q N K x)
    (hK : Γ ⊢[PRAAx] le one K)
    (hW : Γ ⊢[PRAAx] lt (denominator Q N x) (numerator P Q N x)) :
    Γ ⊢[PRAAx] lt K (count C N x) := by
  refine .orE (lt_or_le K (count C N x)) Prf.hyp0 ?_
  have id := sum_clearing (Γ := le (count C N x) K :: Γ) C P Q N K x h.wk
  have bound := le_mul_mono (le_refl (denominator Q N x)) (Prf.hyp0 : le (count C N x) K :: Γ ⊢[PRAAx] _)
  have reduced : le (count C N x) K :: Γ ⊢[PRAAx] le (K*numerator P Q N x) (K*denominator Q N x) :=
    le_congr id (mul_comm _ _) bound
  have opposite : le (count C N x) K :: Γ ⊢[PRAAx] le (numerator P Q N x) (denominator Q N x) :=
    mul_le_cancel (le_congr (congrMul (positive_form hK.wk) (.eqRefl _))
      (congrMul (positive_form hK.wk) (.eqRefl _)) reduced)
  exact lt_irrefl _ _ (le_trans hW.wk opposite)

theorem content_sum_closed (C P Q : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (clearing C P Q (var 0) (var 1) (var 2) ⟶
      (denominator Q (var 0) (var 2)*count C (var 0) (var 2) ≐
        var 1*numerator P Q (var 0) (var 2))) :=
  closeUniv 3 (.impI (sum_clearing C P Q _ _ _ Prf.hyp0))

theorem content_threshold_closed (C P Q : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (clearing C P Q (var 0) (var 1) (var 2) ⟶ positiveDenominators Q (var 0) (var 2) ⟶
      le one (var 1) ⟶ lt (denominator Q (var 0) (var 2)) (numerator P Q (var 0) (var 2)) ⟶
        (le one (denominator Q (var 0) (var 2)) ⋏ lt (var 1) (count C (var 0) (var 2)))) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (.andI
    (denominator_positive Q _ _ Prf.hyp1.wk)
    (strict_count C P Q _ _ _ Prf.hyp1.wk.wk Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiContentSum
