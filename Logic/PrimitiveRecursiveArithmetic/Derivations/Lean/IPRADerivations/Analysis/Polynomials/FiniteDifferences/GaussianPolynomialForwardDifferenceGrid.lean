import IPRADerivations.Analysis.Polynomials.FiniteDifferences.GaussianPolynomialForwardDifferenceIteration
import IPRADerivations.Foundations.SequenceEquality

/-!
# Actual equally spaced Gaussian forward differences at encoded order

The data program takes adjacent differences of stored observations
and shortens the row at each step. Its entire row agrees with evaluations
of the corresponding iterated polynomial difference. The final entry is
the scaled leading coefficient, with encoded Gaussian step and order.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialForwardDifferenceGrid

open_ipra
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.Foundations.SequenceEquality (agree sequence_equal)
open LeanProofs.IPRA.Analysis.Products (fact)
open GaussianPolynomialForwardDifferenceIteration (stage stage_length)
open GaussianRationalHorner (qadd qmul evaluate)
open GaussianRationalMetric (qsub)
open GaussianRationalNaturalScale (natScale natScale_congr)
open GaussianRationalReciprocal (power)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr)
open GaussianRationalTranslation (evaluate_congr)
open GaussianRationalTranslationStages (remaining remaining_step)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def point (x h i : PTm n) : PTm n := qadd x (natScale i h)
def sampleData (C x h : PTm n) : PTm n := pairT C (pairT x h)
def sampleBody : PTm 2 :=
  evaluate (fstT (var 1)) (point (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0))
def samples (C L x h : PTm n) : PTm n := sequence sampleBody L (sampleData C x h)

def differenceBody : PTm 2 := qsub (entry (var 1) (succ (var 0))) (entry (var 1) (var 0))
def adjacent (V L : PTm n) : PTm n := sequence differenceBody L V

def gridStep : PTm 4 := adjacent (var 1) (remaining (var 3) (var 0))
def gridF : PR 3 := recDef (var 0 : PTm 2) gridStep
def grid (V N j : PTm n) : PTm n := ap3 gridF j V N
def value (V N : PTm n) : PTm n := entry (grid V N N) zero

@[simp] theorem subst_point {l : ℕ} (σ : Fin n → PTm l) (x h i : PTm n) :
    Syn.subst σ (point x h i) = point (Syn.subst σ x) (Syn.subst σ h) (Syn.subst σ i) := by simp [point]

@[simp] theorem subst_sampleData {l : ℕ} (σ : Fin n → PTm l) (C x h : PTm n) :
    Syn.subst σ (sampleData C x h) = sampleData (Syn.subst σ C) (Syn.subst σ x) (Syn.subst σ h) := by simp [sampleData]

@[simp] theorem subst_samples {l : ℕ} (σ : Fin n → PTm l) (C L x h : PTm n) :
    Syn.subst σ (samples C L x h) = samples (Syn.subst σ C) (Syn.subst σ L) (Syn.subst σ x) (Syn.subst σ h) := by
  simp [samples]

@[simp] theorem subst_adjacent {l : ℕ} (σ : Fin n → PTm l) (V L : PTm n) :
    Syn.subst σ (adjacent V L) = adjacent (Syn.subst σ V) (Syn.subst σ L) := by simp [adjacent]

@[simp] theorem subst_grid {l : ℕ} (σ : Fin n → PTm l) (V N j : PTm n) :
    Syn.subst σ (grid V N j) = grid (Syn.subst σ V) (Syn.subst σ N) (Syn.subst σ j) := by simp [grid]

theorem point_succ (x h i : PTm n) : Γ ⊢[PRAAx] point x h (succ i) ≐ qadd h (point x h i) := by
  have e : Γ ⊢[PRAAx] natScale (succ i) h ≐ qadd (natScale i h) h :=
    (natScale_congr (by ipra_ring) (.eqRefl _)).eqTrans
      ((GaussianRationalNaturalScale.natScale_add i one h).eqTrans
        ((qadd_congr (.eqRefl _) (GaussianRationalNaturalScale.natScale_one h)).eqTrans
          (GaussianRationalSyntheticCoefficientValues.qadd_recode_right _ _)))
  exact (qadd_congr (.eqRefl _) e).eqTrans
    ((GaussianRationalSumAlgebra.qadd_associative _ _ _).eqSymm.eqTrans (GaussianReciprocalHorner.qadd_commutative _ _))

theorem sample_body_at (C x h i : PTm n) :
    Γ ⊢[PRAAx] inst2 sampleBody i (sampleData C x h) ≐ evaluate C (point x h i) := by
  have tail := snd_pair (Γ := Γ) C (pairT x h)
  ipra_congr (evaluate (var 0) (point (var 1) (var 2) (var 3)) : PTm 4) with
    [fst_pair C _, (congrFst tail).eqTrans (fst_pair x h), (congrSnd tail).eqTrans (snd_pair x h), .eqRefl i]
    using [sampleBody,sampleData,inst2]

theorem sample_lookup (C L x h i : PTm n) (hi : Γ ⊢[PRAAx] lt i L) :
    Γ ⊢[PRAAx] entry (samples C L x h) i ≐ evaluate C (point x h i) :=
  (sequence_decode sampleBody hi).eqTrans (sample_body_at C x h i)

theorem adjacent_lookup (V L i : PTm n) (hi : Γ ⊢[PRAAx] lt i L) :
    Γ ⊢[PRAAx] entry (adjacent V L) i ≐ qsub (entry V (succ i)) (entry V i) := by
  simpa [inst2,adjacent,differenceBody] using sequence_decode (Γ := Γ) differenceBody (x := V) hi

theorem grid_zero (V N : PTm n) : Γ ⊢[PRAAx] grid V N zero ≐ V := by
  have raw := rec_zero (Γ := Γ) (var 0 : PTm 2) gridStep ![V,N]
  have e : (Fin.cases zero ![V,N] : Fin 3 → PTm n) = ![zero,V,N] := by funext i; fin_cases i <;> rfl
  rw [e] at raw
  simpa only [grid,ap3,gridF,Syn.subst_var,Matrix.cons_val_zero] using raw

theorem grid_succ (V N j : PTm n) :
    Γ ⊢[PRAAx] grid V N (succ j) ≐ adjacent (grid V N j) (remaining N j) := by
  have raw := rec_succ (Γ := Γ) (var 0 : PTm 2) gridStep j ![V,N]
  have a : (Fin.cases (succ j) ![V,N] : Fin 3 → PTm n) = ![succ j,V,N] := by funext i; fin_cases i <;> rfl
  have b : (Fin.cases j (Fin.cases (PTm.app gridF (Fin.cases j ![V,N])) ![V,N]) : Fin 4 → PTm n) =
      ![j,grid V N j,V,N] := by funext i; fin_cases i <;> rfl
  unfold gridF at b
  rw [a,b] at raw
  simpa only [grid,ap3,gridF,gridStep,subst_adjacent,GaussianRationalTranslationStages.subst_remaining,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons] using raw

private theorem samples_congr {C D L M x h : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D) (hL : Γ ⊢[PRAAx] L ≐ M) :
    Γ ⊢[PRAAx] samples C L x h ≐ samples D M x h := by
  ipra_congr (samples (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hC, hL, .eqRefl x, .eqRefl h]

theorem adjacent_samples (C N h x : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) :
    Γ ⊢[PRAAx] adjacent (samples C (succ N) x h) N ≐ samples (GaussianPolynomialForwardDifference.difference C N h) N x h := by
  refine sequence_equal differenceBody sampleBody N _ _ (.allI (.impI ?_))
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  let C' := Syn.shift C
  let N' := Syn.shift N
  let x' := Syn.shift x
  let h' := Syn.shift h
  let i : PTm (n+1) := var 0
  let V := samples C' (succ N') x' h'
  let D := GaussianPolynomialForwardDifference.difference C' N' h'
  have shape : Δ ⊢[PRAAx] length C' ≐ succ N' := by simpa [Δ,C',N',Fm.shift,Syn.shift] using hC.shift.wk
  have hi : Δ ⊢[PRAAx] lt i N' := Prf.hyp0
  have next : Δ ⊢[PRAAx] lt (succ i) (succ N') := (succ_monus_succ _ _).eqTrans hi
  have atNow := sample_lookup C' (succ N') x' h' i (lt_of_lt_of_le hi (le_succ_self _))
  have atNext := (sample_lookup C' (succ N') x' h' (succ i) next).eqTrans
    (evaluate_congr (.eqRefl _) (point_succ x' h' i))
  have eq : Δ ⊢[PRAAx] qsub (entry V (succ i)) (entry V i) ≐ inst2 sampleBody i (sampleData D x' h') :=
    (qsub_congr atNext atNow).eqTrans
      ((GaussianPolynomialForwardDifference.evaluation C' N' h' (point x' h' i) shape).eqSymm.eqTrans
        (sample_body_at D x' h' i).eqSymm)
  simpa [agree,Δ,C',N',x',h',i,V,D,Syn.shift,differenceBody,inst2] using eq

private def sampleLaw (C N x h j : PTm n) : Fm PTm n := le j N ⟶
  grid (samples C (succ N) x h) N j ≐ samples (stage C N h j) (succ (remaining N j)) x h

@[simp] private theorem subst_sampleLaw {l : ℕ} (σ : Fin n → PTm l) (C N x h j : PTm n) :
    (sampleLaw C N x h j).subst σ = sampleLaw (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ h)
      (Syn.subst σ j) := by simp [sampleLaw]

theorem stage_readback (C N x h j : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] grid (samples C (succ N) x h) N j ≐ samples (stage C N h j) (succ (remaining N j)) x h := by
  have all : Γ ⊢[PRAAx] .all (sampleLaw (Syn.shift C) (Syn.shift N) (Syn.shift x) (Syn.shift h) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_sampleLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI ((grid_zero (samples C (succ N) x h) N).eqTrans
        (samples_congr (GaussianPolynomialForwardDifferenceIteration.stage_zero C N h).eqSymm
          (congrSucc (monus_zero N).eqSymm))).wk
    · simp only [subst_sampleLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let C' := Syn.shift C
      let N' := Syn.shift N
      let x' := Syn.shift x
      let h' := Syn.shift h
      let j' : PTm (n+1) := var 0
      let I := sampleLaw C' N' x' h' j'
      let Δ := le (succ j') N' :: I :: Γ.map Fm.shift
      let M := remaining N' j'
      let P := stage C' N' h' j'
      have shape : Δ ⊢[PRAAx] length C' ≐ succ N' := by
        simpa [Δ,C',N',Fm.shift,Syn.shift] using hC.shift.wk.wk
      have next : Δ ⊢[PRAAx] lt j' N' := Prf.hyp0
      have old := le_trans (le_succ_self _) next
      have ih := Prf.impE (Prf.hyp1 : Δ ⊢[PRAAx] I) old
      have lift : Δ ⊢[PRAAx] adjacent (grid (samples C' (succ N') x' h') N' j') M ≐ adjacent (samples P (succ M) x' h') M := by
        change Δ ⊢[PRAAx] adjacent (grid (samples C' (succ N') x' h') N' j') M ≐
          adjacent (samples (stage C' N' h' j') (succ (remaining N' j')) x' h') M
        ipra_congr (adjacent (var 0) (var 1) : PTm 2) with [ih, .eqRefl M]
      have adjacent := adjacent_samples P M h' x' (stage_length C' N' h' j' shape old)
      have new := samples_congr (GaussianPolynomialForwardDifferenceIteration.stage_succ C' N' h' j').eqSymm
        (remaining_step N' j' next) (x := x') (h := h')
      exact (grid_succ _ _ _).eqTrans (lift.eqTrans (adjacent.eqTrans new))
  have rule : Γ ⊢[PRAAx] sampleLaw C N x h j := by
    simpa only [subst_sampleLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE rule hj

theorem leading_coefficient (C N x h : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) :
    Γ ⊢[PRAAx] value (samples C (succ N) x h) N ≐ natScale (fact N) (qmul (entry C zero) (power h N)) := by
  have decoded := sample_lookup (Γ := Γ) (stage C N h N) (succ (remaining N N)) x h zero (zero_lt_succ _)
  exact (entry_congr (stage_readback C N x h N hC (le_refl _)) (.eqRefl _)).eqTrans
    (decoded.eqTrans (GaussianPolynomialForwardDifferenceIteration.terminal_evaluation C N h (point x h zero) hC))

theorem actual_Gaussian_grid_forward_difference_leading_coefficient_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶
      value (samples (var 0) (succ (var 1)) (var 2) (var 3)) (var 1) ≐
        natScale (fact (var 1)) (qmul (entry (var 0) zero) (power (var 3) (var 1)))) :=
  closeUniv 4 (.impI (leading_coefficient _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianPolynomialForwardDifferenceGrid
