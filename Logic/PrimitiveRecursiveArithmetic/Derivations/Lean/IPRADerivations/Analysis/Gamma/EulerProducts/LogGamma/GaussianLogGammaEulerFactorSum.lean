import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerHead
import IPRADerivations.Analysis.Logarithm.RightHalfPlane.GaussianRightHalfPlaneLogarithmRescale
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteSumFamilySplit
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteSumFamilyCongruence
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteSumFamilyAdd

/-!
# Normalize the original finite Euler denominator logarithms

Separate the zeroth row. For each remaining numerical row k≥1,
extract log(k) by the exact positive scaling law. The two resulting
sums are the positive integer logarithms and the canonical logarithms
of 1+z/k, using the same encoded z and imaginary sign in every row.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerFactorSum

open_ipra
open GaussianLogGammaEulerHead (rowBody rowData row_at sumData)
open GaussianEuclideanDistanceName (pointCN subst_pointCN)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent subst_crossEquivalent cross_trans cross_symm cross_refl)
open GaussianNamedFiniteProductFamily (regularRows regular_at)
open GaussianNamedFiniteProductFamilyCongruence (equalRows)
open GaussianNamedFiniteSumFamilySplit (first_cross regular_tail)
open GaussianNamedFiniteSumFamilyCongruence (family_sum_cross)
open GaussianNamedFiniteSumFamilyAdd (mixedBody family_add_cross)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianPositiveRationalLogarithm (logF)
open GaussianRightHalfPlaneLogarithm (source)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => GaussianRightHalfPlaneLogarithm.nameF
local notation "P" => GaussianRightHalfPlaneLogarithm.data
local notation "L" => GaussianPositiveRationalLogarithm.data
local notation "S" => GaussianNamedFiniteSumFamily.nameF
local notation "sd" => GaussianNamedFiniteSumFamily.data

def integerBody : PTm 2 := L (succ (var 0)) one
def residualBody : PTm 2 :=
  P (fstT (var 1)+succ (var 0)*fstT (sndT (sndT (var 1))))
    (fstT (sndT (var 1))) (fstT (sndT (sndT (var 1)))*succ (var 0)) (sndT (sndT (sndT (var 1))))

def integerF : PR 2 := S logF integerBody
def residualF : PR 2 := S G residualBody
def tailF : PR 2 := addF integerF residualF

private theorem move_input (f : PR 2) {x y : PTm n} (e : Γ ⊢[PRAAx] x ≐ y)
    (h : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx] pointCN f y := by
  have h' : Γ ⊢[PRAAx] (pointCN f (var 0) : Fm PTm 1).subst ![x] := by
    simpa only [subst_pointCN,Syn.subst_var,Matrix.cons_val_zero] using h
  have proof := Prf.eqSubst (Γ := Γ) (Ax := PRAAx) (pointCN f (var 0) : Fm PTm 1) ![x] ![y]
    (fun i => by fin_cases i; exact e) h'
  simpa only [subst_pointCN,Syn.subst_var,Matrix.cons_val_zero] using proof

private theorem move_inputs (f g : PR 2) {x x' y y' : PTm n}
    (a : Γ ⊢[PRAAx] x ≐ x') (b : Γ ⊢[PRAAx] y ≐ y') (h : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent f g x' y' := by
  have h' : Γ ⊢[PRAAx] (crossEquivalent f g (var 0) (var 1) : Fm PTm 2).subst ![x,y] := by
    simpa only [subst_crossEquivalent,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using h
  have proof := Prf.eqSubst (Γ := Γ) (Ax := PRAAx) (crossEquivalent f g (var 0) (var 1) : Fm PTm 2)
    ![x,y] ![x',y'] (fun i => by fin_cases i; exact a; exact b) h'
  simpa only [subst_crossEquivalent,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using proof

theorem residual_at (i A B D neg : PTm n) :
    Γ ⊢[PRAAx] inst2 residualBody i (rowData A B D neg) ≐ P (A+succ i*D) B (D*succ i) neg := by
  let x := rowData A B D neg
  let k := succ i
  let e₁ := fst_pair (Γ := Γ) A (pairT B (pairT D neg))
  let e₂ := snd_pair (Γ := Γ) A (pairT B (pairT D neg))
  let e₃ := (congrSnd e₂).eqTrans (snd_pair B (pairT D neg))
  let eD := (congrFst e₃).eqTrans (fst_pair D neg)
  have h := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (P (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![fstT x+k*fstT (sndT (sndT x)),fstT (sndT x),fstT (sndT (sndT x))*k,sndT (sndT (sndT x))])
    (σ' := ![A+k*D,B,D*k,neg]) (fun j => by
      fin_cases j
      · exact congrAdd e₁ (congrMul (.eqRefl _) eD)
      · exact (congrFst e₂).eqTrans (fst_pair _ _)
      · exact congrMul eD (.eqRefl _)
      · exact (congrSnd e₃).eqTrans (snd_pair _ _))
  simpa [residualBody,inst2,x,k] using h

private theorem residual_source (i A D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] source (A+succ i*D) (D*succ i) neg :=
  .andI (GaussianLogGammaEulerHead.shifted_source (succ i) A D neg h).andE₁
    (positive_product D (succ i) h.andE₂ (zero_lt_succ i))

theorem integer_rows (N x : PTm n) : Γ ⊢[PRAAx] regularRows logF integerBody N x := by
  refine .allI (.impI ?_)
  simpa [regularRows,integerBody,inst2] using
    (GaussianPositiveRationalLogarithm.name_regular (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift)
      (succ (var 0)) one (.andI (zero_lt_succ _) (le_refl _)))

theorem residual_rows (A B D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] regularRows G residualBody N (rowData A B D neg) := by
  refine .allI (.impI ?_)
  let sh (a : PTm n) := Syn.shift a
  let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (sh A) (sh D) (sh neg) := by
    simpa [Fm.shift,Syn.shift,sh,Δ,source,GaussianRightHalfPlaneArgument.source] using h.shift.wk
  have r := GaussianRightHalfPlaneLogarithm.regular (sh A+succ (var 0)*sh D) (sh B) (sh D*succ (var 0))
    (sh neg) (residual_source (var 0) (sh A) (sh D) (sh neg) hs)
  simpa only [regularRows,Syn.shift,GaussianLogGammaEulerHead.subst_rowData,sh,Δ] using
    move_input G (residual_at (var 0) (sh A) (sh B) (sh D) (sh neg)).eqSymm r

theorem factor_rows (A B D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] equalRows G (addF logF G) (shiftBody rowBody) (mixedBody integerBody residualBody)
      N (rowData A B D neg) (rowData A B D neg) := by
  refine .allI (.impI ?_)
  let sh (a : PTm n) := Syn.shift a
  let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
  let x := rowData (sh A) (sh B) (sh D) (sh neg)
  let k : PTm (n+1) := succ (var 0)
  have hs : Δ ⊢[PRAAx] source (sh A) (sh D) (sh neg) := by
    simpa [Fm.shift,Syn.shift,sh,Δ,source,GaussianRightHalfPlaneArgument.source] using h.shift.wk
  have factor := GaussianRightHalfPlaneLogarithmRescale.split_shift (sh A) (sh B) (sh D) (sh neg)
    k hs (zero_lt_succ _)
  have left : Δ ⊢[PRAAx] inst2 (shiftBody rowBody) (var 0) x ≐ P (sh A+k*sh D) (sh B) (sh D) (sh neg) := by
    rw [inst2_shiftBody]
    exact row_at k (sh A) (sh B) (sh D) (sh neg)
  have readInteger : inst2 integerBody (var 0) x = L k one := by
    simp [integerBody,inst2,k,one]
  have right : Δ ⊢[PRAAx] inst2 (mixedBody integerBody residualBody) (var 0) x ≐
      addData (L k one) (P (sh A+k*sh D) (sh B) (sh D*k) (sh neg)) := by
    rw [GaussianNamedFiniteSumFamilyAdd.inst2_mixedBody,readInteger]
    let u := inst2 residualBody (var 0) x
    let v := P (sh A+k*sh D) (sh B) (sh D*k) (sh neg)
    have field : Δ ⊢[PRAAx] u ≐ v := residual_at (var 0) (sh A) (sh B) (sh D) (sh neg)
    have proof := Prf.eqCongr (Γ := Δ) (Ax := PRAAx) (addData (var 0) (var 1) : PTm 2)
      (σ := ![L k one,u]) (σ' := ![L k one,v]) (fun j => by fin_cases j; exact .eqRefl _; exact field)
    simpa only [GaussianNameArithmetic.subst_addData,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using proof
  simpa only [equalRows,Syn.shift,GaussianLogGammaEulerHead.subst_rowData,sh,Δ,x] using
    move_inputs G (addF logF G) left.eqSymm right.eqSymm factor

theorem denominator_split (A B D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] crossEquivalent GaussianLogGammaEulerHead.sumF (addF G tailF) (sumData A B D neg N)
      (addData (P A B D neg) (addData (sd N (rowData A B D neg)) (sd N (rowData A B D neg)))) := by
  let x := rowData A B D neg
  let l := inst2 rowBody zero x
  let r := P A B D neg
  let t := S G (shiftBody rowBody)
  let s := sd N x
  let y := addData s s
  have rows := GaussianLogGammaEulerHead.sum_rows A B D neg N h
  have first := first_cross G rowBody N x rows
  have origin := GaussianRightHalfPlaneLogarithm.regular A B D neg h
  have atZero : Γ ⊢[PRAAx] A+zero*D ≐ A := by ipra_ring
  have numeratorEq : Γ ⊢[PRAAx] P (A+zero*D) B D neg ≐ r := by
    have e := Prf.eqCongr1 (P (var 0) (Syn.shift B) (Syn.shift D) (Syn.shift neg)) atZero
    simpa only [GaussianRightHalfPlaneLogarithm.subst_data,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,r] using e
  have bind : Γ ⊢[PRAAx] l ≐ r := (row_at zero A B D neg).eqTrans numeratorEq
  let m := S (addF logF G) (mixedBody integerBody residualBody)
  have tail : Γ ⊢[PRAAx] crossEquivalent t m s s :=
    family_sum_cross G (addF logF G) (shiftBody rowBody) (mixedBody integerBody residualBody)
      N x x (factor_rows A B D neg N h)
  have intRows := integer_rows (Γ := Γ) N x
  have remRows := residual_rows A B D neg N h
  have add := family_add_cross logF G integerBody residualBody N x intRows remRows
  have tailEq := cross_trans t m tailF s s y tail add
  have ht := GaussianNamedFiniteSumFamily.regular _ _ _ _ (regular_tail G rowBody N x rows)
  have hy := add_fast integerF residualF s s
    (GaussianNamedFiniteSumFamily.regular _ _ _ _ intRows) (GaussianNamedFiniteSumFamily.regular _ _ _ _ remRows)
  have main := add_cross G G t tailF l r s y
    (move_input G bind.eqSymm origin) origin ht hy
    (move_inputs G G bind.eqSymm (.eqRefl _) (cross_refl _ _ origin)) tailEq
  exact cross_trans GaussianLogGammaEulerHead.sumF (addF G t) (addF G tailF)
    (sumData A B D neg N) (addData l s) (addData r y) first main

theorem actual_finite_Euler_logarithm_denominator_split_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source (var 0) (var 2) (var 3) ⟶
        crossEquivalent GaussianLogGammaEulerHead.sumF (addF G tailF) (sumData (var 0) (var 1) (var 2) (var 3) (var 4))
          (addData (P (var 0) (var 1) (var 2) (var 3))
            (addData (sd (var 4) (rowData (var 0) (var 1) (var 2) (var 3)))
              (sd (var 4) (rowData (var 0) (var 1) (var 2) (var 3)))))) :=
  closeUniv 5 (.impI (denominator_split _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerFactorSum
