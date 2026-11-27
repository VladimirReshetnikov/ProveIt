import IPRADerivations.Analysis.Stirling.Binet.WeightedIntegrals.Exponential.GaussianBinetWeightedExponentialGrid
import IPRADerivations.Analysis.Stirling.Binet.ExponentialIntegrals.GaussianBinetExponentialIntegralGrid
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.Reindexing.GaussianRationalFubini

/-!
# Finite Fubini for the Binet recurrence integrand

The literal entries are the product of the original complex Laplace
sample in t and the original weighted real decay sample in u.
The first sum in u is the existing weighted exponential grid; the
finite rectangle can be returned in either summation order.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBinetExponentialRectangle

open_ipra
open GaussianCompactRiemannName
  (sampleData sampleBody field0 field1 field2 field3 field4 field5
    field0_at field1_at field2_at field3_at field4_at field5_at)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalFiniteSum (sum)
open GaussianRationalFubini (row rowBody rowFirst rowSumBody columnFirst row_entry row_sum_at)
open GaussianRationalHorner (qmul)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "L" => GaussianBinetExponentialIntegralGrid.row
local notation "W" => GaussianBinetWeightedExponentialGrid.rowValue
local notation "Q" => GaussianBinetWeightedExponentialGrid.value
local notation "F" => GaussianBinetWeightedExponentialGrid.evaluatorF

private theorem cons_val_five {α : Type} {m : ℕ} (a : α) (u : Fin (m+5) → α) :
    Matrix.vecCons a u 5 = Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u)))) := rfl

private theorem cons_val_six {α : Type} {m : ℕ} (a : α) (u : Fin (m+6) → α) :
    Matrix.vecCons a u 6 = Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u))))) := rfl

private theorem cons_val_seven {α : Type} {m : ℕ} (a : α) (u : Fin (m+7) → α) :
    Matrix.vecCons a u 7 = Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u)))))) := rfl

def data (p q S T N M : PTm n) : PTm n := sampleData p q S T N M
def entry (i j p q S T N M : PTm n) : PTm n := qmul (L p q S (T*i) N) (W p (T*i) N j M)
def matrix : PTm 3 := entry (var 0) (var 1) (field0 (var 2)) (field1 (var 2)) (field2 (var 2))
  (field3 (var 2)) (field4 (var 2)) (field5 (var 2))

ipra_subst data

ipra_subst entry

theorem entry_at (i j p q S T N M : PTm n) :
    Γ ⊢[PRAAx] inst3 matrix i j (data p q S T N M) ≐ entry i j p q S T N M := by
  let d := data p q S T N M
  simpa only [matrix,inst3,subst_entry,GaussianCompactRiemannName.subst_field0,GaussianCompactRiemannName.subst_field1,
    GaussianCompactRiemannName.subst_field2,GaussianCompactRiemannName.subst_field3,GaussianCompactRiemannName.subst_field4,
    GaussianCompactRiemannName.subst_field5,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,cons_val_five,cons_val_six,cons_val_seven,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons,d] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
      (entry (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) : PTm 8)
      (σ := ![i,j,field0 d,field1 d,field2 d,field3 d,field4 d,field5 d]) (σ' := ![i,j,p,q,S,T,N,M])
      (fun k => by
        fin_cases k
        exact .eqRefl _
        exact .eqRefl _
        exact field0_at _ _ _ _ _ _
        exact field1_at _ _ _ _ _ _
        exact field2_at _ _ _ _ _ _
        exact field3_at _ _ _ _ _ _
        exact field4_at _ _ _ _ _ _
        exact field5_at _ _ _ _ _ _)

theorem weighted_row (i p q S T N M : PTm n) :
    Γ ⊢[PRAAx] qmul (fraction one M) (row matrix i M (data p q S T N M)) ≐
      qmul (L p q S (T*i) N) (Q p M (T*i) N) := by
  let c := L p q S (T*i) N
  let d := data p q S T N M
  let x := sampleData p M one one one (pairT (T*i) N)
  let f := sampleBody F
  let g := GaussianRationalFiniteSum.multiplyBody f
  have rows : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual (rowBody matrix) g M (pairT i d) (pairT c x) := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s M) :: Γ.map Fm.shift
    have l := (row_entry (Γ := Δ) matrix (s i) (var 0) (data (s p) (s q) (s S) (s T) (s N) (s M))).eqTrans
      (entry_at (s i) (var 0) (s p) (s q) (s S) (s T) (s N) (s M))
    have r := (GaussianRationalFiniteSum.multiply_body_at (Γ := Δ) f (L (s p) (s q) (s S) (s T*s i) (s N)) (var 0)
      (sampleData (s p) (s M) one one one (pairT (s T*s i) (s N)))).eqTrans
      (qmul_congr (.eqRefl _) (GaussianBinetWeightedExponentialGrid.cell_at (var 0) (s p) (s M) (s T*s i) (s N)))
    simpa only [GaussianRationalFiniteSum.termsEqual,Syn.shift,s,Δ,c,d,x,g,f,entry,
      GaussianCompactRiemannName.subst_sampleData,subst_data,subst_pairT,PTm.subst_mul,
      GaussianBinetExponentialIntegralGrid.subst_row,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      l.eqTrans r.eqSymm
  have read : Γ ⊢[PRAAx] row matrix i M d ≐ qmul c (sum f M x) :=
    (GaussianRationalFiniteSum.sum_congr_bounded (rowBody matrix) g M _ _ rows).eqTrans
      (GaussianRationalFiniteSum.sum_multiply f c M x)
  have weight : Γ ⊢[PRAAx] fraction one M ≐ GaussianRationalRiemannRefinement.weight one one M :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (one_mul M).eqSymm
  exact (qmul_congr (.eqRefl _) read).eqTrans
    ((GaussianRationalPowerAlgebra.commute_nested (fraction one M) c _).eqTrans
       (qmul_congr (.eqRefl _) (qmul_congr weight (.eqRefl _))))

def outerEntry (i p q S T N M : PTm n) : PTm n := qmul (L p q S (T*i) N) (Q p M (T*i) N)
def outerBody : PTm 2 := outerEntry (var 0) (field0 (var 1)) (field1 (var 1)) (field2 (var 1))
  (field3 (var 1)) (field4 (var 1)) (field5 (var 1))

ipra_subst outerEntry

theorem outer_at (i p q S T N M : PTm n) :
    Γ ⊢[PRAAx] inst2 outerBody i (data p q S T N M) ≐ outerEntry i p q S T N M := by
  let d := data p q S T N M
  simpa only [outerBody,inst2,subst_outerEntry,GaussianCompactRiemannName.subst_field0,
    GaussianCompactRiemannName.subst_field1,GaussianCompactRiemannName.subst_field2,GaussianCompactRiemannName.subst_field3,
    GaussianCompactRiemannName.subst_field4,GaussianCompactRiemannName.subst_field5,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,cons_val_five,cons_val_six,Matrix.cons_val_succ,
    Matrix.head_cons,Matrix.tail_cons,d] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
      (outerEntry (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7)
      (σ := ![i,field0 d,field1 d,field2 d,field3 d,field4 d,field5 d]) (σ' := ![i,p,q,S,T,N,M])
      (fun k => by
        fin_cases k
        exact .eqRefl _
        exact field0_at _ _ _ _ _ _
        exact field1_at _ _ _ _ _ _
        exact field2_at _ _ _ _ _ _
        exact field3_at _ _ _ _ _ _
        exact field4_at _ _ _ _ _ _
        exact field5_at _ _ _ _ _ _)

theorem swap_weighted_grid (p q S T N M : PTm n) :
    Γ ⊢[PRAAx] qmul (fraction T N) (sum outerBody N (data p q S T N M)) ≐
      qmul (fraction T N) (qmul (fraction one M) (columnFirst matrix N M (data p q S T N M))) := by
  let d := data p q S T N M
  let c := fraction one M
  let g := rowSumBody matrix
  let x := pairT M d
  let h := GaussianRationalFiniteSum.multiplyBody g
  have rows : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual outerBody h N d (pairT c x) := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s N) :: Γ.map Fm.shift
    have l := outer_at (Γ := Δ) (var 0) (s p) (s q) (s S) (s T) (s N) (s M)
    have r := (GaussianRationalFiniteSum.multiply_body_at (Γ := Δ) g (fraction one (s M)) (var 0)
      (pairT (s M) (data (s p) (s q) (s S) (s T) (s N) (s M)))).eqTrans
      (qmul_congr (.eqRefl _) (row_sum_at matrix (var 0) (s M) _))
    simpa only [GaussianRationalFiniteSum.termsEqual,Syn.shift,s,Δ,d,c,x,h,g,outerEntry,subst_data,
      subst_pairT,GaussianPositiveRationalLogarithm.subst_fraction,one,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] using
      l.eqTrans ((weighted_row (var 0) (s p) (s q) (s S) (s T) (s N) (s M)).eqSymm.eqTrans r.eqSymm)
  have swap : Γ ⊢[PRAAx] rowFirst matrix N M d ≐ columnFirst matrix N M d :=
    GaussianRationalFubini.fubini matrix N M d
  exact qmul_congr (.eqRefl _)
    ((GaussianRationalFiniteSum.sum_congr_bounded outerBody h N d (pairT c x) rows).eqTrans
      ((GaussianRationalFiniteSum.sum_multiply g c N x).eqTrans (qmul_congr (.eqRefl _) swap)))

end LeanProofs.IPRA.Analysis.GaussianBinetExponentialRectangle
