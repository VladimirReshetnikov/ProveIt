import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalHigherMercatorSum
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalHigherTail
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalFubini

/-!
# Transpose the original finite Barnes row and Taylor degree sums

At row i the cutoff index is succ (N+i). Transposing the rectangle
collects each original coefficient window before multiplying by the
corresponding power of the common increment.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHigherMercatorTranspose

open_ipra
open GaussianBarnesCanonicalHigherRows (coefficient degree)
open GaussianBarnesCanonicalHigherMercatorSum (data)
open GaussianRationalFiniteSum (sum multiplyBody multiply_body_at sum_multiply)
open GaussianRationalFubini (row column rowBody columnBody columnSumBody column_entry row_entry column_sum_at
  rowFirst columnFirst)
open GaussianRationalHorner (qmul ofGaussian)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (power)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "MBody" => GaussianBarnesCanonicalHigherMercatorSum.body
local notation "MValue" => GaussianBarnesCanonicalHigherMercatorSum.value
local notation "TBody" => GaussianBarnesCanonicalHigherTail.body
local notation "TData" => GaussianBarnesCanonicalHigherTail.data
local notation "TValue" => GaussianBarnesCanonicalHigherTail.value

def matrix : PTm 3 :=
  qmul (coefficient (fstT (fstT (var 2))) (fstT (sndT (var 2))) (succ (sndT (sndT (var 2))+var 0)) (var 1))
    (power (ofGaussian (sndT (fstT (var 2))) (fstT (sndT (var 2)))) (degree (var 1)))

def degreeValue (z h B N r j : PTm n) : PTm n := qmul (TValue z B N j r) (power (ofGaussian h B) (degree j))

def degreeBody : PTm 2 :=
  let d := sndT (var 1)
  degreeValue (fstT (fstT d)) (sndT (fstT d)) (fstT (sndT d)) (sndT (sndT d)) (fstT (var 1)) (var 0)

def polynomial (z h B N r M : PTm n) : PTm n := sum degreeBody M (pairT r (data z h B N))

@[simp] theorem subst_degreeValue {m : ℕ} (σ : Fin n → PTm m) (z h B N r j : PTm n) :
    Syn.subst σ (degreeValue z h B N r j) =
      degreeValue (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) (Syn.subst σ j) :=
  by simp [degreeValue]

@[simp] theorem subst_polynomial {m : ℕ} (σ : Fin n → PTm m) (z h B N r M : PTm n) :
    Syn.subst σ (polynomial z h B N r M) =
      polynomial (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) (Syn.subst σ M) :=
  by simp [polynomial]

theorem matrix_at (z h B N i j : PTm n) : Γ ⊢[PRAAx]
    inst3 matrix i j (data z h B N) ≐ qmul (coefficient z B (succ (N+i)) j) (power (ofGaussian h B) (degree j)) := by
  let x := data z h B N
  have u : Γ ⊢[PRAAx] fstT x ≐ pairT z h := fst_pair _ _
  have v : Γ ⊢[PRAAx] sndT x ≐ pairT B N := snd_pair _ _
  have fields := Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (qmul (coefficient (var 0) (var 2) (var 3) (var 4)) (power (ofGaussian (var 1) (var 2)) (degree (var 4))) : PTm 5)
    (σ := ![fstT (fstT x),sndT (fstT x),fstT (sndT x),succ (sndT (sndT x)+i),j])
    (σ' := ![z,h,B,succ (N+i),j]) (fun p => by
      fin_cases p
      · exact (congrFst u).eqTrans (fst_pair _ _)
      · exact (congrSnd u).eqTrans (snd_pair _ _)
      · exact (congrFst v).eqTrans (fst_pair _ _)
      · exact congrSucc (congrAdd ((congrSnd v).eqTrans (snd_pair _ _)) (.eqRefl _))
      · exact .eqRefl j)
  simpa [matrix,inst3,x] using fields

theorem degree_at (z h B N r j : PTm n) : Γ ⊢[PRAAx]
    inst2 degreeBody j (pairT r (data z h B N)) ≐ degreeValue z h B N r j := by
  let x := data z h B N
  let y := pairT r x
  let a := sndT y
  have raw : Γ ⊢[PRAAx] a ≐ x := snd_pair _ _
  have u : Γ ⊢[PRAAx] fstT a ≐ pairT z h := (congrFst raw).eqTrans (fst_pair _ _)
  have v : Γ ⊢[PRAAx] sndT a ≐ pairT B N := (congrSnd raw).eqTrans (snd_pair _ _)
  have fields := Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (degreeValue (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
    (σ := ![fstT (fstT a),sndT (fstT a),fstT (sndT a),sndT (sndT a),fstT y,j])
    (σ' := ![z,h,B,N,r,j]) (fun p => by
      fin_cases p
      · exact (congrFst u).eqTrans (fst_pair _ _)
      · exact (congrSnd u).eqTrans (snd_pair _ _)
      · exact (congrFst v).eqTrans (fst_pair _ _)
      · exact (congrSnd v).eqTrans (snd_pair _ _)
      · exact fst_pair _ _
      · exact .eqRefl j)
  simpa [degreeBody,inst2,a,y,x] using fields

theorem row_value (z h B N i M : PTm n) : Γ ⊢[PRAAx]
    row matrix i M (data z h B N) ≐ MValue z h B (succ (N+i)) M := by
  refine GaussianRationalFiniteSum.sum_congr_bounded (rowBody matrix) MBody M (pairT i (data z h B N))
    (data z h B (succ (N+i))) (.allI (.impI ?_))
  let s (a : PTm n) := Syn.shift a
  let Δ := lt (var 0) (s M) :: Γ.map Fm.shift
  have e := (row_entry (Γ := Δ) matrix (s i) (var 0) (data (s z) (s h) (s B) (s N))).eqTrans
    ((matrix_at (s z) (s h) (s B) (s N) (s i) (var 0)).eqTrans
      (GaussianBarnesCanonicalHigherMercatorSum.body_at (s z) (s h) (s B) (succ (s N+s i)) (var 0)).eqSymm)
  simpa only [s,Δ,Syn.shift,GaussianBarnesCanonicalHigherMercatorSum.subst_data,subst_pairT,PTm.subst_add,
    ConciseIPRA.PTm.subst_succ] using e

theorem column_value (z h B N r j : PTm n) : Γ ⊢[PRAAx]
    column matrix j r (data z h B N) ≐ degreeValue z h B N r j := by
  let w := power (ofGaussian h B) (degree j)
  let x := TData z B N j
  have eq : Γ ⊢[PRAAx] column matrix j r (data z h B N) ≐ sum (multiplyBody TBody) r (pairT w x) := by
    refine GaussianRationalFiniteSum.sum_congr_bounded (columnBody matrix) (multiplyBody TBody)
      r (pairT j (data z h B N)) (pairT w x) (.allI (.impI ?_))
    let s (a : PTm n) := Syn.shift a
    let Δ := lt (var 0) (s r) :: Γ.map Fm.shift
    let w' := power (ofGaussian (s h) (s B)) (degree (s j))
    let x' := TData (s z) (s B) (s N) (s j)
    have a := (column_entry (Γ := Δ) matrix (var 0) (s j) (data (s z) (s h) (s B) (s N))).eqTrans
      (matrix_at (s z) (s h) (s B) (s N) (var 0) (s j))
    have b := (multiply_body_at (Γ := Δ) TBody w' (var 0) x').eqTrans
      ((GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (GaussianBarnesCanonicalHigherTail.body_at
        (s z) (s B) (s N) (s j) (var 0))).eqTrans (qmul_commutative _ _))
    simpa only [s,Δ,w,x,w',x',Syn.shift,GaussianBarnesCanonicalHigherMercatorSum.subst_data,
      GaussianBarnesCanonicalHigherTail.subst_data,subst_pairT,GaussianRationalReciprocal.subst_power,
      GaussianRationalHorner.subst_ofGaussian,GaussianBarnesCanonicalHigherRows.subst_degree] using a.eqTrans b.eqSymm
  exact eq.eqTrans ((sum_multiply TBody w r x).eqTrans (qmul_commutative _ _))

theorem transpose (z h B N r M : PTm n) : Γ ⊢[PRAAx]
    rowFirst matrix r M (data z h B N) ≐ polynomial z h B N r M := by
  refine (GaussianRationalFubini.fubini matrix r M (data z h B N)).eqTrans ?_
  refine GaussianRationalFiniteSum.sum_congr_bounded (columnSumBody matrix) degreeBody
    M (pairT r (data z h B N)) (pairT r (data z h B N)) (.allI (.impI ?_))
  let s (a : PTm n) := Syn.shift a
  let Δ := lt (var 0) (s M) :: Γ.map Fm.shift
  have e := (column_sum_at (Γ := Δ) matrix (var 0) (s r) (data (s z) (s h) (s B) (s N))).eqTrans
    ((column_value (s z) (s h) (s B) (s N) (s r) (var 0)).eqTrans
      (degree_at (s z) (s h) (s B) (s N) (s r) (var 0)).eqSymm)
  simpa only [s,Δ,Syn.shift,GaussianBarnesCanonicalHigherMercatorSum.subst_data,subst_pairT] using e

theorem actual_Barnes_higher_Mercator_coefficient_transpose_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let z := var 0
     let h := var 1
     let B := var 2
     let N := var 3
     let r := var 4
     let M := var 5
     rowFirst matrix r M (data z h B N) ≐ polynomial z h B N r M) :=
  closeUniv 6 (transpose _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHigherMercatorTranspose
