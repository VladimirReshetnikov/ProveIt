import IPRADerivations.Analysis.Stirling.Binet.Kernel.FrequencyGrids.GaussianBinetKernelFrequencyGrid
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.Reindexing.GaussianRationalFubini

/-!
# Exact finite kernel rectangle on the retained frequency suffix

The geometric index and the positive frequency index can be summed
in either order. At each frequency the complex damping factors
outside the frozen kernel prefix without changing its observation.
-/

set_option autoImplicit false
set_option maxHeartbeats 780000

namespace LeanProofs.IPRA.Analysis.GaussianBinetFrozenKernelRectangle

open_ipra
open GaussianBinetExponentialIntegralGrid (row subst_row)
open GaussianBinetOscillatoryColumns (damping subst_damping)
open GaussianBinetKernelFrozenPrefix (dampedBody dampedData damped_term damped_sum)
open GaussianCompactRiemannName
  (sampleData field0 field1 field2 field3 field4 field5
    field0_at field1_at field2_at field3_at field4_at field5_at)
open GaussianLogGammaEulerHead (argument)
open GaussianRationalFiniteSum (sum termsEqual sum_congr_bounded)
open GaussianRationalFubini (columnBody column_entry columnSumBody column_sum_at)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (qnegative)
open GaussianRationalRiemannRefinement (weight)
open GaussianRationalSyntheticDivision (qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (p k N S cut X Y D sign R : PTm n) : PTm n :=
  sampleData (p+N) N S cut k (pairT (qnegative (argument X Y D sign)) (R*S))

def term (i j r N S cut k x : PTm n) : PTm n :=
  let A := S*(cut+j)
  qmul (row r (fstT x) (sndT x) A N) (GaussianBinetKernelRows.value k (succ i) A N)

def matrix : PTm 3 :=
  let d : PTm 3 := var 2
  term (var 0) (var 1) (field0 d) (field1 d) (field2 d) (field3 d) (field4 d) (field5 d)

def value (p k I N S cut X Y D sign R : PTm n) : PTm n :=
  qmul (weight S one N) (GaussianRationalFubini.rowFirst matrix I (monus N cut) (data p k N S cut X Y D sign R))

ipra_subst data [GaussianLogGammaEulerRepresentation.subst_argument]

ipra_subst term

@[simp] theorem matrix_at (i j d : PTm n) :
    inst3 matrix i j d = term i j (field0 d) (field1 d) (field2 d) (field3 d) (field4 d) (field5 d) := by
  simp [matrix,inst3]

theorem cell_at (i j p k N S cut X Y D sign R : PTm n) :
    Γ ⊢[PRAAx] inst3 matrix i j (data p k N S cut X Y D sign R) ≐
      qmul (damping p X Y D sign S (cut+j) N R) (GaussianBinetKernelRows.value k (succ i) (S*(cut+j)) N) := by
  let z := qnegative (argument X Y D sign)
  let x := pairT z (R*S)
  let d := data p k N S cut X Y D sign R
  let a := ![i,j,field0 d,field1 d,field2 d,field3 d,field4 d,field5 d]
  let b := ![i,j,p+N,N,S,cut,k,x]
  let f : PTm 8 := term (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
  have bind := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) f (σ := a) (σ' := b) (fun j => by
    fin_cases j
    · exact .eqRefl _
    · exact .eqRefl _
    · exact field0_at _ _ _ _ _ _
    · exact field1_at _ _ _ _ _ _
    · exact field2_at _ _ _ _ _ _
    · exact field3_at _ _ _ _ _ _
    · exact field4_at _ _ _ _ _ _
    · exact field5_at _ _ _ _ _ _)
  have e1 : Syn.subst a f = term i j (field0 d) (field1 d) (field2 d) (field3 d) (field4 d) (field5 d) := by
    dsimp only [f]
    rw [subst_term]
    rfl
  have e2 : Syn.subst b f = term i j (p+N) N S cut k x := by
    dsimp only [f]
    rw [subst_term]
    rfl
  rw [e1,e2] at bind
  rw [matrix_at]
  let l := S*(cut+j)
  have endpoint : Γ ⊢[PRAAx] row (p+N) (fstT x) (sndT x) l N ≐ row (p+N) z (R*S) l N := by
    let g : PTm 5 := row (var 0) (var 1) (var 2) (var 3) (var 4)
    let u : Fin 5 → PTm n := ![p+N,fstT x,sndT x,l,N]
    let v : Fin 5 → PTm n := ![p+N,z,R*S,l,N]
    have proof := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) g (σ := u) (σ' := v) (fun j => by
      fin_cases j
      · exact .eqRefl _
      · exact fst_pair z (R*S)
      · exact snd_pair z (R*S)
      · exact .eqRefl _
      · exact .eqRefl _)
    have left : Syn.subst u g = row (p+N) (fstT x) (sndT x) l N := by
      dsimp only [g]
      rw [subst_row]
      rfl
    have right : Syn.subst v g = row (p+N) z (R*S) l N := by
      dsimp only [g]
      rw [subst_row]
      rfl
    rw [left,right] at proof
    exact proof
  exact bind.eqTrans (qmul_congr endpoint (.eqRefl _))

theorem column_at (j p k I N S cut X Y D sign R : PTm n) :
    Γ ⊢[PRAAx] GaussianRationalFubini.column matrix j I (data p k N S cut X Y D sign R) ≐
      qmul (damping p X Y D sign S (cut+j) N R)
        (GaussianBinetKernelFrozenPrefix.value k I (S*(cut+j)) N) := by
  let d := data p k N S cut X Y D sign R
  let c := damping p X Y D sign S (cut+j) N R
  let y := dampedData c k (S*(cut+j)) N
  have rows : Γ ⊢[PRAAx] termsEqual (columnBody matrix) dampedBody I (pairT j d) y := by
    refine .allI (.impI ?_)
    let t (z : PTm n) := Syn.shift z
    let Δ := lt (var 0) (t I) :: Γ.map Fm.shift
    let e := damping (t p) (t X) (t Y) (t D) (t sign) (t S) (t cut+t j) (t N) (t R)
    have x := (column_entry (Γ := Δ) matrix (var 0) (t j) (data (t p) (t k) (t N) (t S) (t cut)
      (t X) (t Y) (t D) (t sign) (t R))).eqTrans
        (cell_at (var 0) (t j) (t p) (t k) (t N) (t S) (t cut) (t X) (t Y) (t D) (t sign) (t R))
    simpa only [Δ,t,d,y,c,e,Syn.shift,subst_pairT,subst_data,GaussianBinetKernelFrozenPrefix.subst_dampedData,
      PTm.subst_add,PTm.subst_mul,subst_damping] using
      x.eqTrans (damped_term (var 0) e (t k) (t S*(t cut+t j)) (t N)).eqSymm
  have compare : Γ ⊢[PRAAx] sum (columnBody matrix) I (pairT j d) ≐ sum dampedBody I y :=
    GaussianRationalFiniteSum.sum_congr_bounded (columnBody matrix) dampedBody I (pairT j d) y rows
  have factor : Γ ⊢[PRAAx] sum dampedBody I y ≐ qmul c (GaussianBinetKernelFrozenPrefix.value k I (S*(cut+j)) N) :=
    damped_sum c k I (S*(cut+j)) N
  exact compare.eqTrans factor

end LeanProofs.IPRA.Analysis.GaussianBinetFrozenKernelRectangle
