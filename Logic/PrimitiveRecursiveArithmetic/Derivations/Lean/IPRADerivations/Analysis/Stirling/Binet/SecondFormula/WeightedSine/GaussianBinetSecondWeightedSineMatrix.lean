import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.WeightedSine.GaussianBinetSecondWeightedSineGrid
import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.Rectangles.GaussianBinetOscillatorySineSmallStrip

/-!
# The original weighted sine cells on a positive frequency suffix

The original sine data retain their actual clock, frequency mesh,
and complex argument. Only the two rational time coordinates are
filled from the outer grid. A frequency offset includes precisely
the retained original sine cells.
-/

set_option autoImplicit false
set_option maxHeartbeats 680000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSecondWeightedSineMatrix

open_ipra
open GaussianBinetSecondDecayPointwise (fullDecay)
open GaussianCompactRiemannName
  (sampleData field0 field1 field2 field3 field4 field5
    field0_at field1_at field2_at field3_at field4_at field5_at
    subst_field0 subst_field1 subst_field2 subst_field3 subst_field4 subst_field5)
open GaussianRationalFiniteProduct (offset_at)
open GaussianRationalFiniteSum (sum termsEqual multiplyBody multiply_body_at sum_multiply)
open GaussianRationalFubini (row rowBody row_entry)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalRiemannRefinement (weight)
open GaussianReciprocalHorner (qmul_associative)
open GaussianRationalHorner (qmul)
open GaussianRationalSyntheticDivision (qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "RectBody" => GaussianBinetOscillatorySineRectangle.body
local notation "rectData" => GaussianBinetOscillatorySineRectangle.data

def data (p M T H J X Y D sign R L N cut : PTm n) : PTm n :=
  sampleData zero M T H J (pairT cut (rectData p X Y D sign zero one R T L N))

private def base (d : PTm n) : PTm n := sndT (field5 d)
private def angleData (j d : PTm n) : PTm n :=
  let b := base d
  pairT (fstT (field5 d)) (sampleData (field0 b) (field2 d*j) (field1 d) (field3 b) (field4 b) (field5 b))

private def decay (j d : PTm n) : PTm n := fullDecay (field0 (base d)) (field2 d*j) (field1 d) (field3 d) (field4 d)

def term (j r d : PTm n) : PTm n := qmul (inst2 (offB RectBody) r (angleData j d)) (decay j d)
def matrix : PTm 3 := term (var 0) (var 1) (var 2)

ipra_subst data [one]

@[simp] private theorem subst_angleData {m : ℕ} (σ : Fin n → PTm m) (j d : PTm n) :
    Syn.subst σ (angleData j d) = angleData (Syn.subst σ j) (Syn.subst σ d) := by simp [angleData,base]

@[simp] private theorem subst_decay {m : ℕ} (σ : Fin n → PTm m) (j d : PTm n) :
    Syn.subst σ (decay j d) = decay (Syn.subst σ j) (Syn.subst σ d) := by simp [decay,base,fullDecay,two]

@[simp] theorem subst_term {m : ℕ} (σ : Fin n → PTm m) (j r d : PTm n) :
    Syn.subst σ (term j r d) = term (Syn.subst σ j) (Syn.subst σ r) (Syn.subst σ d) := by
  simp only [term,GaussianRationalHorner.subst_qmul,subst_decay]
  congr 1
  simp only [inst2,Syn.subst_subst]
  congr 1
  funext i
  fin_cases i <;> simp

theorem matrix_at (j r d : PTm n) : inst3 matrix j r d = term j r d := by
  simp only [inst3,matrix,subst_term,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons]

private theorem seed_at (p M T H J X Y D sign R L N cut : PTm n) :
    Γ ⊢[PRAAx] base (data p M T H J X Y D sign R L N cut) ≐ rectData p X Y D sign zero one R T L N :=
  (congrSnd (field5_at _ _ _ _ _ _)).eqTrans (snd_pair _ _)

private theorem angle_data_at (j p M T H J X Y D sign R L N cut : PTm n) :
    Γ ⊢[PRAAx] angleData j (data p M T H J X Y D sign R L N cut) ≐
      pairT cut (rectData p X Y D sign (T*j) M R T L N) := by
  let d := data p M T H J X Y D sign R L N cut
  let u := rectData p X Y D sign zero one R T L N
  let b := base d
  have eu : Γ ⊢[PRAAx] b ≐ u := seed_at _ _ _ _ _ _ _ _ _ _ _ _ _
  have start : Γ ⊢[PRAAx] fstT (field5 d) ≐ cut :=
    (congrFst (field5_at _ _ _ _ _ _)).eqTrans (fst_pair _ _)
  have B3 : Γ ⊢[PRAAx] field3 b ≐ field3 u := by
    simpa only [subst_field3,Syn.subst_var,Syn.inst_zero] using Prf.eqCongr1 (field3 (var 0)) eu
  have B4 : Γ ⊢[PRAAx] field4 b ≐ field4 u := by
    simpa only [subst_field4,Syn.subst_var,Syn.inst_zero] using Prf.eqCongr1 (field4 (var 0)) eu
  have B5 : Γ ⊢[PRAAx] field5 b ≐ field5 u := by
    simpa only [subst_field5,Syn.subst_var,Syn.inst_zero] using Prf.eqCongr1 (field5 (var 0)) eu
  exact congrPairT start
    (congrPairT ((congrFst eu).eqTrans (field0_at _ _ _ _ _ _))
      (congrPairT (congrMul (field2_at _ _ _ _ _ _) (.eqRefl j))
        (congrPairT (field1_at _ _ _ _ _ _)
          (congrPairT (B3.eqTrans (field3_at _ _ _ _ _ _))
            (congrPairT (B4.eqTrans (field4_at _ _ _ _ _ _))
              (B5.eqTrans (field5_at _ _ _ _ _ _)))))))

private theorem decay_at (j p M T H J X Y D sign R L N cut : PTm n) :
    Γ ⊢[PRAAx] decay j (data p M T H J X Y D sign R L N cut) ≐ fullDecay (p+N) (T*j) M H J := by
  let d := data p M T H J X Y D sign R L N cut
  let b := base d
  have front := (congrFst (seed_at (Γ := Γ) p M T H J X Y D sign R L N cut)).eqTrans
    (field0_at (p+N) zero one (D*L) N _)
  have ht : Γ ⊢[PRAAx] field2 d*j ≐ T*j := congrMul (field2_at _ _ _ _ _ _) (.eqRefl j)
  have hx : Γ ⊢[PRAAx] field1 d ≐ M := field1_at _ _ _ _ _ _
  have hh : Γ ⊢[PRAAx] field3 d ≐ H := field3_at _ _ _ _ _ _
  have hj : Γ ⊢[PRAAx] field4 d ≐ J := field4_at _ _ _ _ _ _
  change Γ ⊢[PRAAx] GaussianEulerDecayMesh.observation (two*((field2 d*j)*field3 d)) (field1 d*field4 d) (field0 b) ≐
    GaussianEulerDecayMesh.observation (two*((T*j)*H)) (M*J) (p+N)
  simpa only [GaussianEulerDecayMesh.subst_observation,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (GaussianEulerDecayMesh.observation (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![two*((field2 d*j)*field3 d),field1 d*field4 d,field0 b])
      (σ' := ![two*((T*j)*H),M*J,p+N])
      (fun a => by fin_cases a; exact congrMul (.eqRefl two) (congrMul ht hh); exact congrMul hx hj; exact front)

theorem cell_at (j r p M T H J X Y D sign R L N cut : PTm n) :
    Γ ⊢[PRAAx] inst3 matrix j r (data p M T H J X Y D sign R L N cut) ≐
      qmul (inst2 (offB RectBody) r (pairT cut (rectData p X Y D sign (T*j) M R T L N)))
        (fullDecay (p+N) (T*j) M H J) := by
  rw [matrix_at]
  exact qmul_congr (congrInst2 _ (.eqRefl r) (angle_data_at j p M T H J X Y D sign R L N cut))
    (decay_at j p M T H J X Y D sign R L N cut)

theorem original_cell_at (j r p M T H J X Y D sign R L N cut : PTm n) :
    Γ ⊢[PRAAx] inst3 matrix j r (data p M T H J X Y D sign R L N cut) ≐
      qmul (inst2 RectBody (cut+r) (rectData p X Y D sign (T*j) M R T L N))
        (fullDecay (p+N) (T*j) M H J) :=
  (cell_at j r p M T H J X Y D sign R L N cut).eqTrans
    (qmul_congr (offset_at RectBody cut r _) (.eqRefl _))

/-- The frequency row carries exactly the original suffix sampler and
the original frozen decay at the shared clock. -/
theorem suffix_row_at (j p M T H J X Y D sign R L N cut : PTm n) :
    Γ ⊢[PRAAx] qmul (weight (D*L) one N) (row matrix j (monus N cut) (data p M T H J X Y D sign R L N cut)) ≐
      qmul (GaussianBinetOscillatorySineSmallStrip.suffixValue p X Y D sign (T*j) M R T L N cut)
        (fullDecay (p+N) (T*j) M H J) := by
  let d := data p M T H J X Y D sign R L N cut
  let x := pairT cut (rectData p X Y D sign (T*j) M R T L N)
  let e := fullDecay (p+N) (T*j) M H J
  let w := weight (D*L) one N
  let f := offB RectBody
  let C := monus N cut
  have cells : Γ ⊢[PRAAx] termsEqual (rowBody matrix) (multiplyBody f) C (pairT j d) (pairT e x) := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s C)::Γ.map Fm.shift
    let r : PTm (n+1) := var 0
    let g := inst2 f r (s x)
    have left : Δ ⊢[PRAAx] inst2 (rowBody matrix) r (pairT (s j) (s d)) ≐ qmul g (s e) :=
      (row_entry (Γ := Δ) matrix (s j) r (s d)).eqTrans
      (by simpa only [s,d,x,e,f,g,Syn.shift,subst_data,subst_pairT,GaussianBinetOscillatorySineRectangle.subst_data,
        PTm.subst_add,PTm.subst_mul,fullDecay,GaussianEulerDecayMesh.subst_observation,
        two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
        cell_at (Γ := Δ) (s j) r (s p) (s M) (s T) (s H) (s J) (s X) (s Y) (s D) (s sign) (s R) (s L) (s N) (s cut))
    have right := multiply_body_at (Γ := Δ) f (s e) r (s x)
    simpa only [termsEqual,Syn.shift,subst_pairT,s,Δ,r] using
      left.eqTrans ((qmul_commutative g (s e)).eqTrans right.eqSymm)
  let z := sum f C x
  have exactSum : Γ ⊢[PRAAx] row matrix j C d ≐ qmul e z := by
    change Γ ⊢[PRAAx] sum (rowBody matrix) C (pairT j d) ≐ qmul e z
    have bind : Γ ⊢[PRAAx] sum (rowBody matrix) C (pairT j d) ≐ sum (multiplyBody f) C (pairT e x) :=
      GaussianRationalFiniteSum.sum_congr_bounded (rowBody matrix) (multiplyBody f) C (pairT j d) (pairT e x) cells
    exact bind.eqTrans (sum_multiply f e C x)
  exact (qmul_congr (.eqRefl w) exactSum).eqTrans
    ((qmul_congr (.eqRefl w) (qmul_commutative e z)).eqTrans
      ((qmul_associative w z e).eqSymm))

end LeanProofs.IPRA.Analysis.GaussianBinetSecondWeightedSineMatrix
