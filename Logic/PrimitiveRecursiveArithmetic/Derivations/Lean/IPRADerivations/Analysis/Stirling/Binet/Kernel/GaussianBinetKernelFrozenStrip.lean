import IPRADerivations.Analysis.Stirling.Binet.Kernel.GaussianBinetKernelFrozenPrefix
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Strips.GaussianBinetLaplaceStripCutoff

/-!
# Shared-clock finite kernel on the original Laplace strip grid

Use the original physical tags and Laplace exponential. Replacing the
cofinal kernel by its literal finite prefix incurs a uniform error per
cell. Weighting by the physical mesh cancels the grid count.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBinetKernelFrozenStrip

open_ipra
open GaussianBinetKernelFrozenPrefix (dampedValue damped_error)
open GaussianBinetLaplaceStrip (source subst_source tagNumerator tag_inside)
open GaussianCompactRiemannName (grid grid_inside quadrature sampleBody sampleData sample_body_at
  field0 field1 field2 field3 field4 field5 field0_at field1_at field2_at field3_at field4_at field5_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalRiemannRefinement (termsDistance sum_distance weight weight_bound)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Exp" => GaussianBinetLaplaceExponential.nameF
local notation "expData" => GaussianBinetLaplaceExponential.data
local notation "Cofinal" => GaussianBinetLaplaceStrip.evaluatorF GaussianBinetLaplaceStrip.Kernel.cofinal
local notation "cofinalData" => GaussianBinetLaplaceStrip.fixedData

def fixedData (k N X Y D sign R T : PTm n) : PTm n := sampleData X Y D sign R (pairT T (pairT k N))
def rowValue (p k N X Y D sign R T A B : PTm n) : PTm n :=
  dampedValue (ap2 Exp p (expData X Y D sign R T A B)) k N A B

def evaluatorTerm (p t x : PTm n) : PTm n :=
  rowValue p (fstT (sndT (field5 x))) (sndT (sndT (field5 x)))
    (field0 x) (field1 x) (field2 x) (field3 x) (field4 x) (fstT (field5 x)) (tagNumerator t) (sndT t)
def evaluatorF : PR 3 := PTm.toPR (evaluatorTerm (var 0) (var 1) (var 2))

def value (p k N M X Y D sign R T A C E : PTm n) : PTm n :=
  quadrature evaluatorF p M (E+A) C E (fixedData k N X Y D sign R T)

ipra_subst fixedData

ipra_subst rowValue [dampedValue]

ipra_subst evaluatorTerm

ipra_subst value

private theorem val_4 {α : Type} (a b c d e f g h : α) : ![a,b,c,d,e,f,g,h] (4 : Fin 8) = e := rfl
private theorem val_5 {α : Type} (a b c d e f g h : α) : ![a,b,c,d,e,f,g,h] (5 : Fin 8) = f := rfl
private theorem val_6 {α : Type} (a b c d e f g h : α) : ![a,b,c,d,e,f,g,h] (6 : Fin 8) = g := rfl
private theorem val_7 {α : Type} (a b c d e f g h : α) : ![a,b,c,d,e,f,g,h] (7 : Fin 8) = h := rfl

theorem evaluator_at (p t k N X Y D sign R T : PTm n) :
    Γ ⊢[PRAAx] ap3 evaluatorF p t (fixedData k N X Y D sign R T) ≐
      rowValue p k N X Y D sign R T (tagNumerator t) (sndT t) := by
  let x := fixedData k N X Y D sign R T
  have eval : Γ ⊢[PRAAx] ap3 evaluatorF p t x ≐ evaluatorTerm p t x := by
    simpa only [evaluatorF,ap3,subst_evaluatorTerm,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (evaluatorTerm (var 0) (var 1) (var 2) : PTm 3) ![p,t,x]
  have ps : Γ ⊢[PRAAx] sndT (field5 x) ≐ pairT k N :=
    (congrSnd (field5_at X Y D sign R (pairT T (pairT k N)))).eqTrans (snd_pair _ _)
  let A := tagNumerator t
  let B := sndT t
  have exp : Γ ⊢[PRAAx] expData (field0 x) (field1 x) (field2 x) (field3 x) (field4 x) (fstT (field5 x)) A B ≐
      expData X Y D sign R T A B := by
    simpa only [GaussianBinetLaplaceExponential.subst_data,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,val_4,val_5,val_6,val_7,Matrix.head_cons,Matrix.tail_cons] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
        (expData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) : PTm 8)
        (σ := ![field0 x,field1 x,field2 x,field3 x,field4 x,fstT (field5 x),A,B])
        (σ' := ![X,Y,D,sign,R,T,A,B]) (fun i => by
          fin_cases i
          exact field0_at _ _ _ _ _ _
          exact field1_at _ _ _ _ _ _
          exact field2_at _ _ _ _ _ _
          exact field3_at _ _ _ _ _ _
          exact field4_at _ _ _ _ _ _
          exact (congrFst (field5_at X Y D sign R (pairT T (pairT k N)))).eqTrans (fst_pair _ _)
          exact (Prf.eqRefl A : Γ ⊢[PRAAx] A ≐ A)
          exact (Prf.eqRefl B : Γ ⊢[PRAAx] B ≐ B))
  have ker : Γ ⊢[PRAAx] GaussianBinetKernelFrozenPrefix.value (fstT (sndT (field5 x))) (sndT (sndT (field5 x))) A B ≐
      GaussianBinetKernelFrozenPrefix.value k N A B := by
    simpa only [GaussianBinetKernelFrozenPrefix.subst_value,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (GaussianBinetKernelFrozenPrefix.value (var 0) (var 1) (var 2) (var 3) : PTm 4)
        (σ := ![fstT (sndT (field5 x)),sndT (sndT (field5 x)),A,B]) (σ' := ![k,N,A,B])
        (fun i => by
          fin_cases i
          exact (congrFst ps).eqTrans (fst_pair _ _)
          exact (congrSnd ps).eqTrans (snd_pair _ _)
          exact (Prf.eqRefl A : Γ ⊢[PRAAx] A ≐ A)
          exact (Prf.eqRefl B : Γ ⊢[PRAAx] B ≐ B))
  exact eval.eqTrans (GaussianRationalSyntheticDivision.qmul_congr (congrAp2 Exp (.eqRefl p) exp) ker)

theorem row_at (i p k N M X Y D sign R T A C E : PTm n) : Γ ⊢[PRAAx]
    inst2 (sampleBody evaluatorF) i (sampleData p M (E+A) C E (fixedData k N X Y D sign R T)) ≐
      rowValue p k N X Y D sign R T (tagNumerator (grid i M (E+A) C E)) (sndT (grid i M (E+A) C E)) :=
  (sample_body_at evaluatorF i p M (E+A) C E (fixedData k N X Y D sign R T)).eqTrans
    (evaluator_at p (grid i M (E+A) C E) k N X Y D sign R T)

private theorem row_error (i p k N M X Y D sign R T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T A C E) (hM : Γ ⊢[PRAAx] le one M) (hi : Γ ⊢[PRAAx] lt i M)
    (hN : Γ ⊢[PRAAx] le (unit p) N) (hk : Γ ⊢[PRAAx] le (N*unit p) (unit k)) : Γ ⊢[PRAAx]
    distanceBounded (inst2 (sampleBody evaluatorF) i (sampleData p M (E+A) C E (fixedData k N X Y D sign R T)))
      (inst2 (sampleBody Cofinal) i (sampleData p M (E+A) C E (cofinalData X Y D sign R T zero))) (num 14) (unit p) := by
  let t := grid i M (E+A) C E
  have hE := h.andE₂.andE₁
  have within := grid_inside i M (E+A) C E (le_trans hE (le_add_right E A)) hE hM (le_of_lt hi)
  have ht := tag_inside t A C E T hE h.andE₂.andE₂ within
  have bound := damped_error p k N X Y D sign R T (tagNumerator t) (sndT t)
    (.andI h.andE₁ (.andI within.andE₂.andE₁ ht.andE₂)) hN hk
  have cofinal := (sample_body_at (Γ := Γ) Cofinal i p M (E+A) C E (cofinalData X Y D sign R T zero)).eqTrans
    (GaussianBinetLaplaceStrip.evaluator_at .cofinal p t X Y D sign R T zero)
  exact distance_congr (row_at i p k N M X Y D sign R T A C E).eqSymm cofinal.eqSymm (.eqRefl _) (.eqRefl _) bound

theorem quadrature_error (p k N M X Y D sign R T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T A C E) (hM : Γ ⊢[PRAAx] le one M)
    (hN : Γ ⊢[PRAAx] le (unit p) N) (hk : Γ ⊢[PRAAx] le (N*unit p) (unit k)) : Γ ⊢[PRAAx]
    distanceBounded (value p k N M X Y D sign R T A C E)
      (quadrature Cofinal p M (E+A) C E (cofinalData X Y D sign R T zero)) (num 14*C) (E*unit p) := by
  let x := sampleData p M (E+A) C E (fixedData k N X Y D sign R T)
  let y := sampleData p M (E+A) C E (cofinalData X Y D sign R T zero)
  let u := GaussianRationalFiniteSum.sum (sampleBody evaluatorF) M x
  let v := GaussianRationalFiniteSum.sum (sampleBody Cofinal) M y
  let w := weight C E M
  have rows : Γ ⊢[PRAAx] termsDistance (sampleBody evaluatorF) (sampleBody Cofinal) M x y (num 14) (unit p) := by
    refine .allI (.impI ?_)
    let s (t : PTm n) := Syn.shift t
    let Δ := Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s R) (s T) (s A) (s C) (s E) :=
      by simpa only [Δ,Fm.shift,Syn.shift,s,subst_source] using h.shift
    have ms : Δ ⊢[PRAAx] le one (s M) := by simpa [Δ,Fm.shift,Syn.shift,s] using hM.shift
    have ns : Δ ⊢[PRAAx] le (unit (s p)) (s N) := by simpa [Δ,Fm.shift,Syn.shift,s] using hN.shift
    have ks : Δ ⊢[PRAAx] le (s N*unit (s p)) (unit (s k)) := by simpa [Δ,Fm.shift,Syn.shift,s] using hk.shift
    simpa only [termsDistance,x,y,Δ,Syn.shift,s,GaussianCompactRiemannName.subst_sampleData,subst_fixedData,
      subst_pairT,PTm.subst_add,PTm.subst_num,ConciseIPRA.PTm.subst_zero,GaussianCoefficientNameBounds.subst_unit] using
      row_error (var 0) (s p) (s k) (s N) (s M) (s X) (s Y) (s D) (s sign) (s R) (s T) (s A) (s C) (s E)
        hs.wk ms.wk Prf.hyp0 ns.wk ks.wk
  have hp := unit_positive (Γ := Γ) p
  have hE := h.andE₂.andE₁
  have d := positive_product _ _ hE hM
  have raw := GaussianRationalReciprocal.bounded_product w _ C (E*M) (M*num 14) (unit p) d hp
    (weight_bound C E M hE hM) (sum_distance _ _ M x y _ _ hp rows)
  have scaled := GaussianRationalReciprocal.bound_congr
    (GaussianRationalRoundedPower.multiplication_difference w u v).eqSymm (.eqRefl _) (.eqRefl _) raw
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ d hp) (positive_product _ _ hE hp)
    (le_of_eq_add (d := zero) (by ipra_ring)) scaled

end LeanProofs.IPRA.Analysis.GaussianBinetKernelFrozenStrip
