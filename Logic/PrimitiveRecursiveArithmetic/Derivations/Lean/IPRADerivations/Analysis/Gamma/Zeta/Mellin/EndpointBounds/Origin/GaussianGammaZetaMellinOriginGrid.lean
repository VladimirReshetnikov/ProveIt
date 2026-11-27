import IPRADerivations.Analysis.Gamma.Zeta.Mellin.EndpointBounds.Origin.GaussianGammaZetaMellinOriginCell

/-!
# A finite lower cutoff estimate on the original Mellin root grid

The literal right grid starts at the first positive root tag. Every
physical width is integrated on its own powered cell, so the uniform
right-cell estimate sums in the root coordinate.
-/

set_option autoImplicit false
set_option maxHeartbeats 720000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinOriginGrid

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianCompactRiemannName
  (sampleData field0 field1 field2 field3 field4 field0_at field1_at field2_at field3_at field4_at)
open GaussianGammaZetaMellinOriginCell (value subst_value right_cell_bound)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalRiemannRefinement (constantBody constant_entry constant_sum termsDistance sum_distance)
open GaussianReconstructionRoots (distance_zero_iff)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def data (p z D k b : PTm n) : PTm n := sampleData p z D k b zero

def body : PTm 2 :=
  let d : PTm 2 := var 1
  value (field0 d) (field1 d) (field2 d) (field3 d) (var 0) (succ (var 0)) (field4 d)

def gridValue (p z D k b N : PTm n) : PTm n := GaussianRationalFiniteSum.sum body N (data p z D k b)

ipra_subst data

theorem cell_at (i p z D k b : PTm n) :
    Γ ⊢[PRAAx] inst2 body i (data p z D k b) ≐ value p z D k i (succ i) b := by
  let d := data p z D k b
  have expansion : inst2 body i d = value (field0 d) (field1 d) (field2 d) (field3 d) i (succ i) (field4 d) := by
    simp [body,inst2]
  rw [expansion]
  let code : PTm 6 := value (var 0) (var 1) (var 2) (var 3) (var 4) (succ (var 4)) (var 5)
  let a : Fin 6 → PTm n := ![field0 d,field1 d,field2 d,field3 d,i,field4 d]
  let b' : Fin 6 → PTm n := ![p,z,D,k,i,b]
  have read := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) code
    (σ := a) (σ' := b') (fun j => by
      fin_cases j
      · exact field0_at _ _ _ _ _ _
      · exact field1_at _ _ _ _ _ _
      · exact field2_at _ _ _ _ _ _
      · exact field3_at _ _ _ _ _ _
      · exact .eqRefl _
      · exact field4_at _ _ _ _ _ _)
  have left : Syn.subst a code = value (field0 d) (field1 d) (field2 d) (field3 d) i (succ i) (field4 d) := by
    dsimp only [code]
    rw [subst_value,ConciseIPRA.PTm.subst_succ]
    rfl
  have right : Syn.subst b' code = value p z D k i (succ i) b := by
    dsimp only [code]
    rw [subst_value,ConciseIPRA.PTm.subst_succ]
    rfl
  rw [left,right] at read
  exact read

theorem grid_bound (p z R D k b N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R D (succ k))
    (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le N b) :
    Γ ⊢[PRAAx] bounded (gridValue p z D k b N) (N*(succ k*(unit p+num 3))) (b*unit p) := by
  let x := data p z D k b
  let V := succ k*(unit p+num 3)
  let B := b*unit p
  have hB : Γ ⊢[PRAAx] le one B := positive_product _ _ hb (unit_positive p)
  have cells : Γ ⊢[PRAAx] termsDistance body constantBody N x qzero V B := by
    refine .allI (.impI ?_)
    let s (t : PTm n) := Syn.shift t
    let i : PTm (n+1) := var 0
    let Δ := lt i (s N)::Γ.map Fm.shift
    have coeff : Δ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source (s z) (s R) (s D) (succ (s k)) := by
      simpa [Δ,s,Fm.shift,Syn.shift] using h.shift.wk
    have bpos : Δ ⊢[PRAAx] le one (s b) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hb.shift.wk
    have Nbound : Δ ⊢[PRAAx] le (s N) (s b) := by simpa [Δ,s,Fm.shift,Syn.shift] using hN.shift.wk
    have right : Δ ⊢[PRAAx] le (succ i) (s b) := le_trans Prf.hyp0 Nbound
    have admit : Δ ⊢[PRAAx] GaussianEulerLowerPowerOrder.source (s z) (s R) (s D) (succ (s k)) (succ i) (s b) :=
      .andI coeff (.andI (.andI (zero_lt_succ i) bpos) right)
    have hi : Δ ⊢[PRAAx] le i (succ i) := le_succ_self _
    have width := (congrMonus (succ_eq_add_one (Γ := Δ) i) (.eqRefl i)).eqTrans (add_monus' one i)
    have remove : Δ ⊢[PRAAx] succ (s k)*one ≐ succ (s k) := (mul_comm _ _).eqTrans (one_mul _)
    have read := cell_at (Γ := Δ) i (s p) (s z) (s D) (s k) (s b)
    have bound := bound_congr read.eqSymm
      (congrMul ((congrMul (.eqRefl _) width).eqTrans remove) (.eqRefl _))
      (.eqRefl _) (right_cell_bound (s p) (s z) (s R) (s D) (s k) i (succ i) (s b) admit hi)
    have den := positive_product _ _ bpos (unit_positive (s p))
    simpa [Δ,i,s,x,V,B,Syn.shift,constant_entry,one] using (distance_zero_iff _ _ _ den).iffMpr bound
  have eqZero := (constant_sum (Γ := Γ) qzero N).eqTrans (GaussianRationalFactorialEulerSums.scale_zero_value N)
  exact (distance_zero_iff _ _ _ hB).iffMp
    (distance_congr (.eqRefl _) eqZero (.eqRefl _) (.eqRefl _)
      (sum_distance body constantBody N x qzero V B hB cells))

theorem shrinking_grid_bound (p h z R D k b N : PTm n)
    (hi : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R D (succ k))
    (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le N b)
    (small : Γ ⊢[PRAAx] le ((N*succ k)*unit h) b) :
    Γ ⊢[PRAAx] bounded (gridValue p z D k b N) (num 4) (unit h) := by
  let U := unit p
  have hu := unit_positive (Γ := Γ) p
  have narrow : Γ ⊢[PRAAx] le (U+num 3) (num 4*U) := by ipra_le 3*sl hu
  have major := le_mul_mono small narrow
  refine bounded_radius_mono _ _ _ _ _ (positive_product _ _ hb hu) (unit_positive h) ?_
    (grid_bound p z R D k b N hi hb hN)
  change Γ ⊢[PRAAx] le ((N*(succ k*(U+num 3)))*unit h) (num 4*(b*U))
  exact le_congr (by ipra_ring) (by ipra_ring) major

theorem actual_gamma_zeta_mellin_shrinking_grid_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let p := var 0
     let h := var 1
     let z := var 2
     let R := var 3
     let D := var 4
     let k := var 5
     let b := var 6
     let N := var 7
     (GaussianEulerLowerPowerCoefficients.source z R D (succ k) ⋏
       (le one b ⋏ (le N b ⋏ le ((N*succ k)*unit h) b))) ⟶
       bounded (gridValue p z D k b N) (num 4) (unit h)) :=
  closeUniv 8 (.impI (shrinking_grid_bound _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinOriginGrid
