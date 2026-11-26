import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.GaussianBinetArctangentCosineLaplace
import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.GaussianBinetArctangentQuadrature

/-!
# Actual arctangent samples and the finite cosine rectangle

Compare identical outer meshes. On each frequency row use the actual
complex Laplace cosine panel average with the same horizon and inner
mesh. Exact finite weighted-sum arithmetic propagates that error
with precisely the outer interval length.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBinetArctangentCosineRectangle

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetArctangentCosineLaplace (value error finite_error)
open GaussianBinetArctangentResolvent (pole subst_pole)
open GaussianInverseBinomialRows (negative_congr)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianBinetLaplaceStrip (tagNumerator tag_inside)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (field0 field1 field2 field3 field4 field5 grid grid_inside sampleBody sampleData sample_body_at quadrature)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalRiemannRefinement (termsDistance sum_distance weight weight_bound leftSum)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianBinetArctangentQuadrature.evaluatorF
local notation "fixed" => GaussianBinetArctangentQuadrature.fixedData

local notation "LV" => GaussianBinetExponentialIntegralGrid.value

def fixedData (X Y D sign R U L N : PTm n) : PTm n := sampleData X Y D sign R (pairT U (pairT L N))
def rowTerm (p t x : PTm n) : PTm n :=
  value p (field0 x) (field1 x) (field2 x) (field3 x) (tagNumerator t) (sndT t) (field4 x)
    (fstT (field5 x)) (fstT (sndT (field5 x))) (sndT (sndT (field5 x)))
def body : PTm 2 :=
  rowTerm (field0 (var 1)) (grid (var 0) (field1 (var 1)) (field2 (var 1)) (field3 (var 1)) (field4 (var 1))) (field5 (var 1))
def rectangle (p M X Y D sign A B R U L N : PTm n) : PTm n :=
  leftSum body M (sampleData p M (B+zero) A B (fixedData X Y D sign R U L N)) A B

@[simp] theorem subst_fixedData {m : ℕ} (σ : Fin n → PTm m) (X Y D sign R U L N : PTm n) :
    Syn.subst σ (fixedData X Y D sign R U L N) = fixedData (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D)
      (Syn.subst σ sign) (Syn.subst σ R) (Syn.subst σ U) (Syn.subst σ L) (Syn.subst σ N) := by simp [fixedData]

@[simp] theorem subst_rowTerm {m : ℕ} (σ : Fin n → PTm m) (p t x : PTm n) :
    Syn.subst σ (rowTerm p t x) = rowTerm (Syn.subst σ p) (Syn.subst σ t) (Syn.subst σ x) := by
  simp only [rowTerm,GaussianBinetArctangentCosineLaplace.subst_value,GaussianBinetLaplaceStrip.subst_tagNumerator,
    subst_sndT,subst_fstT,GaussianCompactRiemannName.subst_field0,GaussianCompactRiemannName.subst_field1,
    GaussianCompactRiemannName.subst_field2,GaussianCompactRiemannName.subst_field3,GaussianCompactRiemannName.subst_field4,
    GaussianCompactRiemannName.subst_field5]

@[simp] theorem subst_rectangle {m : ℕ} (σ : Fin n → PTm m) (p M X Y D sign A B R U L N : PTm n) :
    Syn.subst σ (rectangle p M X Y D sign A B R U L N) = rectangle (Syn.subst σ p) (Syn.subst σ M)
      (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D) (Syn.subst σ sign) (Syn.subst σ A) (Syn.subst σ B)
      (Syn.subst σ R) (Syn.subst σ U) (Syn.subst σ L) (Syn.subst σ N) := by simp [rectangle]

private theorem value_congr {p p' q q' S S' T T' N N' : PTm n}
    (hp : Γ ⊢[PRAAx] p ≐ p') (hq : Γ ⊢[PRAAx] q ≐ q') (hS : Γ ⊢[PRAAx] S ≐ S')
    (hT : Γ ⊢[PRAAx] T ≐ T') (hN : Γ ⊢[PRAAx] N ≐ N') : Γ ⊢[PRAAx]
    LV p q S T N ≐ LV p' q' S' T' N' := by
  simpa only [GaussianBinetExponentialIntegralGrid.subst_value,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (LV (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      (σ := ![p,q,S,T,N]) (σ' := ![p',q',S',T',N'])
      (fun j => by fin_cases j; exact hp; exact hq; exact hS; exact hT; exact hN)

private theorem pole_congr (s : Bool) (A B : PTm n) {X X' Y Y' D D' sign sign' : PTm n}
    (hx : Γ ⊢[PRAAx] X ≐ X') (hy : Γ ⊢[PRAAx] Y ≐ Y') (hd : Γ ⊢[PRAAx] D ≐ D')
    (hs : Γ ⊢[PRAAx] sign ≐ sign') : Γ ⊢[PRAAx] pole s X Y D sign A B ≐ pole s X' Y' D' sign' A B := by
  have val₅ {α : Type} (a b c d e f : α) : ![a,b,c,d,e,f] (5 : Fin 6) = f := rfl
  simpa only [subst_pole,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,val₅,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (pole s (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
      (σ := ![X,Y,D,sign,A,B]) (σ' := ![X',Y',D',sign',A,B]) (fun j => by
        fin_cases j; exact hx; exact hy; exact hd; exact hs; exact .eqRefl A; exact .eqRefl B)

theorem row_term_at (p t X Y D sign R U L N : PTm n) : Γ ⊢[PRAAx]
    rowTerm p t (fixedData X Y D sign R U L N) ≐ value p X Y D sign (tagNumerator t) (sndT t) R U L N := by
  let x := fixedData X Y D sign R U L N
  have read : Γ ⊢[PRAAx] field5 x ≐ pairT U (pairT L N) := GaussianCompactRiemannName.field5_at _ _ _ _ _ _
  have tail := (congrSnd read).eqTrans (snd_pair U (pairT L N))
  have hx : Γ ⊢[PRAAx] field0 x ≐ X := GaussianCompactRiemannName.field0_at _ _ _ _ _ _
  have hy : Γ ⊢[PRAAx] field1 x ≐ Y := GaussianCompactRiemannName.field1_at _ _ _ _ _ _
  have hd : Γ ⊢[PRAAx] field2 x ≐ D := GaussianCompactRiemannName.field2_at _ _ _ _ _ _
  have hs : Γ ⊢[PRAAx] field3 x ≐ sign := GaussianCompactRiemannName.field3_at _ _ _ _ _ _
  have hr : Γ ⊢[PRAAx] field4 x ≐ R := GaussianCompactRiemannName.field4_at _ _ _ _ _ _
  have hu := (congrFst read).eqTrans (fst_pair U (pairT L N))
  have hl := (congrFst tail).eqTrans (fst_pair L N)
  have hn := (congrSnd tail).eqTrans (snd_pair L N)
  have ht := congrMul hd hl
  have equally (s : Bool) := value_congr (congrAdd (.eqRefl p) hn)
    (negative_congr (pole_congr s (tagNumerator t) (sndT t) hx hy hd hs))
    (congrMul (congrAdd hr hu) ht) ht hn
  exact qmul_congr (.eqRefl _) (qadd_congr (equally false) (equally true))

theorem cell_at (i p M a A B X Y D sign R U L N : PTm n) : Γ ⊢[PRAAx]
    inst2 body i (sampleData p M a A B (fixedData X Y D sign R U L N)) ≐
      value p X Y D sign (tagNumerator (grid i M a A B)) (sndT (grid i M a A B)) R U L N := by
  let x := fixedData X Y D sign R U L N
  let d := sampleData p M a A B x
  let t := grid i M a A B
  let t' := grid i (field1 d) (field2 d) (field3 d) (field4 d)
  have packed : Γ ⊢[PRAAx] rowTerm (field0 d) t' (field5 d) ≐ rowTerm p t x := by
    have gridRead : Γ ⊢[PRAAx] t' ≐ t := GaussianCompactRiemannName.grid_congr _ _ _ _ _ _ _ _ _ _ (.eqRefl _)
      (GaussianCompactRiemannName.field1_at _ _ _ _ _ _) (GaussianCompactRiemannName.field2_at _ _ _ _ _ _)
      (GaussianCompactRiemannName.field3_at _ _ _ _ _ _) (GaussianCompactRiemannName.field4_at _ _ _ _ _ _)
    simpa only [subst_rowTerm,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (rowTerm (var 0) (var 1) (var 2) : PTm 3)
        (σ := ![field0 d,t',field5 d]) (σ' := ![p,t,x]) (fun j => by
          fin_cases j
          · exact GaussianCompactRiemannName.field0_at _ _ _ _ _ _
          · exact gridRead
          · exact GaussianCompactRiemannName.field5_at _ _ _ _ _ _)
  simpa [body,inst2,d,t'] using packed.eqTrans (row_term_at p t X Y D sign R U L N)

private theorem cell_error (i p q M X Y D sign A B R U K L N : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hB : Γ ⊢[PRAAx] le one B)
    (hM : Γ ⊢[PRAAx] le one M) (hA : Γ ⊢[PRAAx] le A (B*U)) (hm : Γ ⊢[PRAAx] le D (K*X))
    (hL : Γ ⊢[PRAAx] le L p) (hN : Γ ⊢[PRAAx] le ((R+U)*(D*L)) N) (hpN : Γ ⊢[PRAAx] le (unit p) N)
    (hi : Γ ⊢[PRAAx] lt i M) : Γ ⊢[PRAAx] distanceBounded
      (inst2 body i (sampleData p M (B+zero) A B (fixedData X Y D sign R U L N)))
      (inst2 (sampleBody F) i (sampleData q M (B+zero) A B (fixed X Y D sign)))
      (error p R U K (D*L) L) (unit p*unit L) := by
  let t := grid i M (B+zero) A B
  have inside := grid_inside i M (B+zero) A B (le_trans hB (le_add_right B zero)) hB hM (le_of_lt hi)
  have tags := tag_inside t zero A B U hB (le_congr (by ipra_ring) (.eqRefl _) hA) inside
  have hp := cell_at (Γ := Γ) i p M (B+zero) A B X Y D sign R U L N
  have hq := (sample_body_at (Γ := Γ) F i q M (B+zero) A B (fixed X Y D sign)).eqTrans
    (GaussianBinetArctangentQuadrature.evaluator_at q t X Y D sign)
  exact distance_congr hp.eqSymm hq.eqSymm (.eqRefl _) (.eqRefl _)
    (finite_error p X Y D sign (tagNumerator t) (sndT t) R U K L N hz inside.andE₂.andE₁ tags.andE₂ hm hL hN hpN)

theorem rectangle_error (p q M X Y D sign A B R U K L N : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hB : Γ ⊢[PRAAx] le one B)
    (hM : Γ ⊢[PRAAx] le one M) (hA : Γ ⊢[PRAAx] le A (B*U)) (hm : Γ ⊢[PRAAx] le D (K*X))
    (hL : Γ ⊢[PRAAx] le L p) (hN : Γ ⊢[PRAAx] le ((R+U)*(D*L)) N) (hpN : Γ ⊢[PRAAx] le (unit p) N) :
    Γ ⊢[PRAAx] distanceBounded (rectangle p M X Y D sign A B R U L N)
      (quadrature F q M (B+zero) A B (fixed X Y D sign)) (A*error p R U K (D*L) L) (B*(unit p*unit L)) := by
  let x := sampleData p M (B+zero) A B (fixedData X Y D sign R U L N)
  let y := sampleData q M (B+zero) A B (fixed X Y D sign)
  let C := error p R U K (D*L) L
  let E := unit p*unit L
  let s (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  have zs : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s R) := by simpa [Δ,s,Fm.shift,Syn.shift] using hz.shift
  have bs : Δ ⊢[PRAAx] le one (s B) := by simpa [Δ,s,Fm.shift,Syn.shift] using hB.shift
  have ms : Δ ⊢[PRAAx] le one (s M) := by simpa [Δ,s,Fm.shift,Syn.shift] using hM.shift
  have as' : Δ ⊢[PRAAx] le (s A) (s B*s U) := by simpa [Δ,s,Fm.shift,Syn.shift] using hA.shift
  have cs : Δ ⊢[PRAAx] le (s D) (s K*s X) := by simpa [Δ,s,Fm.shift,Syn.shift] using hm.shift
  have ls : Δ ⊢[PRAAx] le (s L) (s p) := by simpa [Δ,s,Fm.shift,Syn.shift] using hL.shift
  have ns : Δ ⊢[PRAAx] le ((s R+s U)*(s D*s L)) (s N) := by simpa [Δ,s,Fm.shift,Syn.shift] using hN.shift
  have ps : Δ ⊢[PRAAx] le (unit (s p)) (s N) := by simpa [Δ,s,Fm.shift,Syn.shift] using hpN.shift
  have rows : Γ ⊢[PRAAx] termsDistance body (sampleBody F) M x y C E := by
    refine .allI (.impI ?_)
    simpa only [x,y,C,E,s,Δ,Syn.shift,GaussianCompactRiemannName.subst_sampleData,subst_fixedData,
      GaussianBinetArctangentQuadrature.subst_fixedData,GaussianBinetArctangentCosineLaplace.subst_error,
      GaussianCoefficientNameBounds.subst_unit,PTm.subst_mul,PTm.subst_add,ConciseIPRA.PTm.subst_zero] using
      cell_error (var 0) (s p) (s q) (s M) (s X) (s Y) (s D) (s sign) (s A) (s B) (s R) (s U) (s K) (s L) (s N)
        zs.wk bs.wk ms.wk as'.wk cs.wk ls.wk ns.wk ps.wk Prf.hyp0
  have e := positive_product (Γ := Γ) _ _ (unit_positive p) (unit_positive L)
  have b := positive_product (Γ := Γ) _ _ hB hM
  let u := sum body M x
  let v := sum (sampleBody F) M y
  let w := weight A B M
  have sums := sum_distance _ _ _ _ _ _ _ e rows
  have product := bounded_product w _ A (B*M) (M*C) E b e (weight_bound A B M hB hM) sums
  have scaled : Γ ⊢[PRAAx] distanceBounded (qmul w u) (qmul w v) (A*(M*C)) ((B*M)*E) :=
    bound_congr (GaussianRationalRoundedPower.multiplication_difference w u v).eqSymm (.eqRefl _) (.eqRefl _) product
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ b e) (positive_product _ _ hB e)
    (le_of_eq_add (d := zero) (by ipra_ring)) scaled

end LeanProofs.IPRA.Analysis.GaussianBinetArctangentCosineRectangle
