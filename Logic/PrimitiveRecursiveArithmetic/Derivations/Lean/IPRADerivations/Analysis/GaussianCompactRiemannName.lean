import IPRADerivations.Analysis.GaussianRationalRiemannRefinement
import IPRADerivations.Analysis.GaussianNamedInverseRate
import IPRADerivations.Analysis.GaussianFiniteLogarithmDyadicTail
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual compact-interval Gaussian quadrature

The evaluator is the original fixed PR3 program at (precision,time,data).
The local sampled-modulus contract explicitly retains both observation
errors. It is an input theorem about the original evaluator, never a
regularity or refinement assumption on the returned quadrature.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianCompactRiemannName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open ComplexLogarithmRemainder (scale oneCode)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

@[simp] theorem up_two {k m : ℕ} (σ : Fin (k+2) → PTm m) :
    Syn.up σ (2 : Fin (k+3)) = Syn.shift (σ 1) := rfl
@[simp] theorem up_three {k m : ℕ} (σ : Fin (k+3) → PTm m) :
    Syn.up σ (3 : Fin (k+4)) = Syn.shift (σ 2) := rfl

def grid (i N a C E : PTm n) : PTm n := pairT (a*N+C*i) (E*N)
def value (t : PTm n) : PTm n := ofGaussian (scale (fstT t) oneCode) (sndT t)
def inside (a C E t : PTm n) : Fm PTm n := le one (fstT t) ⋏ (le one (sndT t) ⋏
  (le (a*sndT t) (E*fstT t) ⋏ le (E*fstT t) ((a+C)*sndT t)))
def nameData (t x : PTm n) : PTm n := pairT t x
def evaluatorName (F : PR 3) : PR 2 := PTm.toPR (ap3 F (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2)
@[simp] theorem subst_grid {l : ℕ} (σ : Fin n → PTm l) (i N a C E : PTm n) :
    Syn.subst σ (grid i N a C E) = grid (Syn.subst σ i) (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) := by simp [grid]
@[simp] theorem subst_value {l : ℕ} (σ : Fin n → PTm l) (t : PTm n) :
    Syn.subst σ (value t) = value (Syn.subst σ t) := by simp [value]
@[simp] theorem subst_inside {l : ℕ} (σ : Fin n → PTm l) (a C E t : PTm n) :
    (inside a C E t).subst σ = inside (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ t) := by simp [inside]
@[simp] theorem subst_nameData {l : ℕ} (σ : Fin n → PTm l) (t x : PTm n) :
    Syn.subst σ (nameData t x) = nameData (Syn.subst σ t) (Syn.subst σ x) := by simp [nameData]

theorem evaluator_at (F : PR 3) (p t x : PTm n) : Γ ⊢[PRAAx]
    ap2 (evaluatorName F) p (nameData t x) ≐ ap3 F p t x := by
  have old := toPR_eq (Γ := Γ) (ap3 F (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2) ![p,nameData t x]
  have e : Γ ⊢[PRAAx] ap2 (evaluatorName F) p (nameData t x) ≐
      ap3 F p (fstT (nameData t x)) (sndT (nameData t x)) := by
    simpa only [evaluatorName,ap2,subst_ap3,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using old
  exact e.eqTrans (congrAp3 F (.eqRefl _) (fst_pair _ _) (snd_pair _ _))

def localBody (F : PR 3) (a C E L x t u A D : PTm n) : Fm PTm n :=
  le one D ⟶ inside a C E t ⟶ inside a C E u ⟶ distanceBounded (value t) (value u) A D ⟶
    independentRate (evaluatorName F) (evaluatorName F) (nameData t x) (nameData u x) (L*A) D
@[simp] theorem subst_localBody {l : ℕ} (σ : Fin n → PTm l) (F : PR 3) (a C E L x t u A D : PTm n) :
    (localBody F a C E L x t u A D).subst σ = localBody F (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E)
      (Syn.subst σ L) (Syn.subst σ x) (Syn.subst σ t) (Syn.subst σ u) (Syn.subst σ A) (Syn.subst σ D) := by simp [localBody]

def sampledModulus (F : PR 3) (a C E L x : PTm n) : Fm PTm n := .all (.all (.all (.all
  (localBody F (Syn.shift (Syn.shift (Syn.shift (Syn.shift a)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift C))))
    (Syn.shift (Syn.shift (Syn.shift (Syn.shift E)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift L))))
    (Syn.shift (Syn.shift (Syn.shift (Syn.shift x)))) (var 3) (var 2) (var 1) (var 0)))))
@[simp] theorem subst_sampledModulus {l : ℕ} (σ : Fin n → PTm l) (F : PR 3) (a C E L x : PTm n) :
    (sampledModulus F a C E L x).subst σ = sampledModulus F (Syn.subst σ a) (Syn.subst σ C)
      (Syn.subst σ E) (Syn.subst σ L) (Syn.subst σ x) := by simp [sampledModulus,Syn.subst_shift,Syn.shift_subst,Syn.up]

theorem sampled_modulus_at (F : PR 3) (a C E L x p q t u A D : PTm n)
    (h : Γ ⊢[PRAAx] sampledModulus F a C E L x) (hD : Γ ⊢[PRAAx] le one D)
    (ht : Γ ⊢[PRAAx] inside a C E t) (hu : Γ ⊢[PRAAx] inside a C E u)
    (hd : Γ ⊢[PRAAx] distanceBounded (value t) (value u) A D) : Γ ⊢[PRAAx]
    distanceBounded (ap3 F p t x) (ap3 F q u x) (rateNumerator (L*A) D p q) (rateDenominator D p q) := by
  have rule : Γ ⊢[PRAAx] localBody F a C E L x t u A D := by
    simpa only [sampledModulus,Fm.subst_all,subst_localBody,Foundations.BoundedFormulas.subst_up_shift',
      Syn.subst_var,up_three,up_two,Syn.up_one,Syn.up_zero,Syn.up_succ,Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift,Syn.shift_var] using
      (((h.allE t).allE u).allE A).allE D
  have rate := Prf.impE (Prf.impE (Prf.impE (Prf.impE rule hD) ht) hu) hd
  exact distance_congr (evaluator_at F p t x) (evaluator_at F q u x) (.eqRefl _) (.eqRefl _)
    (GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q rate)

theorem grid_inside (i N a C E : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hE : Γ ⊢[PRAAx] le one E)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] inside a C E (grid i N a C E) := by
  have hn := le_trans (positive_product _ _ ha hN) (le_add_right (a*N) (C*i))
  have hd := positive_product (Γ := Γ) _ _ hE hN
  have lower : Γ ⊢[PRAAx] le (a*(E*N)) (E*(a*N+C*i)) := le_of_eq_add (d := E*C*i) (by ipra_ring)
  have upper := add_le_add₂ (le_refl (Γ := Γ) (E*a*N)) (mul_le_mul_right (E*C) hi)
  have upper' : Γ ⊢[PRAAx] le (E*(a*N+C*i)) ((a+C)*(E*N)) := le_congr (by ipra_ring) (by ipra_ring) upper
  exact .andI (le_congr (.eqRefl _) (fst_pair _ _).eqSymm hn)
    (.andI (le_congr (.eqRefl _) (snd_pair _ _).eqSymm hd)
      (.andI (le_congr (congrMul (.eqRefl _) (snd_pair _ _)).eqSymm (congrMul (.eqRefl _) (fst_pair _ _)).eqSymm lower)
        (le_congr (congrMul (.eqRefl _) (fst_pair _ _)).eqSymm (congrMul (.eqRefl _) (snd_pair _ _)).eqSymm upper')))


theorem fraction_congr (a a' b b' : PTm n) (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') : Γ ⊢[PRAAx]
    ofGaussian (scale a oneCode) b ≐ ofGaussian (scale a' oneCode) b' := by
  ipra_congr (ofGaussian (scale (var 0) oneCode) (var 1) : PTm 2) with [ha, hb]

theorem value_grid (i N a C E : PTm n) : Γ ⊢[PRAAx]
    value (grid i N a C E) ≐ ofGaussian (scale (a*N+C*i) oneCode) (E*N) :=
  fraction_congr _ _ _ _ (fst_pair _ _) (snd_pair _ _)

theorem positive_as_successor (R : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    R ≐ succ (monus R one) := (eq_add_of_le hR).eqTrans (by ipra_ring)

theorem coarse_bound (i R N : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hi : Γ ⊢[PRAAx] lt i (R*N)) : Γ ⊢[PRAAx]
    lt (quo i R) N := by
  have qr := div_mod_at (x := i) (positive_as_successor R hR)
  refine .orE (lt_or_le (quo i R) N) Prf.hyp0 ?_
  have prod : (le N (quo i R)) :: Γ ⊢[PRAAx] le (N*R) (quo i R*R) := mul_le_mul_right R Prf.hyp0
  have upto : (le N (quo i R)) :: Γ ⊢[PRAAx] le (R*quo i R) i :=
    le_congr (.eqRefl _) qr.andE₁.wk.eqSymm (le_add_right _ _)
  have prod' : (le N (quo i R)) :: Γ ⊢[PRAAx] le (R*N) (R*quo i R) :=
    le_congr (mul_comm _ _) (mul_comm _ _) prod
  exact le_lt_absurd _ (le_trans prod' upto) hi.wk

theorem grid_native_difference (i R N a C E : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    GaussianRootAlgebra.equal
      (GaussianRootAlgebra.sub (scale (E*N) (scale (a*(R*N)+C*i) oneCode))
        (scale (E*(R*N)) (scale (a*N+C*quo i R) oneCode)))
      (scale (C*E*N*rem i R) oneCode) := by
  have qr := natEq (div_mod_at (x := i) (positive_as_successor R hR)).andE₁
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_scale,
      GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ipra_simps
  · linear_combination (𝔞(C)*𝔞(E)*𝔞(N))*qr
  · ring

/-- Original fine point and its actual quotient-index coarse point. -/
theorem grid_distance (i R N a C E : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hN : Γ ⊢[PRAAx] le one N) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    distanceBounded (value (grid i (R*N) a C E)) (value (grid (quo i R) N a C E)) C (E*N) := by
  let Q := (E*(R*N))*(E*N)
  have d1 := positive_product (Γ := Γ) E (R*N) hE (positive_product _ _ hR hN)
  have d2 := positive_product (Γ := Γ) E N hE hN
  have dQ := positive_product _ _ d1 d2
  have fine := GaussianRationalSyntheticDivision.rescale_to _ _ _ (E*N) Q
    (GaussianRationalHorner.ofGaussian_represents (scale (a*(R*N)+C*i) oneCode) (E*(R*N)) d1) (.eqRefl _)
  have coarse := GaussianRationalSyntheticDivision.rescale_to _ _ _ (E*(R*N)) Q
    (GaussianRationalHorner.ofGaussian_represents (scale (a*N+C*quo i R) oneCode) (E*N) d2) (by dsimp [Q]; ipra_ring)
  have ns : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq
      (GaussianRootAlgebra.sub (scale (E*N) (scale (a*(R*N)+C*i) oneCode))
        (scale (E*(R*N)) (scale (a*N+C*quo i R) oneCode))) ≐ (C*E*N*rem i R)*(C*E*N*rem i R) := (GaussianRootAlgebra.normSq_equal (grid_native_difference i R N a C E hR)).eqTrans
    ((ComplexLogarithmRemainder.normSq_scale _ _).eqTrans
      ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one).eqTrans (by ipra_ring)))
  have bound : Γ ⊢[PRAAx] le ((E*N*(E*N))*ComplexLogarithmRemainder.normSq
      (GaussianRootAlgebra.sub (scale (E*N) (scale (a*(R*N)+C*i) oneCode))
        (scale (E*(R*N)) (scale (a*N+C*quo i R) oneCode)))) ((C*C)*(Q*Q)) := by
    have sq := mul_le_mul_right (C*C*E*E*E*E*N*N*N*N)
      (sq_le_sq (le_of_lt (div_mod_at (x := i) (positive_as_successor R hR)).andE₂))
    exact le_congr ((congrMul (.eqRefl _) ns).eqTrans (by ipra_ring)).eqSymm (by dsimp [Q]; ipra_ring) sq
  have raw := (GaussianRationalMetric.bounded_difference_iff _ _ _ _ Q C (E*N) dQ d2 fine coarse).iffMpr bound
  exact distance_congr (value_grid i (R*N) a C E).eqSymm (value_grid (quo i R) N a C E).eqSymm (.eqRefl _) (.eqRefl _) raw


def sampleData (p N a C E x : PTm n) : PTm n := pairT p (pairT N (pairT a (pairT C (pairT E x))))
def field0 (d : PTm n) : PTm n := fstT d
def field1 (d : PTm n) : PTm n := fstT (sndT d)
def field2 (d : PTm n) : PTm n := fstT (sndT (sndT d))
def field3 (d : PTm n) : PTm n := fstT (sndT (sndT (sndT d)))
def field4 (d : PTm n) : PTm n := fstT (sndT (sndT (sndT (sndT d))))
def field5 (d : PTm n) : PTm n := sndT (sndT (sndT (sndT (sndT d))))
@[simp] theorem subst_sampleData {l : ℕ} (σ : Fin n → PTm l) (p N a C E x : PTm n) :
    Syn.subst σ (sampleData p N a C E x) = sampleData (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ a)
      (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ x) := by simp [sampleData]
@[simp] theorem subst_field0 {l : ℕ} (σ : Fin n → PTm l) (d : PTm n) : Syn.subst σ (field0 d) = field0 (Syn.subst σ d) := by simp [field0]
@[simp] theorem subst_field1 {l : ℕ} (σ : Fin n → PTm l) (d : PTm n) : Syn.subst σ (field1 d) = field1 (Syn.subst σ d) := by simp [field1]
@[simp] theorem subst_field2 {l : ℕ} (σ : Fin n → PTm l) (d : PTm n) : Syn.subst σ (field2 d) = field2 (Syn.subst σ d) := by simp [field2]
@[simp] theorem subst_field3 {l : ℕ} (σ : Fin n → PTm l) (d : PTm n) : Syn.subst σ (field3 d) = field3 (Syn.subst σ d) := by simp [field3]
@[simp] theorem subst_field4 {l : ℕ} (σ : Fin n → PTm l) (d : PTm n) : Syn.subst σ (field4 d) = field4 (Syn.subst σ d) := by simp [field4]
@[simp] theorem subst_field5 {l : ℕ} (σ : Fin n → PTm l) (d : PTm n) : Syn.subst σ (field5 d) = field5 (Syn.subst σ d) := by simp [field5]
theorem field0_at (p N a C E x : PTm n) : Γ ⊢[PRAAx] field0 (sampleData p N a C E x) ≐ p := fst_pair _ _
theorem field1_at (p N a C E x : PTm n) : Γ ⊢[PRAAx] field1 (sampleData p N a C E x) ≐ N :=
  (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
theorem field2_at (p N a C E x : PTm n) : Γ ⊢[PRAAx] field2 (sampleData p N a C E x) ≐ a :=
  (congrFst (congrSnd (snd_pair _ _))).eqTrans ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))

theorem field3_at (p N a C E x : PTm n) : Γ ⊢[PRAAx] field3 (sampleData p N a C E x) ≐ C :=
  (congrFst (congrSnd (congrSnd (snd_pair _ _)))).eqTrans
    ((congrFst (congrSnd (snd_pair _ _))).eqTrans ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)))
theorem field4_at (p N a C E x : PTm n) : Γ ⊢[PRAAx] field4 (sampleData p N a C E x) ≐ E :=
  (congrFst (congrSnd (congrSnd (congrSnd (snd_pair _ _))))).eqTrans
    ((congrFst (congrSnd (congrSnd (snd_pair _ _)))).eqTrans
      ((congrFst (congrSnd (snd_pair _ _))).eqTrans ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))))
theorem field5_at (p N a C E x : PTm n) : Γ ⊢[PRAAx] field5 (sampleData p N a C E x) ≐ x :=
  (congrSnd (congrSnd (congrSnd (congrSnd (snd_pair _ _))))).eqTrans
    ((congrSnd (congrSnd (congrSnd (snd_pair _ _)))).eqTrans
      ((congrSnd (congrSnd (snd_pair _ _))).eqTrans ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))))

def sampleBody (F : PR 3) : PTm 2 := ap3 F (field0 (var 1))
  (grid (var 0) (field1 (var 1)) (field2 (var 1)) (field3 (var 1)) (field4 (var 1))) (field5 (var 1))
@[simp] theorem sample_entry (F : PR 3) (i d : PTm n) : inst2 (sampleBody F) i d =
    ap3 F (field0 d) (grid i (field1 d) (field2 d) (field3 d) (field4 d)) (field5 d) := by simp [sampleBody,inst2]
theorem grid_congr (i i' N N' a a' C C' E E' : PTm n) (hi : Γ ⊢[PRAAx] i ≐ i')
    (hN : Γ ⊢[PRAAx] N ≐ N') (ha : Γ ⊢[PRAAx] a ≐ a') (hC : Γ ⊢[PRAAx] C ≐ C') (hE : Γ ⊢[PRAAx] E ≐ E') :
    Γ ⊢[PRAAx] grid i N a C E ≐ grid i' N' a' C' E' :=
  congrPairT (congrAdd (congrMul ha hN) (congrMul hC hi)) (congrMul hE hN)
theorem sample_body_at (F : PR 3) (i p N a C E x : PTm n) : Γ ⊢[PRAAx]
    inst2 (sampleBody F) i (sampleData p N a C E x) ≐ ap3 F p (grid i N a C E) x := by
  rw [sample_entry]
  exact congrAp3 F (field0_at _ _ _ _ _ _) (grid_congr _ _ _ _ _ _ _ _ _ _ (.eqRefl _)
    (field1_at _ _ _ _ _ _) (field2_at _ _ _ _ _ _) (field3_at _ _ _ _ _ _) (field4_at _ _ _ _ _ _)) (field5_at _ _ _ _ _ _)

def quadrature (F : PR 3) (p N a C E x : PTm n) : PTm n :=
  GaussianRationalRiemannRefinement.leftSum (sampleBody F) N (sampleData p N a C E x) C E
@[simp] theorem subst_quadrature {l : ℕ} (σ : Fin n → PTm l) (F : PR 3) (p N a C E x : PTm n) :
    Syn.subst σ (quadrature F p N a C E x) = quadrature F (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ a)
      (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ x) := by simp [quadrature]


theorem refinement_cell (F : PR 3) (i p q N R a C E L x : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N)
    (hR : Γ ⊢[PRAAx] le one R) (h : Γ ⊢[PRAAx] sampledModulus F a C E L x)
    (hi : Γ ⊢[PRAAx] lt i (R*N)) : Γ ⊢[PRAAx]
    distanceBounded (inst2 (sampleBody F) i (sampleData p (R*N) a C E x))
      (inst2 (sampleBody F) (quo i R) (sampleData q N a C E x))
      (rateNumerator (L*C) (E*N) p q) (rateDenominator (E*N) p q) := by
  have fine := grid_inside i (R*N) a C E ha hE (positive_product _ _ hR hN) (le_of_lt hi)
  have coarse := grid_inside (quo i R) N a C E ha hE hN (le_of_lt (coarse_bound i R N hR hi))
  exact distance_congr (sample_body_at F i p (R*N) a C E x).eqSymm
    (sample_body_at F (quo i R) q N a C E x).eqSymm (.eqRefl _) (.eqRefl _)
    (sampled_modulus_at F a C E L x p q _ _ C (E*N) h (positive_product _ _ hE hN) fine coarse
      (grid_distance i R N a C E hR hN hE))

theorem quadrature_refinement (F : PR 3) (p q N R a C E L x : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N)
    (hR : Γ ⊢[PRAAx] le one R) (h : Γ ⊢[PRAAx] sampledModulus F a C E L x) : Γ ⊢[PRAAx]
    distanceBounded (quadrature F p (R*N) a C E x) (quadrature F q N a C E x)
      (C*rateNumerator (L*C) (E*N) p q) (E*rateDenominator (E*N) p q) := by
  have as' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using ha.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using hE.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift R) := by simpa [Fm.shift,Syn.shift] using hR.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] sampledModulus F (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift L) (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have cells : Γ ⊢[PRAAx] GaussianRationalRiemannRefinement.cellDistances (sampleBody F) (sampleBody F) N R
      (sampleData p (R*N) a C E x) (sampleData q N a C E x)
      (rateNumerator (L*C) (E*N) p q) (rateDenominator (E*N) p q) := by
    refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_sampleData,PTm.subst_mul,GaussianNamedInverseRate.subst_rateNumerator,
      GaussianNamedInverseRate.subst_rateDenominator] using refinement_cell F (var 0) (Syn.shift p) (Syn.shift q)
        (Syn.shift N) (Syn.shift R) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift L) (Syn.shift x)
        as'.wk es.wk ns.wk rs.wk hs.wk Prf.hyp0
  have d1 := positive_product _ _ (positive_product _ _ hE hN) (positive_product _ _ (unit_positive p) (unit_positive q))
  exact GaussianRationalRiemannRefinement.refinement _ _ N R _ _ C E _ _ hN hR hE (le_congr (.eqRefl _) (by unfold rateDenominator; ipra_ring) d1) cells

def mesh (p L T : PTm n) : PTm n := unit (p+num 6)*(one+L*T*T)
def precision (p T : PTm n) : PTm n := p+T+num 6
def sample (F : PR 3) (p a C E L T x : PTm n) : PTm n := quadrature F (precision p T) (mesh p L T) a C E x
@[simp] theorem subst_mesh {l : ℕ} (σ : Fin n → PTm l) (p L T : PTm n) :
    Syn.subst σ (mesh p L T) = mesh (Syn.subst σ p) (Syn.subst σ L) (Syn.subst σ T) := by simp [mesh]
@[simp] theorem subst_precision {l : ℕ} (σ : Fin n → PTm l) (p T : PTm n) :
    Syn.subst σ (precision p T) = precision (Syn.subst σ p) (Syn.subst σ T) := by simp [precision]
@[simp] theorem subst_sample {l : ℕ} (σ : Fin n → PTm l) (F : PR 3) (p a C E L T x : PTm n) :
    Syn.subst σ (sample F p a C E L T x) = sample F (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ C)
      (Syn.subst σ E) (Syn.subst σ L) (Syn.subst σ T) (Syn.subst σ x) := by simp [sample]
theorem mesh_positive (p L T : PTm n) : Γ ⊢[PRAAx] le one (mesh p L T) :=
  positive_product _ _ (unit_positive _) (le_add_right one (L*T*T))
theorem mesh_refines (p q L T : PTm n) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    mesh q L T ≐ unit (monus q p)*mesh p L T := by
  have u : Γ ⊢[PRAAx] q+num 6 ≐ (p+num 6)+monus q p :=
    (congrAdd (eq_add_of_le hpq) (.eqRefl _)).eqTrans (by ipra_ring)
  have raw := (congrAp2 powF u (.eqRefl two)).eqTrans (pw_add two (p+num 6) (monus q p))
  exact (congrMul raw (.eqRefl (one+L*T*T))).eqTrans (by unfold mesh unit; ipra_ring)

theorem precision_unit (p T : PTm n) : Γ ⊢[PRAAx]
    unit (precision p T) ≐ unit (p+num 6)*unit T :=
  (congrAp2 powF (by unfold precision; ipra_ring) (.eqRefl two)).eqTrans (pw_add two (p+num 6) T)
theorem dyadic_monotone (p q : PTm n) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx] le (unit p) (unit q) := by
  have shifted : Γ ⊢[PRAAx] unit q ≐ unit p*unit (monus q p) :=
    (congrAp2 powF (eq_add_of_le hpq) (.eqRefl two)).eqTrans (pw_add two p (monus q p))
  exact le_congr (one_mul _ ) ((mul_comm _ _).eqTrans shifted.eqSymm) (mul_le_mul_right (unit p) (unit_positive (monus q p)))
theorem precision_lower (p T : PTm n) : Γ ⊢[PRAAx] le (unit (p+num 6)*T) (unit (precision p T)) := by
  have lower : Γ ⊢[PRAAx] le T (unit T) := le_trans (le_succ_self T) (RationalClosure.succ_le_two_pow T)
  exact le_congr (mul_comm _ _) ((mul_comm _ _).eqTrans (precision_unit p T).eqSymm)
    (mul_le_mul_right (unit (p+num 6)) lower)
theorem mesh_cost (p L T : PTm n) : Γ ⊢[PRAAx] le (unit (p+num 6)*L*T*T) (mesh p L T) :=
  le_of_eq_add (d := unit (p+num 6)) (by unfold mesh; ipra_ring)

/-- Three genuine finite error terms: mesh variation and two original
observation errors. -/
theorem quadrature_budget (C E L N U V K T : PTm n)
    (hC : Γ ⊢[PRAAx] le C (E*T)) (hN : Γ ⊢[PRAAx] le (K*L*T*T) N)
    (hU : Γ ⊢[PRAAx] le (K*T) U) (hV : Γ ⊢[PRAAx] le (K*T) V) : Γ ⊢[PRAAx]
    le (C*(L*C*U*V+E*N*(U+V))*K) ((num 3)*(E*(E*N*U*V))) := by
  have square := sq_le_sq hC
  have first : Γ ⊢[PRAAx] le (C*C*L*K*U*V) (E*E*N*U*V) := by
    ipra_le (𝔞(L)*𝔞(K)*𝔞(U)*𝔞(V))*sl square + (𝔞(E)*𝔞(E)*𝔞(U)*𝔞(V))*sl hN
  have second : Γ ⊢[PRAAx] le (C*E*N*U*K) (E*E*N*U*V) := by
    ipra_le (𝔞(E)*𝔞(N)*𝔞(U)*𝔞(K))*sl hC + (𝔞(E)*𝔞(E)*𝔞(N)*𝔞(U))*sl hV
  have third : Γ ⊢[PRAAx] le (C*E*N*V*K) (E*E*N*U*V) := by
    ipra_le (𝔞(E)*𝔞(N)*𝔞(V)*𝔞(K))*sl hC + (𝔞(E)*𝔞(E)*𝔞(N)*𝔞(V))*sl hU
  exact le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ (add_le_add₂ first second) third)


theorem quadrature_index_congr (F : PR 3) (p N M a C E x : PTm n) (hN : Γ ⊢[PRAAx] N ≐ M) : Γ ⊢[PRAAx]
    quadrature F p N a C E x ≐ quadrature F p M a C E x := by
  ipra_congr (quadrature F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) with
    [.eqRefl p, hN, .eqRefl a, .eqRefl C, .eqRefl E, .eqRefl x]

theorem ordered_sample_distance (F : PR 3) (p q a C E L T x : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hE : Γ ⊢[PRAAx] le one E) (hC : Γ ⊢[PRAAx] le C (E*T))
    (h : Γ ⊢[PRAAx] sampledModulus F a C E L x) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    distanceBounded (sample F q a C E L T x) (sample F p a C E L T x) (num 3) (unit (p+num 6)) := by
  let N := mesh p L T
  let R := unit (monus q p)
  let U := unit (precision q T)
  let V := unit (precision p T)
  let K := unit (p+num 6)
  have hN := mesh_positive (Γ := Γ) p L T
  have hR := unit_positive (Γ := Γ) (monus q p)
  have raw := quadrature_refinement F (precision q T) (precision p T) N R a C E L x ha hE hN hR h
  have actual : Γ ⊢[PRAAx] distanceBounded (sample F q a C E L T x) (sample F p a C E L T x)
      (C*rateNumerator (L*C) (E*N) (precision q T) (precision p T))
      (E*rateDenominator (E*N) (precision q T) (precision p T)) :=
    distance_congr (quadrature_index_congr F _ _ _ _ _ _ _ (mesh_refines p q L T hpq)).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) raw
  have grow : Γ ⊢[PRAAx] le (precision p T) (precision q T) := by
    exact le_congr (by unfold precision; ipra_ring) (by unfold precision; ipra_ring) (add_le_add_right (T+num 6) hpq)
  have ub : Γ ⊢[PRAAx] le (K*T) U := le_trans (precision_lower p T) (dyadic_monotone _ _ grow)
  have budget := quadrature_budget C E L N U V K T hC (mesh_cost p L T) ub (precision_lower p T)
  have den := positive_product _ _ hE (positive_product _ _ (positive_product _ _ hE hN)
    (positive_product _ _ (unit_positive (precision q T)) (unit_positive (precision p T))))
  apply distance_radius_mono _ _ _ _ (num 3) K
    (le_congr (.eqRefl _) (by unfold rateDenominator; ipra_ring) den) (unit_positive _) _ actual
  exact budget

theorem dyadic_six_lower (p : PTm n) : Γ ⊢[PRAAx] le ((num 3)*unit p) (unit (p+num 6)) := by
  have six : Γ ⊢[PRAAx] le (num 3 : PTm n) (unit (num 6)) :=
    le_trans (le_of_eq_add (d := num 4) (by ipra_ring)) (RationalClosure.succ_le_two_pow (num 6))
  exact le_congr (.eqRefl _) ((mul_comm _ _).eqTrans (pw_add two p (num 6)).eqSymm) (mul_le_mul_right (unit p) six)


theorem ordered_sample_regularity (F : PR 3) (p q a C E L T x : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hE : Γ ⊢[PRAAx] le one E) (hC : Γ ⊢[PRAAx] le C (E*T))
    (h : Γ ⊢[PRAAx] sampledModulus F a C E L x) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    distanceBounded (sample F q a C E L T x) (sample F p a C E L T x) (unit p+unit q) (unit p*unit q) := by
  have cleared : Γ ⊢[PRAAx] le ((num 3)*(unit p*unit q)) ((unit p+unit q)*unit (p+num 6)) := by
    have first := mul_le_mul_right (unit q) (dyadic_six_lower (Γ := Γ) p)
    have large : Γ ⊢[PRAAx] le (unit (p+num 6)*unit q) ((unit p+unit q)*unit (p+num 6)) :=
      le_of_eq_add (d := unit p*unit (p+num 6)) (by ipra_ring)
    exact le_trans (le_congr (by ipra_ring) (.eqRefl _) first) large
  exact distance_radius_mono _ _ _ _ _ _ (unit_positive _) (positive_product _ _ (unit_positive _) (unit_positive _)) cleared
    (ordered_sample_distance F p q a C E L T x ha hE hC h hpq)

theorem sample_regularity (F : PR 3) (p q a C E L T x : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hE : Γ ⊢[PRAAx] le one E) (hC : Γ ⊢[PRAAx] le C (E*T))
    (h : Γ ⊢[PRAAx] sampledModulus F a C E L x) : Γ ⊢[PRAAx]
    distanceBounded (sample F p a C E L T x) (sample F q a C E L T x) (unit p+unit q) (unit p*unit q) := by
  refine .orE (le_total p q) ?_ ?_
  · exact GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive _) (unit_positive _))
      (ordered_sample_regularity F p q a C E L T x ha.wk hE.wk hC.wk h.wk Prf.hyp0)
  · exact distance_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _)
      (ordered_sample_regularity F q p a C E L T x ha.wk hE.wk hC.wk h.wk Prf.hyp0)


def data (a C E L T x : PTm n) : PTm n := sampleData a C E L T x
def nameF (F : PR 3) : PR 2 := PTm.toPR
  (sample F (var 0) (field0 (var 1)) (field1 (var 1)) (field2 (var 1)) (field3 (var 1)) (field4 (var 1)) (field5 (var 1)) : PTm 2)
def input (F : PR 3) (a C E L T x : PTm n) : Fm PTm n :=
  le one a ⋏ (le one E ⋏ (le C (E*T) ⋏ sampledModulus F a C E L x))
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (a C E L T x : PTm n) :
    Syn.subst σ (data a C E L T x) = data (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E)
      (Syn.subst σ L) (Syn.subst σ T) (Syn.subst σ x) := by simp [data]
@[simp] theorem subst_input {l : ℕ} (σ : Fin n → PTm l) (F : PR 3) (a C E L T x : PTm n) :
    (input F a C E L T x).subst σ = input F (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E)
      (Syn.subst σ L) (Syn.subst σ T) (Syn.subst σ x) := by simp [input]

theorem name_at (F : PR 3) (p a C E L T x : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF F) p (data a C E L T x) ≐ sample F p a C E L T x := by
  have old := toPR_eq (Γ := Γ)
    (sample F (var 0) (field0 (var 1)) (field1 (var 1)) (field2 (var 1)) (field3 (var 1)) (field4 (var 1)) (field5 (var 1)) : PTm 2)
    ![p,data a C E L T x]
  have e : Γ ⊢[PRAAx] ap2 (nameF F) p (data a C E L T x) ≐ sample F p
      (field0 (data a C E L T x)) (field1 (data a C E L T x)) (field2 (data a C E L T x))
      (field3 (data a C E L T x)) (field4 (data a C E L T x)) (field5 (data a C E L T x)) := by
    simpa only [nameF,ap2,subst_sample,subst_field0,subst_field1,subst_field2,subst_field3,subst_field4,subst_field5,
      Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using old
  apply e.eqTrans
  ipra_congr (sample F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) with
    [.eqRefl p, (show _ ⊢[PRAAx] field0 (data a C E L T x) ≐ a from field0_at _ _ _ _ _ _),
      (show _ ⊢[PRAAx] field1 (data a C E L T x) ≐ C from field1_at _ _ _ _ _ _),
      (show _ ⊢[PRAAx] field2 (data a C E L T x) ≐ E from field2_at _ _ _ _ _ _),
      (show _ ⊢[PRAAx] field3 (data a C E L T x) ≐ L from field3_at _ _ _ _ _ _),
      (show _ ⊢[PRAAx] field4 (data a C E L T x) ≐ T from field4_at _ _ _ _ _ _),
      (show _ ⊢[PRAAx] field5 (data a C E L T x) ≐ x from field5_at _ _ _ _ _ _)]

theorem sample_canonical (F : PR 3) (p a C E L T x : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (sample F p a C E L T x) := GaussianRationalHorner.qmul_canonical _ _
theorem name_canonical (F : PR 3) (p a C E L T x : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (ap2 (nameF F) p (data a C E L T x)) :=
  GaussianRationalHorner.canonical_congr (name_at F p a C E L T x) (sample_canonical F p a C E L T x)

theorem name_regular (F : PR 3) (a C E L T x : PTm n) (h : Γ ⊢[PRAAx] input F a C E L T x) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN (nameF F) (data a C E L T x) := by
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] input F (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift C))
      (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift L)) (Syn.shift (Syn.shift T)) (Syn.shift (Syn.shift x)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [GaussianEuclideanDistanceName.pointCN,Syn.shift,subst_data,GaussianEuclideanPointDistance.unit,unit]
    using distance_congr (name_at F (var 1) _ _ _ _ _ _).eqSymm (name_at F (var 0) _ _ _ _ _ _).eqSymm
      (.eqRefl _) (.eqRefl _)
      (sample_regularity F (var 1) (var 0) _ _ _ _ _ _ hs.andE₁ hs.andE₂.andE₁ hs.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₂)

def output (F : PR 3) (p a C E L T x : PTm n) : PTm n :=
  pairT (ap2 (nameF F) p (data a C E L T x)) (pairT (mesh p L T) (precision p T))
def outputF (F : PR 3) : PR 7 := PTm.toPR (output F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def run (F : PR 3) (p a C E L T x : PTm n) : PTm n := PTm.app (outputF F) ![p,a,C,E,L,T,x]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (F : PR 3) (p a C E L T x : PTm n) :
    Syn.subst σ (output F p a C E L T x) = output F (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ C)
      (Syn.subst σ E) (Syn.subst σ L) (Syn.subst σ T) (Syn.subst σ x) := by simp [output]
theorem program_at (F : PR 3) (p a C E L T x : PTm n) : Γ ⊢[PRAAx] run F p a C E L T x ≐ output F p a C E L T x := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![p,a,C,E,L,T,x]
theorem returned_sample (F : PR 3) (p a C E L T x : PTm n) : Γ ⊢[PRAAx]
    fstT (run F p a C E L T x) ≐ sample F p a C E L T x :=
  (congrFst (program_at F p a C E L T x)).eqTrans ((fst_pair _ _).eqTrans (name_at F p a C E L T x))
theorem returned_mesh (F : PR 3) (p a C E L T x : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run F p a C E L T x)) ≐ mesh p L T :=
  ((congrFst (congrSnd (program_at F p a C E L T x))).eqTrans (congrFst (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_precision (F : PR 3) (p a C E L T x : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run F p a C E L T x)) ≐ precision p T :=
  ((congrSnd (congrSnd (program_at F p a C E L T x))).eqTrans (congrSnd (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem actual_positive_affine_grid_inside_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 2) ⋏ (le one (var 4) ⋏ (le one (var 1) ⋏ le (var 0) (var 1)))) ⟶
      inside (var 2) (var 3) (var 4) (grid (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (grid_inside _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))
theorem actual_fine_quotient_grid_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 1) ⋏ (le one (var 2) ⋏ le one (var 5))) ⟶
      distanceBounded (value (grid (var 0) (var 1*var 2) (var 3) (var 4) (var 5)))
        (value (grid (quo (var 0) (var 1)) (var 2) (var 3) (var 4) (var 5))) (var 4) (var 5*var 2)) :=
  closeUniv 6 (.impI (grid_distance _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))
theorem actual_dyadic_compact_quadrature_regular_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input F (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶ distanceBounded
      (sample F (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
      (sample F (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
      (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 8 (.impI (sample_regularity F _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))
theorem actual_compact_quadrature_name_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      GaussianEuclideanDistanceName.pointCN (nameF F) (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (name_regular F _ _ _ _ _ _ Prf.hyp0))
theorem actual_compact_quadrature_sample_canonical_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (GaussianRationalHorner.canonical (sample F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))) :=
  closeUniv 7 (sample_canonical F _ _ _ _ _ _ _)
theorem actual_compact_quadrature_program_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (run F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐ output F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (program_at F _ _ _ _ _ _ _)
theorem actual_compact_quadrature_returned_sample_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (fstT (run F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) ≐
      quadrature F (precision (var 0) (var 5)) (mesh (var 0) (var 4) (var 5)) (var 1) (var 2) (var 3) (var 6)) :=
  closeUniv 7 (returned_sample F _ _ _ _ _ _ _)
theorem actual_compact_quadrature_returned_schedules_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (fstT (sndT (run F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))) ≐ mesh (var 0) (var 4) (var 5) ⋏
     sndT (sndT (run F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))) ≐ precision (var 0) (var 5)) :=
  closeUniv 7 (.andI (returned_mesh F _ _ _ _ _ _ _) (returned_precision F _ _ _ _ _ _ _))

end LeanProofs.IPRA.Analysis.GaussianCompactRiemannName
