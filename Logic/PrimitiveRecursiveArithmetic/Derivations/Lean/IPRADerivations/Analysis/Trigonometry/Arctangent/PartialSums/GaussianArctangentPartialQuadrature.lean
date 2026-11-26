import IPRADerivations.Analysis.Trigonometry.Arctangent.PartialSums.GaussianArctangentExponentialPrefix
import IPRADerivations.Analysis.Integration.GaussianRationalRiemannRefinement

/-!
# Regularity of the native partial arctangent quadrature

The interval ending at A/B uses exactly A*N of the B*N original cells.
Within a refined block the sample at its first fine cell, counted once
for each fine cell, gives the coarse increment exactly. Comparing
actual fine cells with those first cells bounds mesh refinement by 4/N.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentPartialQuadrature

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (scale oneCode normSq normSq_eval eval_re_code eval_im_code)
open GaussianArctangentCayleyValues (imaginaryCode denominator denominator_positive)
open GaussianArctangentCayleyStep (increment incrementCode)
open GaussianArctangentExponentialPrefix (prefixValue source)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalFiniteSum (sum sum_index_congr multiplyBody multiply_body_at sum_multiply termsEqual)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents qmul qmul_canonical qmul_represents
  positive_product canonical_unique represents_congr represents_rescale)
open GaussianRationalMetric (bounded distanceBounded bounded_difference_iff)
open GaussianRationalNaturalScale (naturalPoint natural_point_represents)
open GaussianRationalRiemannRefinement (cellDistances fine_coarse_sum)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRootAlgebra (equal equal_of_values equal_refl re_sub im_sub re_scale im_scale re_mul im_mul re_one im_one)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

@[simp] theorem subst_increment {m : ℕ} (σ : Fin n → PTm m) (M j : PTm n) :
    Syn.subst σ (increment M j) = increment (Syn.subst σ M) (Syn.subst σ j) := by
  simp [increment,incrementCode,denominator]

def rowBody : PTm 2 := increment (var 1) (var 0)
def alignedBody : PTm 2 := increment (fstT (var 1)*sndT (var 1)) (fstT (var 1)*var 0)

theorem row_at (M i : PTm n) : inst2 rowBody i M = increment M i := by
  simp [rowBody,inst2]

theorem aligned_at (R M i : PTm n) : Γ ⊢[PRAAx] inst2 alignedBody i (pairT R M) ≐ increment (R*M) (R*i) := by
  simpa only [alignedBody,inst2,subst_increment,PTm.subst_mul,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] using
    (Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (increment (var 0*var 1) (var 0*var 2) : PTm 3)
      (σ := ![fstT (pairT R M),sndT (pairT R M),i]) (σ' := ![R,M,i])
      (fun k => by fin_cases k; exact fst_pair _ _; exact snd_pair _ _; exact .eqRefl _))

theorem aligned_scale (R M j : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] qmul (naturalPoint R) (increment (R*M) (R*j)) ≐ increment M j := by
  let d := denominator M j
  let t := R*R
  let e := denominator (R*M) (R*j)
  have hd := denominator_positive M j hM
  have he := denominator_positive (R*M) (R*j) (positive_product _ _ hR hM)
  have ht := positive_product R R hR hR
  have hD := positive_product d t hd ht
  have prod := qmul_represents (naturalPoint R) (increment (R*M) (R*j)) (scale R oneCode)
    (incrementCode (R*M)) one e (le_refl one) he (natural_point_represents R) (ofGaussian_represents _ _ he)
  have target := represents_rescale (increment M j) (incrementCode M) d t (ofGaussian_represents _ _ hd)
  apply canonical_unique _ _ _ (d*t) (qmul_canonical _ _) (ofGaussian_canonical _ _ hd) hD (hrv := target)
  apply represents_congr (.eqRefl _) ?_ (by unfold d t e denominator; ipra_ring) prod
  apply equal_of_values <;>
    simp only [t,re_mul,im_mul,re_scale,im_scale,re_one,im_one,incrementCode,eval_re_code,eval_im_code,ZT.toZ_ofNat] <;>
    ipra_simps <;> ring

theorem aligned_sum (R M k : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] qmul (naturalPoint R) (sum alignedBody k (pairT R M)) ≐ sum rowBody k M := by
  refine (sum_multiply alignedBody (naturalPoint R) k (pairT R M)).eqSymm.eqTrans ?_
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  let r := Syn.shift R
  let m := Syn.shift M
  let i : PTm (n+1) := var 0
  have hR' : Γ.map Fm.shift ⊢[PRAAx] le one r := by simpa [Fm.shift,Syn.shift,r] using hR.shift
  have hM' : Γ.map Fm.shift ⊢[PRAAx] le one m := by simpa [Fm.shift,Syn.shift,m] using hM.shift
  let Δ := lt i (Syn.shift k) :: Γ.map Fm.shift
  have read := multiply_body_at (Γ := Δ) alignedBody (naturalPoint r) i (pairT r m)
  have point := (GaussianRationalSyntheticDivision.qmul_congr (Γ := Δ) (.eqRefl (naturalPoint r)) (aligned_at r m i)).eqTrans
    (aligned_scale r m i hR'.wk hM'.wk)
  simpa only [termsEqual,Syn.shift,subst_pairT,GaussianRationalNaturalScale.subst_naturalPoint,row_at,r,m,i,Δ] using
    read.eqTrans point

private def prefixLaw (j M L : PTm n) : Fm PTm n :=
  le j M ⟶ prefixValue j M L ≐ sum rowBody j M

@[simp] private theorem subst_prefixLaw {m : ℕ} (σ : Fin n → PTm m) (j M L : PTm n) :
    (prefixLaw j M L).subst σ = prefixLaw (Syn.subst σ j) (Syn.subst σ M) (Syn.subst σ L) := by
  simp [prefixLaw]

theorem prefix_as_sum (j M L : PTm n) (h : Γ ⊢[PRAAx] source M L) (hj : Γ ⊢[PRAAx] le j M) :
    Γ ⊢[PRAAx] prefixValue j M L ≐ sum rowBody j M := by
  have all : Γ ⊢[PRAAx] .all (prefixLaw (var 0) (Syn.shift M) (Syn.shift L)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI ((GaussianArctangentExponentialPrefix.prefix_zero M L).eqTrans (GaussianRationalFiniteSum.sum_zero rowBody M).eqSymm)
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let m := Syn.shift M
      let l := Syn.shift L
      let i : PTm (n+1) := var 0
      have hs : Γ.map Fm.shift ⊢[PRAAx] source m l := by
        simpa only [Fm.shift,GaussianArctangentExponentialPrefix.subst_source,Syn.shift,m,l] using h.shift
      have hi : (le (succ i) m :: prefixLaw i m l :: Γ.map Fm.shift) ⊢[PRAAx] lt i m := Prf.hyp0
      have old : (le (succ i) m :: prefixLaw i m l :: Γ.map Fm.shift) ⊢[PRAAx] prefixValue i m l ≐ sum rowBody i m :=
        .impE Prf.hyp1 (le_of_lt hi)
      have next := GaussianArctangentExponentialPrefix.prefix_succ i m l hs.wk.wk hi
      have append := GaussianRationalFiniteSum.sum_succ (Γ := le (succ i) m :: prefixLaw i m l :: Γ.map Fm.shift) rowBody i m
      rw [row_at] at append
      exact next.eqTrans ((qadd_congr old (.eqRefl _)).eqTrans append.eqSymm)
  have step : Γ ⊢[PRAAx] prefixLaw j M L := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE step hj

private theorem division_at (i R : PTm n) (hR : Γ ⊢[PRAAx] le one R) :
    Γ ⊢[PRAAx] (i ≐ R*quo i R+rem i R) ⋏ le (rem i R) R := by
  have he := RationalIntegerNormalization.positive_form hR
  have div := div_mod (Γ := Γ) i (pred R)
  have q := congrAp2 quoF (.eqRefl i) he
  have r := congrAp2 remF (.eqRefl i) he
  exact .andI (div.andE₁.eqTrans (congrAdd (congrMul he.eqSymm q.eqSymm) r.eqSymm))
    (le_congr r.eqSymm he.eqSymm (le_of_lt div.andE₂))

/-- A fine row and the first row of its coarse block have identical
denominator geometry, with first indices separated by less than R. -/
theorem cell_error (R M i : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hM : Γ ⊢[PRAAx] le one M) (hi : Γ ⊢[PRAAx] le i (R*M)) :
    Γ ⊢[PRAAx] distanceBounded (increment (R*M) i) (increment (R*M) (R*quo i R))
      (num 4) (R*(M*M)) := by
  let F := R*M
  let k := R*quo i R
  let r := rem i R
  let D := R*(M*M)
  let d := denominator F i
  let e := denominator F k
  let a := scale e (incrementCode F)
  let b := scale d (incrementCode F)
  let T := two*F*(r*(i+k))
  have hF := positive_product R M hR hM
  have hD := positive_product R (M*M) hR (positive_product M M hM hM)
  have hd := denominator_positive F i hF
  have he := denominator_positive F k hF
  have hde := positive_product d e hd he
  have div := division_at i R hR
  have hk : Γ ⊢[PRAAx] le k i := le_congr (.eqRefl k) div.andE₁.eqSymm (le_add_right k r)
  have htotal : Γ ⊢[PRAAx] le (i+k) (F+F) := add_le_add₂ hi (le_trans hk hi)
  have hrow : Γ ⊢[PRAAx] le T (two*F*(R*(F+F))) :=
    le_mul_mono (le_refl _) (le_mul_mono div.andE₂ htotal)
  have paid : Γ ⊢[PRAAx] le (D*T) (num 4*((F*F)*(F*F))) :=
    le_congr (.eqRefl _) (by dsimp only [D,F]; ipra_ring) (le_mul_mono (le_refl D) hrow)
  have den_order : Γ ⊢[PRAAx] le ((F*F)*(F*F)) (d*e) :=
    le_mul_mono (le_add_right _ _) (le_add_right _ _)
  have clear : Γ ⊢[PRAAx] le (D*T) (num 4*(d*e)) :=
    le_trans paid (le_mul_mono (le_refl _) den_order)
  have exact_norm : Γ ⊢[PRAAx] normSq (GaussianRootAlgebra.sub a b) ≐ T*T := by
    have decomp : Γ ⊢[PRAAx] i ≐ k+r := div.andE₁
    have eq := natEq decomp
    apply deriveNat
    rw [normSq_eval]
    simp only [a,b,T,d,e,denominator,re_sub,im_sub,re_scale,im_scale,incrementCode,
      eval_re_code,eval_im_code,ZT.toZ_ofNat]
    ipra_simps
    rw [eq]
    ring
  have ra := represents_rescale (increment F i) (incrementCode F) d e (ofGaussian_represents _ _ hd)
  have rb := represents_congr (.eqRefl _) (equal_refl _) (mul_comm e d)
    (represents_rescale (increment F k) (incrementCode F) e d (ofGaussian_represents _ _ he))
  apply (bounded_difference_iff _ _ a b (d*e) (num 4) D hde hD ra rb).iffMpr
  exact le_congr ((congrMul (.eqRefl _) exact_norm).eqTrans (by ipra_ring)).eqSymm
    (by ipra_ring) (le_mul_mono clear clear)

def clearing (M : PTm n) : PTm n := two*(M*M)
def observation (A B N : PTm n) : PTm n := prefixValue (A*N) (B*N) (clearing (B*N))

@[simp] theorem subst_clearing {m : ℕ} (σ : Fin n → PTm m) (M : PTm n) :
    Syn.subst σ (clearing M) = clearing (Syn.subst σ M) := by simp [clearing]
@[simp] theorem subst_observation {m : ℕ} (σ : Fin n → PTm m) (A B N : PTm n) :
    Syn.subst σ (observation A B N) = observation (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [observation]

theorem observation_source (B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] source (B*N) (clearing (B*N)) :=
  .andI (positive_product B N hB hN) (le_refl _)

theorem observation_bound (A B N : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] bounded (observation A B N) two one :=
  GaussianArctangentExponentialPrefix.prefix_bound _ _ _ (observation_source B N hB hN)
    (le_mul_mono hA (le_refl N))

theorem refinement_cells (R A B N : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hM : Γ ⊢[PRAAx] le one (B*N)) (hA : Γ ⊢[PRAAx] le A B) :
    Γ ⊢[PRAAx] cellDistances rowBody alignedBody (A*N) R (R*(B*N)) (pairT R (B*N)) (num 4) (R*((B*N)*(B*N))) := by
  refine .allI (.impI ?_)
  let r := Syn.shift R
  let a := Syn.shift A
  let b := Syn.shift B
  let m := Syn.shift N
  let i : PTm (n+1) := var 0
  let Δ := lt i (r*(a*m)) :: Γ.map Fm.shift
  have hr : Γ.map Fm.shift ⊢[PRAAx] le one r := by simpa [Fm.shift,Syn.shift,r] using hR.shift
  have hb : Γ.map Fm.shift ⊢[PRAAx] le one (b*m) := by simpa [Fm.shift,Syn.shift,b,m] using hM.shift
  have inRange : Γ.map Fm.shift ⊢[PRAAx] le a b := by simpa [Fm.shift,Syn.shift,a,b] using hA.shift
  have hi : Δ ⊢[PRAAx] le i (r*(b*m)) :=
    le_trans (le_of_lt Prf.hyp0) (le_mul_mono (le_refl _) (le_mul_mono inRange.wk (le_refl _)))
  have d := cell_error r (b*m) i hr.wk hb.wk hi
  simpa only [cellDistances,Syn.shift,PTm.subst_num,PTm.subst_mul,subst_pairT,row_at,r,a,b,m,i,Δ] using
    distance_congr (.eqRefl _) (aligned_at r (b*m) (quo i r)).eqSymm (.eqRefl _) (.eqRefl _) d

theorem physical_refinement (A B N R : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B)
    (hN : Γ ⊢[PRAAx] le one N) (hR : Γ ⊢[PRAAx] le one R) :
    Γ ⊢[PRAAx] distanceBounded (observation A B (R*N)) (observation A B N) (num 4) (B*N) := by
  let M := B*N
  let K := A*N
  let E := R*(M*M)
  have hM := positive_product B N hB hN
  have hF := positive_product R M hR hM
  have order : Γ ⊢[PRAAx] le K M := le_mul_mono hA (le_refl N)
  have hE := positive_product _ _ hR (positive_product _ _ hM hM)
  have sums := fine_coarse_sum rowBody alignedBody K R (R*M) (pairT R M) (num 4) E hR hE
    (refinement_cells R A B N hR hM hA)
  have coarse := (aligned_sum R M K hR hM).eqTrans
    (prefix_as_sum K M (clearing M) (.andI hM (le_refl _)) order).eqSymm
  have hs : Γ ⊢[PRAAx] le one (B*(R*N)) := le_congr (.eqRefl _) (by dsimp only [M]; ipra_ring) hF
  have fine : Γ ⊢[PRAAx] sum rowBody (R*K) (R*M) ≐ observation A B (R*N) :=
    (sum_index_congr rowBody (by dsimp only [K]; ipra_ring)
    (by dsimp only [M]; ipra_ring)).eqTrans
      (prefix_as_sum (A*(R*N)) (B*(R*N)) (clearing (B*(R*N)))
        (.andI hs (le_refl _)) (le_mul_mono hA (le_refl _))).eqSymm
  have rate : Γ ⊢[PRAAx] le (((R*K)*num 4)*M) (num 4*E) :=
    le_congr (by ipra_ring) (by dsimp only [E]; ipra_ring)
      (le_mul_mono (le_refl (num 4*R)) (le_mul_mono order (le_refl M)))
  exact distance_radius_mono _ _ _ _ _ _ hE hM rate
    (distance_congr fine coarse (.eqRefl _) (.eqRefl _) sums)

theorem finite_refinement (A B N R : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B)
    (hN : Γ ⊢[PRAAx] le one N) (hR : Γ ⊢[PRAAx] le one R) :
    Γ ⊢[PRAAx] distanceBounded (observation A B (R*N)) (observation A B N) (num 4) N := by
  have hnM := le_congr (one_mul N) (.eqRefl _) (le_mul_mono hB (le_refl N))
  exact distance_radius_mono _ _ _ _ _ _ (positive_product B N hB hN) hN
    (le_mul_mono (le_refl (num 4)) hnM) (physical_refinement A B N R hB hA hN hR)

theorem finite_comparison (A B N K : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B)
    (hN : Γ ⊢[PRAAx] le one N) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] distanceBounded (observation A B N) (observation A B K)
      (num 4*K+num 4*N) (N*K) := by
  have eq : Γ ⊢[PRAAx] observation A B (N*K) ≐ observation A B (K*N) := by
    simpa only [subst_observation,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] using
      (Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (observation (var 0) (var 1) (var 2) : PTm 3)
        (σ := ![A,B,N*K]) (σ' := ![A,B,K*N])
        (fun i => by fin_cases i; exact .eqRefl _; exact .eqRefl _; exact mul_comm _ _))
  exact GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hN hK
    (distance_symmetric _ _ _ _ hN (finite_refinement A B N K hB hA hN hK))
    (distance_congr eq (.eqRefl _) (.eqRefl _) (.eqRefl _) (finite_refinement A B K N hB hA hK hN))

def mesh (p : PTm n) : PTm n := num 4*unit p
def sample (p A B : PTm n) : PTm n := observation A B (mesh p)
def data (A B : PTm n) : PTm n := pairT A B
def nameTerm (p x : PTm n) : PTm n := sample p (fstT x) (sndT x)
def nameF : PR 2 := PTm.toPR (nameTerm (var 0) (var 1) : PTm 2)

@[simp] theorem subst_mesh {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (mesh p) = mesh (Syn.subst σ p) := by simp [mesh]
@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p A B : PTm n) :
    Syn.subst σ (sample p A B) = sample (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ B) := by simp [sample]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (A B : PTm n) :
    Syn.subst σ (data A B) = data (Syn.subst σ A) (Syn.subst σ B) := by simp [data]
@[simp] theorem subst_nameTerm {m : ℕ} (σ : Fin n → PTm m) (p x : PTm n) :
    Syn.subst σ (nameTerm p x) = nameTerm (Syn.subst σ p) (Syn.subst σ x) := by simp [nameTerm]

theorem four_positive : Γ ⊢[PRAAx] le one (num 4) :=
  le_of_eq_add (d := num 3) (by ipra_ring)

theorem mesh_positive (p : PTm n) : Γ ⊢[PRAAx] le one (mesh p) :=
  positive_product _ _ four_positive (unit_positive p)

theorem sample_at (p A B : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data A B) ≐ sample p A B := by
  have run : Γ ⊢[PRAAx] ap2 nameF p (data A B) ≐ nameTerm p (data A B) := by
    simpa [nameF,ap2] using toPR_eq (Γ := Γ) (nameTerm (var 0) (var 1) : PTm 2) ![p,data A B]
  refine run.eqTrans ?_
  simpa only [nameTerm,subst_sample,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons,data] using
    (Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (sample (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![p,fstT (pairT A B),sndT (pairT A B)]) (σ' := ![p,A,B])
      (fun i => by fin_cases i; exact .eqRefl _; exact fst_pair _ _; exact snd_pair _ _))

theorem sample_regularity (p q A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B) :
    Γ ⊢[PRAAx] distanceBounded (sample p A B) (sample q A B) (unit p+unit q) (unit p*unit q) := by
  have hp := mesh_positive (Γ := Γ) p
  have hq := mesh_positive (Γ := Γ) q
  have bound := finite_comparison A B (mesh p) (mesh q) hB hA hp hq
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp hq)
    (positive_product _ _ (unit_positive p) (unit_positive q))
    (le_of_eq_add (d := zero) (by unfold mesh; ipra_ring)) bound

theorem name_regular (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B) :
    Γ ⊢[PRAAx] pointCN nameF (data A B) := by
  let a := Syn.shift (Syn.shift A)
  let b := Syn.shift (Syn.shift B)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have ha : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le a b := by
    simpa [Fm.shift,Syn.shift,a,b] using hA.shift.shift
  have hb : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one b := by
    simpa [Fm.shift,Syn.shift,b] using hB.shift.shift
  refine .allI (.allI ?_)
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,unit,Syn.shift,subst_data,a,b,p,q] using
    distance_congr (sample_at p a b).eqSymm (sample_at q a b).eqSymm
      (.eqRefl _) (.eqRefl _) (sample_regularity p q a b hb ha)

theorem actual_partial_arctangent_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap2 nameF (var 0) (data (var 1) (var 2)) ≐ sample (var 0) (var 1) (var 2)) :=
  closeUniv 3 (sample_at _ _ _)

theorem actual_partial_arctangent_refinement_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ le (var 0) (var 1) ⟶ le one (var 2) ⟶ le one (var 3) ⟶
      distanceBounded (observation (var 0) (var 1) (var 3*var 2)) (observation (var 0) (var 1) (var 2))
        (num 4) (var 2)) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (finite_refinement _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))

theorem actual_partial_arctangent_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ le (var 0) (var 1) ⟶ pointCN nameF (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (.impI (name_regular _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianArctangentPartialQuadrature
