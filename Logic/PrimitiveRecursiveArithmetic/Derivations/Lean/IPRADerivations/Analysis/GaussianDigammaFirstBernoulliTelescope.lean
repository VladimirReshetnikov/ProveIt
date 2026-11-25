import IPRADerivations.Analysis.GaussianDigammaFirstBernoulliReference

/-!
# Exact telescoping of the digamma reference rows

The original reference rows telescope to the closed reciprocal prefix
with its two half-endpoints and its single harmonic interval removed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace LeanProofs.IPRA.Analysis.GaussianDigammaFirstBernoulliTelescope

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianDigammaFirstBernoulliLocal (reference)
open GaussianDigammaFirstBernoulliReference (anchor subst_anchor subst_reference harmonicPrefix reference_row anchor_zero)
open GaussianGammaDigammaFiniteSum (index subst_index reciprocalBody reciprocalSum reciprocal_entry row_source)
open GaussianGammaDigammaHarmonicCells (halfReciprocal half_pair)
open GaussianGammaDigammaHarmonicPrefix (endpointPair reciprocal_succ)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalFiniteSum (sum addBody sum_add sum_congr_bounded termsEqual inst2_addBody sum_canonical)
open GaussianRationalHorner (qadd ofGaussian_canonical positive_product)
open GaussianRationalMetric (qsub qnegative)
open GaussianRationalParameterTelescope (forward forward_at forward_sum)
open GaussianRationalInverseQuadraticAlgebra (subtract_sum)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr qadd_sub_cancel)
open GaussianReciprocalHorner (qadd_commutative)
open GaussianStirlingAllOrderPanelPartsOuter (data)
open GaussianStirlingGammaLogarithm (source)
open RationalGaussianEmbedding (embed subst_embed)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def refBody : PTm 2 :=
  let x := var 1
  embed (reference (index (fstT x) (fstT (sndT x)) (var 0)) (fstT (sndT x)) (sndT (sndT x)))

def anchorBody : PTm 2 :=
  let x := var 1
  anchor (fstT x) (fstT (sndT x)) (sndT (sndT x)) (var 0)

def recipBody : PTm 2 :=
  let x := var 1
  inst2 reciprocalBody (var 0) (pairT (fstT x) (fstT (sndT x)))

def refPrefix (A B Q L : PTm n) : PTm n := sum refBody L (data A B Q)

def meshTarget (A B Q L : PTm n) : PTm n :=
  qsub (qsub (reciprocalSum A B (succ L)) (endpointPair A B L)) (harmonicPrefix A B Q L)

@[simp] theorem subst_refPrefix {m : ℕ} (σ : Fin n → PTm m) (A B Q L : PTm n) :
    Syn.subst σ (refPrefix A B Q L) = refPrefix (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ Q) (Syn.subst σ L) := by
  simp [refPrefix,data]

private theorem read_fields (A B Q : PTm n) : Γ ⊢[PRAAx]
    fstT (data A B Q) ≐ A ⋏ (fstT (sndT (data A B Q)) ≐ B ⋏ sndT (sndT (data A B Q)) ≐ Q) := by
  have h : Γ ⊢[PRAAx] sndT (data A B Q) ≐ pairT B Q := snd_pair _ _
  exact .andI (fst_pair _ _) (.andI ((congrFst h).eqTrans (fst_pair _ _)) ((congrSnd h).eqTrans (snd_pair _ _)))

theorem ref_at (A B Q k : PTm n) : Γ ⊢[PRAAx] inst2 refBody k (data A B Q) ≐ embed (reference (index A B k) B Q) := by
  let d := data A B Q
  have h := read_fields (Γ := Γ) A B Q
  have u : Γ ⊢[PRAAx] index (fstT d) (fstT (sndT d)) k ≐ index A B k :=
    congrAdd h.andE₁ (congrMul (.eqRefl _) h.andE₂.andE₁)
  simpa only [refBody,inst2,subst_embed,subst_reference,subst_index,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (embed (reference (var 0) (var 1) (var 2)) : PTm 3)
      (σ := ![index (fstT d) (fstT (sndT d)) k,fstT (sndT d),sndT (sndT d)]) (σ' := ![index A B k,B,Q])
      (fun i => by fin_cases i; exact u; exact h.andE₂.andE₁; exact h.andE₂.andE₂)

theorem anchor_at (A B Q k : PTm n) : Γ ⊢[PRAAx] inst2 anchorBody k (data A B Q) ≐ anchor A B Q k := by
  let d := data A B Q
  have h := read_fields (Γ := Γ) A B Q
  simpa only [anchorBody,inst2,subst_anchor,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (anchor (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![fstT d,fstT (sndT d),sndT (sndT d),k]) (σ' := ![A,B,Q,k])
      (fun i => by fin_cases i; exact h.andE₁; exact h.andE₂.andE₁; exact h.andE₂.andE₂; exact .eqRefl _)

theorem recip_at (A B Q k : PTm n) : Γ ⊢[PRAAx] inst2 recipBody k (data A B Q) ≐ inst2 reciprocalBody k (pairT A B) := by
  have h := read_fields (Γ := Γ) A B Q
  change Γ ⊢[PRAAx] Syn.subst ![k,data A B Q] recipBody ≐ _
  simp only [recipBody,subst_inst2,subst_pairT,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact congrInst2 reciprocalBody (.eqRefl _) (congrPairT h.andE₁ h.andE₂.andE₁)

private theorem ref_readback (A B Q L : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] refPrefix A B Q L ≐ qadd (reciprocalSum A B L) (qsub (anchor A B Q L) (halfReciprocal A B)) := by
  let x := data A B Q
  let f := GaussianRationalFiniteSum.addBody recipBody (forward anchorBody)
  have rows : Γ ⊢[PRAAx] termsEqual refBody f L x x := by
    refine .allI (.impI ?_)
    let sh (t : PTm n) := Syn.shift t
    let i : PTm (n+1) := var 0
    let Δ := lt i (sh L) :: Γ.map Fm.shift
    let d := data (sh A) (sh B) (sh Q)
    have h : Δ ⊢[PRAAx] source (sh A) (sh B) := by simpa [Δ,sh,Syn.shift,Fm.shift] using hs.shift.wk
    have hRec := (recip_at (Γ := Δ) (sh A) (sh B) (sh Q) i).eqTrans (reciprocal_entry _ _ _)
    have fw : Δ ⊢[PRAAx] inst2 (forward anchorBody) i d ≐
        qsub (anchor (sh A) (sh B) (sh Q) (succ i)) (anchor (sh A) (sh B) (sh Q) i) := by
      rw [forward_at]
      exact qsub_congr (anchor_at _ _ _ _) (anchor_at _ _ _ _)
    have rhs : Δ ⊢[PRAAx] inst2 f i d ≐ qadd (fraction (sh B) (index (sh A) (sh B) i))
        (qsub (anchor (sh A) (sh B) (sh Q) (succ i)) (anchor (sh A) (sh B) (sh Q) i)) := by
      unfold f
      rw [GaussianRationalFiniteSum.inst2_addBody]
      exact qadd_congr hRec fw
    simpa [termsEqual,x,d,sh,i,Δ,Syn.shift,data] using
      ((ref_at (Γ := Δ) (sh A) (sh B) (sh Q) i).eqTrans ((reference_row _ _ _ _ h).eqTrans rhs.eqSymm))
  have eqR : Γ ⊢[PRAAx] termsEqual recipBody reciprocalBody L x (pairT A B) := by
    refine .allI (.impI ?_)
    simpa [termsEqual,x,Syn.shift,data] using
      (recip_at (Γ := lt (var 0) (Syn.shift L) :: Γ.map Fm.shift) (Syn.shift A) (Syn.shift B) (Syn.shift Q) (var 0))
  have part := (forward_sum (Γ := Γ) anchorBody L x).eqTrans
    (qsub_congr (anchor_at A B Q L) ((anchor_at A B Q zero).eqTrans (anchor_zero A B Q hs.andE₁)))
  exact (GaussianRationalFiniteSum.sum_congr_bounded refBody f L x x rows).eqTrans
    ((GaussianRationalFiniteSum.sum_add recipBody (forward anchorBody) L x).eqTrans
      (qadd_congr (GaussianRationalFiniteSum.sum_congr_bounded recipBody reciprocalBody L x (pairT A B) eqR) part))

theorem exact_prefix (A B Q L : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] refPrefix A B Q L ≐ meshTarget A B Q L := by
  let R := reciprocalSum A B L
  let S := reciprocalSum A B (succ L)
  let x := halfReciprocal A B
  let y := halfReciprocal (index A B L) B
  let H := harmonicPrefix A B Q L
  have h := (row_source A B L hs).andE₁
  have sumEq := (reciprocal_succ A B L).eqTrans
    (qadd_congr (.eqRefl R) (half_pair (index A B L) B h).eqSymm)
  have middle := (qadd_associative (Γ := Γ) R y y).eqSymm.eqTrans (qadd_commutative _ y)
  have cancel : Γ ⊢[PRAAx] qsub S y ≐ qadd R y :=
    ((qsub_congr (sumEq.eqTrans middle) (.eqRefl y)).eqTrans (qadd_sub_cancel y _ (GaussianRationalHorner.qadd_canonical _ _)))
  have combine : Γ ⊢[PRAAx] qadd R (qsub (qsub y H) x) ≐ qsub (qadd R y) (qadd H x) :=
    (qadd_congr (.eqRefl R) (subtract_sum y H x)).eqTrans (qadd_associative R y (qnegative (qadd H x))).eqSymm
  have order : Γ ⊢[PRAAx] qadd y (qadd H x) ≐ qadd (qadd x y) H :=
    (qadd_congr (.eqRefl _) (qadd_commutative H x)).eqTrans
      ((qadd_associative _ _ _).eqSymm.eqTrans (qadd_congr (qadd_commutative y x) (.eqRefl _)))
  have last := (qsub_congr cancel.eqSymm (.eqRefl (qadd H x))).eqTrans
    ((subtract_sum S y (qadd H x)).eqTrans
      ((qsub_congr (.eqRefl S) order).eqTrans (subtract_sum S (qadd x y) H).eqSymm))
  exact (ref_readback A B Q L hs).eqTrans (combine.eqTrans last)

end LeanProofs.IPRA.Analysis.GaussianDigammaFirstBernoulliTelescope
