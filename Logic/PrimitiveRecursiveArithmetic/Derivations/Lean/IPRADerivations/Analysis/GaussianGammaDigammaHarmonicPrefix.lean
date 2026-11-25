import IPRADerivations.Analysis.GaussianGammaDigammaHarmonicCells
import IPRADerivations.Analysis.GaussianGammaDigammaFiniteSum

/-!
# Literal reciprocal prefixes between harmonic rectangle bounds

The finite prefix contains both endpoints. The harmonic integral lies
above the prefix with the first reciprocal removed and below the
prefix with half of each endpoint removed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaHarmonicPrefix

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaDigammaFiniteSum (index reciprocalBody reciprocalSum reciprocal_entry row_source)
open GaussianGammaDigammaHarmonicCells (cell halfReciprocal half_pair right_rectangle trapezoid cell_zero chain)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qadd qzero ofGaussian_canonical)
open GaussianRationalSyntheticDivision (qadd_congr qzero_add)
open GaussianRationalSumAlgebra (qadd_associative shuffle_four)
open GaussianReciprocalHorner (qadd_commutative)
open GaussianStirlingGammaLogarithm (source)
open GaussianStirlingTailComparison (point_order_refl point_add_order)
open RationalArgmin (rationalLE rationalLE_congr transitive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def prefixCell (a b Q L j : PTm n) : PTm n := cell (index a b j) a Q L
def endpointPair (a b j : PTm n) : PTm n := qadd (halfReciprocal a b) (halfReciprocal (index a b j) b)

def prefixBounds (a b Q L j : PTm n) : Fm PTm n := le (Q*index a b j) L ⟶
  (rationalLE (fstT (qadd (prefixCell a b Q L j) (endpointPair a b j))) (fstT (reciprocalSum a b (succ j))) ⋏
   rationalLE (fstT (reciprocalSum a b (succ j))) (fstT (qadd (prefixCell a b Q L j) (fraction b a))))

@[simp] theorem subst_prefixCell {m : ℕ} (σ : Fin n → PTm m) (a b Q L j : PTm n) :
    Syn.subst σ (prefixCell a b Q L j) = prefixCell (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ Q) (Syn.subst σ L) (Syn.subst σ j) := by
  simp [prefixCell]
@[simp] theorem subst_endpointPair {m : ℕ} (σ : Fin n → PTm m) (a b j : PTm n) :
    Syn.subst σ (endpointPair a b j) = endpointPair (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ j) := by simp [endpointPair]
@[simp] theorem subst_prefixBounds {m : ℕ} (σ : Fin n → PTm m) (a b Q L j : PTm n) :
    (prefixBounds a b Q L j).subst σ = prefixBounds (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ Q) (Syn.subst σ L) (Syn.subst σ j) := by
  simp [prefixBounds]

private theorem cell_first_congr {a a' c Q L : PTm n} (e : Γ ⊢[PRAAx] a ≐ a') :
    Γ ⊢[PRAAx] cell a c Q L ≐ cell a' c Q L := by
  simpa only [GaussianGammaDigammaHarmonicCells.subst_cell,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (cell (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![a,c,Q,L]) (σ' := ![a',c,Q,L]) (fun i => by fin_cases i <;> first | exact e | exact .eqRefl _)

theorem index_succ (a b j : PTm n) : Γ ⊢[PRAAx] index a b (succ j) ≐ index a b j+b := by
  unfold index
  ipra_ring

theorem reciprocal_succ (a b j : PTm n) : Γ ⊢[PRAAx] reciprocalSum a b (succ j) ≐
    qadd (reciprocalSum a b j) (fraction b (index a b j)) :=
  (GaussianRationalFiniteSum.sum_succ reciprocalBody j (pairT a b)).eqTrans (qadd_congr (.eqRefl _) (reciprocal_entry a b j))

private theorem rectangle_rearrangement (M H H₀ K : PTm n) : Γ ⊢[PRAAx]
    qadd (qadd M (qadd H K)) (qadd H₀ K) ≐ qadd (qadd M (qadd H₀ H)) (qadd K K) := by
  have e : Γ ⊢[PRAAx] qadd (qadd H K) (qadd H₀ K) ≐ qadd (qadd H₀ H) (qadd K K) :=
    (qadd_associative (qadd H K) H₀ K).eqSymm.eqTrans
      ((shuffle_four H K H₀ K).eqTrans (qadd_congr (qadd_commutative H H₀) (.eqRefl _)))
  exact (qadd_associative M (qadd H K) (qadd H₀ K)).eqTrans
    ((qadd_congr (.eqRefl _) e).eqTrans (qadd_associative M (qadd H₀ H) (qadd K K)).eqSymm)

private theorem prefix_zero (a b Q L : PTm n) (ha : Γ ⊢[PRAAx] le one a) : Γ ⊢[PRAAx] prefixBounds a b Q L zero := by
  refine .impI ?_
  let Δ := le (Q*index a b zero) L::Γ
  have e : Δ ⊢[PRAAx] index a b zero ≐ a := by unfold index; ipra_ring
  have m : Δ ⊢[PRAAx] prefixCell a b Q L zero ≐ qzero :=
    (cell_first_congr e).eqTrans (cell_zero a Q L)
  have u : Δ ⊢[PRAAx] fraction b (index a b zero) ≐ fraction b a :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) e
  have r : Δ ⊢[PRAAx] reciprocalSum a b (succ zero) ≐ fraction b a :=
    (reciprocal_succ a b zero).eqTrans ((qadd_congr (GaussianRationalFiniteSum.sum_zero reciprocalBody _) u).eqTrans
      (qzero_add _ (ofGaussian_canonical _ _ ha.wk)))
  have half : Δ ⊢[PRAAx] halfReciprocal (index a b zero) b ≐ halfReciprocal a b :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (congrMul (.eqRefl _) e)
  have ep : Δ ⊢[PRAAx] endpointPair a b zero ≐ fraction b a :=
    (qadd_congr (.eqRefl _) half).eqTrans (half_pair a b ha.wk)
  have left := (qadd_congr m ep).eqTrans (qzero_add _ (ofGaussian_canonical _ _ ha.wk))
  have right := (qadd_congr m (.eqRefl (fraction b a))).eqTrans (qzero_add _ (ofGaussian_canonical _ _ ha.wk))
  exact .andI (rationalLE_congr (congrFst left).eqSymm (congrFst r).eqSymm (point_order_refl _))
    (rationalLE_congr (congrFst r).eqSymm (congrFst right).eqSymm (point_order_refl _))

set_option maxHeartbeats 600000 in
private theorem prefix_step (a b Q L j : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hQ : Γ ⊢[PRAAx] le one Q)
    (ih : Γ ⊢[PRAAx] prefixBounds a b Q L j) : Γ ⊢[PRAAx] prefixBounds a b Q L (succ j) := by
  refine .impI ?_
  let c := index a b j
  let d := index a b (succ j)
  let Δ := le (Q*d) L::Γ
  let M := prefixCell a b Q L j
  let M' := prefixCell a b Q L (succ j)
  let C := cell (c+b) c Q L
  let R := reciprocalSum a b (succ j)
  let R' := reciprocalSum a b (succ (succ j))
  let F := fraction b d
  let U := fraction b a
  let H := halfReciprocal c b
  let K := halfReciprocal d b
  let H₀ := halfReciprocal a b
  have he := index_succ (Γ := Δ) a b j
  have hc := (row_source a b j (Prf.wk hs : Δ ⊢[PRAAx] source a b)).andE₁
  have hd : Δ ⊢[PRAAx] le one d := (row_source a b (succ j) (Prf.wk hs : Δ ⊢[PRAAx] source a b)).andE₁
  have hC : Δ ⊢[PRAAx] le (Q*(c+b)) L := le_congr (congrMul (.eqRefl _) he) (.eqRefl _) Prf.hyp0
  have hPrev := le_trans (le_congr (mul_comm c Q) (mul_comm (c+b) Q) (mul_le_mul_right Q (le_add_right c b))) hC
  have old := Prf.impE ih.wk hPrev
  have e : Δ ⊢[PRAAx] qadd M C ≐ M' := (chain a c (c+b) Q L).eqTrans (cell_first_congr he.eqSymm)
  have r : Δ ⊢[PRAAx] R' ≐ qadd R F := reciprocal_succ a b (succ j)
  have term : Δ ⊢[PRAAx] F ≐ fraction b (c+b) :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) he
  have hTerm : Δ ⊢[PRAAx] halfReciprocal (c+b) b ≐ K :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (congrMul (.eqRefl _) he.eqSymm)
  have min := rationalLE_congr (congrFst term).eqSymm (.eqRefl _)
    (right_rectangle c b Q L hc hQ.wk hC)
  have max := rationalLE_congr (.eqRefl _) (congrFst (qadd_congr (.eqRefl H) hTerm))
    (trapezoid c b Q L hc hQ.wk)
  have up := point_add_order R (qadd M U) F C old.andE₂ min
  have sumU : Δ ⊢[PRAAx] qadd (qadd M U) C ≐ qadd M' U :=
    (qadd_associative M U C).eqTrans ((qadd_congr (.eqRefl _) (qadd_commutative U C)).eqTrans
      ((qadd_associative M C U).eqSymm.eqTrans (qadd_congr e (.eqRefl _))))
  have lo1 := point_add_order _ _ _ _ (point_add_order M M C (qadd H K) (point_order_refl M) max)
    (point_order_refl (qadd H₀ K))
  have lo2 := point_add_order (qadd M (qadd H₀ H)) R (qadd K K) F old.andE₁
    (rationalLE_congr (.eqRefl _) (congrFst (half_pair d b hd))
      (point_order_refl (qadd K K)))
  have merged := transitive lo1 (rationalLE_congr (congrFst (rectangle_rearrangement M H H₀ K)).eqSymm (.eqRefl _) lo2)
  exact .andI (rationalLE_congr (congrFst (qadd_congr e (.eqRefl _))) (congrFst r).eqSymm merged)
    (rationalLE_congr (congrFst r).eqSymm (congrFst sumU) up)

theorem prefix_bounds (a b Q L j : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hQ : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] prefixBounds a b Q L j := by
  have shifted : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hs.shift
  have shiftedQ : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift Q) := by simpa [Fm.shift,Syn.shift] using hQ.shift
  have h : Γ ⊢[PRAAx] .all (prefixBounds (Syn.shift a) (Syn.shift b) (Syn.shift Q) (Syn.shift L) (var 0)) := by
    refine PRA.qfInd _ (by unfold prefixBounds rationalLE; exact ⟨le_QF _ _,⟨le_QF _ _,le_QF _ _⟩⟩) ?_ ?_
    · simpa only [subst_prefixBounds,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using prefix_zero a b Q L hs.andE₁
    · simpa only [subst_prefixBounds,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        prefix_step (Syn.shift a) (Syn.shift b) (Syn.shift Q) (Syn.shift L) (var 0) shifted.wk shiftedQ.wk Prf.hyp0
  simpa only [subst_prefixBounds,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE j

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaHarmonicPrefix
