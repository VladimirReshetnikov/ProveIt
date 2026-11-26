import IPRADerivations.Analysis.Polynomials.GaussianPolynomialForwardDifferenceNormalization
import IPRADerivations.Analysis.Polynomials.GaussianPolynomialCoefficientDifferences
import IPRADerivations.Analysis.Polynomials.GaussianRationalCoefficientScaling

/-!
# Exact linearity of the encoded Gaussian forward-difference grid

A rowwise rational linear combination commutes with the actual adjacent
subtraction programs, including the final normalization by the common step.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialForwardDifferenceGridLinearity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open LeanProofs.IPRA.Foundations.SequenceEquality (agree sequence_equal)
open GaussianPolynomialForwardDifferenceGrid (adjacent adjacent_lookup differenceBody grid grid_succ grid_zero value)
open GaussianPolynomialForwardDifferenceNormalization (normalized inversePower)
open GaussianRationalHorner (qadd qmul)
open GaussianRationalMetric (qsub)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr)
open GaussianRationalTranslationStages (remaining remaining_step)
open ConciseIPRA.PTm (succ zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private def parameters (V W a b : PTm n) : PTm n := pairT (pairT a V) (pairT b W)

private def body : PTm 2 :=
  let left := fstT (var 1)
  let right := sndT (var 1)
  qadd (qmul (fstT left) (entry (sndT left) (var 0))) (qmul (fstT right) (entry (sndT right) (var 0)))

def combined (V W a b L : PTm n) : PTm n := sequence body L (parameters V W a b)

@[simp] theorem subst_combined {m : ℕ} (σ : Fin n → PTm m) (V W a b L : PTm n) :
    Syn.subst σ (combined V W a b L) =
      combined (Syn.subst σ V) (Syn.subst σ W) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ L) :=
  by simp [combined,parameters]

private theorem body_at (V W a b i : PTm n) : Γ ⊢[PRAAx] inst2 body i (parameters V W a b) ≐
    qadd (qmul a (entry V i)) (qmul b (entry W i)) := by
  let left := pairT a V
  let right := pairT b W
  have l := fst_pair (Γ := Γ) left right
  have r := snd_pair (Γ := Γ) left right
  ipra_congr (qadd (qmul (var 0) (entry (var 1) (var 4))) (qmul (var 2) (entry (var 3) (var 4))) : PTm 5)
    with [(congrFst l).eqTrans (fst_pair a V), (congrSnd l).eqTrans (snd_pair a V),
      (congrFst r).eqTrans (fst_pair b W), (congrSnd r).eqTrans (snd_pair b W), .eqRefl i]
    using [body,parameters,inst2,left,right]

theorem combined_at (V W a b L i : PTm n) (hi : Γ ⊢[PRAAx] lt i L) :
    Γ ⊢[PRAAx] entry (combined V W a b L) i ≐ qadd (qmul a (entry V i)) (qmul b (entry W i)) :=
  (sequence_decode body hi).eqTrans (body_at V W a b i)

def rowValue (V W a b i : PTm n) : PTm n := qadd (qmul a (entry V i)) (qmul b (entry W i))

@[simp] theorem subst_rowValue {m : ℕ} (σ : Fin n → PTm m) (V W a b i : PTm n) :
    Syn.subst σ (rowValue V W a b i) = rowValue (Syn.subst σ V) (Syn.subst σ W) (Syn.subst σ a)
      (Syn.subst σ b) (Syn.subst σ i) := by simp [rowValue]

theorem combined_equal (V W X Y a b c d L : PTm n)
    (h : lt (var 0) (Syn.shift L) :: Γ.map Fm.shift ⊢[PRAAx]
      rowValue (Syn.shift V) (Syn.shift W) (Syn.shift a) (Syn.shift b) (var 0) ≐
      rowValue (Syn.shift X) (Syn.shift Y) (Syn.shift c) (Syn.shift d) (var 0)) :
    Γ ⊢[PRAAx] combined V W a b L ≐ combined X Y c d L := by
  refine sequence_equal body body L _ _ (.allI (.impI ?_))
  let sh (t : PTm n) := Syn.shift t
  let i : PTm (n+1) := var 0
  simpa [agree,sh,i,Syn.shift,parameters] using
    (body_at (sh V) (sh W) (sh a) (sh b) i).eqTrans (h.eqTrans (body_at (sh X) (sh Y) (sh c) (sh d) i).eqSymm)

private theorem combined_congr {V W X Y a b L M : PTm n}
    (hV : Γ ⊢[PRAAx] V ≐ X) (hW : Γ ⊢[PRAAx] W ≐ Y) (hL : Γ ⊢[PRAAx] L ≐ M) :
    Γ ⊢[PRAAx] combined V W a b L ≐ combined X Y a b M := by
  ipra_congr (combined (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    with [hV, hW, .eqRefl a, .eqRefl b, hL]

private theorem adjacent_congr {V W L : PTm n} (h : Γ ⊢[PRAAx] V ≐ W) :
    Γ ⊢[PRAAx] adjacent V L ≐ adjacent W L := by
  ipra_congr (adjacent (var 0) (var 1) : PTm 2) with [h, .eqRefl L]

theorem adjacent_combined (V W a b L : PTm n) :
    Γ ⊢[PRAAx] adjacent (combined V W a b (succ L)) L ≐ combined (adjacent V L) (adjacent W L) a b L := by
  refine sequence_equal differenceBody body L _ _ (.allI (.impI ?_))
  let sh (t : PTm n) := Syn.shift t
  let j : PTm (n+1) := var 0
  let Δ := lt j (sh L) :: Γ.map Fm.shift
  let P := combined (sh V) (sh W) (sh a) (sh b) (succ (sh L))
  let V₁ := adjacent (sh V) (sh L)
  let W₁ := adjacent (sh W) (sh L)
  let v₀ := entry (sh V) j
  let w₀ := entry (sh W) j
  let v₁ := entry (sh V) (succ j)
  let w₁ := entry (sh W) (succ j)
  have hj : Δ ⊢[PRAAx] lt j (sh L) := Prf.hyp0
  have next : Δ ⊢[PRAAx] lt (succ j) (succ (sh L)) := (succ_monus_succ _ _).eqTrans hj
  have now := lt_of_lt_of_le hj (le_succ_self _)
  have diff : Δ ⊢[PRAAx] qsub (entry P (succ j)) (entry P j) ≐ qadd (qmul (sh a) (entry V₁ j)) (qmul (sh b) (entry W₁ j)) :=
    (qsub_congr (combined_at _ _ _ _ _ _ next) (combined_at _ _ _ _ _ _ now)).eqTrans
      ((GaussianPolynomialCoefficientDifferences.scalar_sum_difference (qmul (sh a) v₁) (qmul (sh a) v₀)
        (qmul (sh b) w₁) (qmul (sh b) w₀)).eqTrans
        (qadd_congr
          ((GaussianRationalRoundedPower.multiplication_difference (sh a) v₁ v₀).eqTrans
            (qmul_congr (.eqRefl _) (adjacent_lookup (sh V) (sh L) j hj).eqSymm))
          ((GaussianRationalRoundedPower.multiplication_difference (sh b) w₁ w₀).eqTrans
            (qmul_congr (.eqRefl _) (adjacent_lookup (sh W) (sh L) j hj).eqSymm))))
  have rows := diff.eqTrans (body_at V₁ W₁ (sh a) (sh b) j).eqSymm
  simpa [agree,Δ,P,V₁,W₁,sh,j,Syn.shift,differenceBody,inst2,parameters] using rows

private def stageLaw (V W a b N j : PTm n) : Fm PTm n :=
  le j N ⟶ grid (combined V W a b (succ N)) N j ≐ combined (grid V N j) (grid W N j) a b (succ (remaining N j))

@[simp] private theorem subst_stageLaw {m : ℕ} (σ : Fin n → PTm m) (V W a b N j : PTm n) :
    (stageLaw V W a b N j).subst σ =
      stageLaw (Syn.subst σ V) (Syn.subst σ W) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) (Syn.subst σ j) :=
  by simp [stageLaw]

theorem grid_combined (V W a b N j : PTm n) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] grid (combined V W a b (succ N)) N j ≐ combined (grid V N j) (grid W N j) a b (succ (remaining N j)) := by
  let sh (t : PTm n) := Syn.shift t
  have all : Γ ⊢[PRAAx] .all (stageLaw (sh V) (sh W) (sh a) (sh b) (sh N) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_stageLaw,Syn.subst_var,Syn.inst_zero,sh,Syn.subst_inst_shift]
      exact .impI ((grid_zero _ _).eqTrans (combined_congr (grid_zero V N).eqSymm (grid_zero W N).eqSymm
        (congrSucc (monus_zero N).eqSymm))).wk
    · simp only [subst_stageLaw,Syn.subst_var,Syn.repl_zero,sh,subst_repl_shift]
      refine .impI ?_
      let j' : PTm (n+1) := var 0
      let J := stageLaw (sh V) (sh W) (sh a) (sh b) (sh N) j'
      let Δ := le (succ j') (sh N) :: J :: Γ.map Fm.shift
      let L := remaining (sh N) j'
      let V' := grid (sh V) (sh N) j'
      let W' := grid (sh W) (sh N) j'
      have next : Δ ⊢[PRAAx] lt j' (sh N) := Prf.hyp0
      have ih := Prf.impE (Prf.hyp1 : Δ ⊢[PRAAx] J) (le_trans (le_succ_self _) next)
      exact (grid_succ _ _ _).eqTrans ((adjacent_congr (L := L) ih).eqTrans
        ((adjacent_combined V' W' (sh a) (sh b) L).eqTrans
          (combined_congr (grid_succ (sh V) (sh N) j').eqSymm (grid_succ (sh W) (sh N) j').eqSymm
            (remaining_step (sh N) j' next))))
  have rule : Γ ⊢[PRAAx] stageLaw V W a b N j := by
    simpa only [sh,subst_stageLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE rule hj

theorem value_combined (V W a b N : PTm n) :
    Γ ⊢[PRAAx] value (combined V W a b (succ N)) N ≐ qadd (qmul a (value V N)) (qmul b (value W N)) :=
  (entry_congr (grid_combined V W a b N N (le_refl _)) (.eqRefl zero)).eqTrans
    (combined_at _ _ _ _ _ _ (zero_lt_succ _))

private theorem swap_factors (s t x : PTm n) : Γ ⊢[PRAAx] qmul s (qmul t x) ≐ qmul t (qmul s x) :=
  (GaussianReciprocalHorner.qmul_associative s t x).eqSymm.eqTrans
    ((qmul_congr (GaussianRationalPowerAlgebra.qmul_commutative s t) (.eqRefl _)).eqTrans
      (GaussianReciprocalHorner.qmul_associative t s x))

theorem normalized_combined (V W a b N h : PTm n) :
    Γ ⊢[PRAAx] normalized (combined V W a b (succ N)) N h ≐
      qadd (qmul a (normalized V N h)) (qmul b (normalized W N h)) := by
  let s := inversePower h N
  let x := value V N
  let y := value W N
  exact (qmul_congr (.eqRefl s) (value_combined V W a b N)).eqTrans
    ((GaussianRationalCoefficientScaling.qmul_add s (qmul a x) (qmul b y)).eqTrans
      (qadd_congr (swap_factors s a x) (swap_factors s b y)))

theorem actual_Gaussian_normalized_grid_linearity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let V := var 0
     let W := var 1
     let a := var 2
     let b := var 3
     let N := var 4
     let h := var 5
     normalized (combined V W a b (succ N)) N h ≐ qadd (qmul a (normalized V N h)) (qmul b (normalized W N h))) :=
  closeUniv 6 (normalized_combined _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianPolynomialForwardDifferenceGridLinearity
