import IPRADerivations.Analysis.Polynomials.FiniteDifferences.GaussianPolynomialForwardDifferenceNormalization

/-!
# Exact increments of the encoded Gaussian forward-difference grid

Each adjacent-difference stage commutes with taking a contiguous window
of the input observations. The quotient of the two adjacent normalized
order-(e) windows is the normalized order-(e+1) observation of the
whole grid, with one common step.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialForwardDifferenceGridIncrement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_decode sequence_length)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr length)
open LeanProofs.IPRA.Foundations.SequenceEquality (agree sequence_equal)
open GaussianPolynomialForwardDifferenceGrid (adjacent adjacent_lookup differenceBody grid grid_succ grid_zero value)
open GaussianPolynomialForwardDifferenceNormalization (normalized inversePower)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (qsub)
open GaussianRationalReciprocal (reciprocal power_succ)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open GaussianRationalTranslationStages (remaining remaining_positive remaining_step)
open ConciseIPRA.PTm (succ zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private def sliceBody : PTm 2 := entry (fstT (var 1)) (sndT (var 1)+var 0)

def slice (V offset count : PTm n) : PTm n := sequence sliceBody count (pairT V offset)

@[simp] theorem subst_slice {m : ℕ} (σ : Fin n → PTm m) (V offset count : PTm n) :
    Syn.subst σ (slice V offset count) = slice (Syn.subst σ V) (Syn.subst σ offset) (Syn.subst σ count) :=
  by simp [slice]

theorem slice_length (V offset count : PTm n) :
    Γ ⊢[PRAAx] length (slice V offset count) ≐ count :=
  sequence_length _ _ _

private theorem slice_body_at (V offset j : PTm n) :
    Γ ⊢[PRAAx] inst2 sliceBody j (pairT V offset) ≐ entry V (offset+j) := by
  ipra_congr (entry (var 0) (var 1+var 2) : PTm 3)
    with [fst_pair V offset, snd_pair V offset, .eqRefl j] using [sliceBody,inst2]

theorem slice_at (V offset count j : PTm n) (hj : Γ ⊢[PRAAx] lt j count) :
    Γ ⊢[PRAAx] entry (slice V offset count) j ≐ entry V (offset+j) :=
  (sequence_decode sliceBody hj).eqTrans (slice_body_at V offset j)

private theorem slice_congr {V W d L M : PTm n} (hV : Γ ⊢[PRAAx] V ≐ W) (hL : Γ ⊢[PRAAx] L ≐ M) :
    Γ ⊢[PRAAx] slice V d L ≐ slice W d M := by
  ipra_congr (slice (var 0) (var 1) (var 2) : PTm 3) with [hV, .eqRefl d, hL]

private theorem adjacent_congr {V W L : PTm n} (h : Γ ⊢[PRAAx] V ≐ W) :
    Γ ⊢[PRAAx] adjacent V L ≐ adjacent W L := by
  ipra_congr (adjacent (var 0) (var 1) : PTm 2) with [h, .eqRefl L]

theorem adjacent_slice (V d N M : PTm n) (hd : Γ ⊢[PRAAx] le (d+M) N) :
    Γ ⊢[PRAAx] adjacent (slice V d (succ M)) M ≐ slice (adjacent V N) d M := by
  refine sequence_equal differenceBody sliceBody M _ _ (.allI (.impI ?_))
  let a (t : PTm n) := Syn.shift t
  let j : PTm (n+1) := var 0
  let Δ := lt j (a M) :: Γ.map Fm.shift
  let W := slice (a V) (a d) (succ (a M))
  have h : Δ ⊢[PRAAx] le (a d+a M) (a N) := by
    simpa [Δ,a,j,Fm.shift,Syn.shift] using hd.shift.wk
  have hj : Δ ⊢[PRAAx] lt j (a M) := Prf.hyp0
  have next : Δ ⊢[PRAAx] lt (succ j) (succ (a M)) := (succ_monus_succ _ _).eqTrans hj
  have large : Δ ⊢[PRAAx] lt (a d+j) (a N) :=
    le_trans (le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right (a d) hj)) h
  have atNext := (slice_at (a V) (a d) (succ (a M)) (succ j) next).eqTrans
    (entry_congr (.eqRefl _) (by ipra_ring : Δ ⊢[PRAAx] a d+succ j ≐ succ (a d+j)))
  have atNow := slice_at (a V) (a d) (succ (a M)) j (lt_of_lt_of_le hj (le_succ_self _))
  have aligned : Δ ⊢[PRAAx] qsub (entry W (succ j)) (entry W j) ≐
      inst2 sliceBody j (pairT (adjacent (a V) (a N)) (a d)) :=
    (qsub_congr atNext atNow).eqTrans
      ((adjacent_lookup (a V) (a N) (a d+j) large).eqSymm.eqTrans
        (slice_body_at (adjacent (a V) (a N)) (a d) j).eqSymm)
  simpa [agree,Δ,a,j,W,Syn.shift,differenceBody,inst2] using aligned

private theorem remaining_window (d N M j : PTm n)
    (hd : Γ ⊢[PRAAx] le (d+M) N) (hj : Γ ⊢[PRAAx] le j M) :
    Γ ⊢[PRAAx] le (d+remaining M j) (remaining N j) := by
  have hjN := le_trans hj (le_trans (le_add_left M d) hd)
  have left := (congrAdd (.eqRefl d) (eq_add_of_le hj)).eqTrans
    (by change Γ ⊢[PRAAx] d+(j+remaining M j) ≐ (d+remaining M j)+j; ipra_ring)
  have right := (eq_add_of_le hjN).eqTrans
    (by change Γ ⊢[PRAAx] j+remaining N j ≐ remaining N j+j; ipra_ring)
  exact le_of_add_le_add_right (le_congr left right hd)

private def stageLaw (V d N M j : PTm n) : Fm PTm n :=
  le j M ⟶ grid (slice V d (succ M)) M j ≐ slice (grid V N j) d (succ (remaining M j))

@[simp] private theorem subst_stageLaw {m : ℕ} (σ : Fin n → PTm m) (V d N M j : PTm n) :
    (stageLaw V d N M j).subst σ =
      stageLaw (Syn.subst σ V) (Syn.subst σ d) (Syn.subst σ N) (Syn.subst σ M) (Syn.subst σ j) :=
  by simp [stageLaw]

theorem grid_slice (V d N M j : PTm n) (hd : Γ ⊢[PRAAx] le (d+M) N) (hj : Γ ⊢[PRAAx] le j M) :
    Γ ⊢[PRAAx] grid (slice V d (succ M)) M j ≐ slice (grid V N j) d (succ (remaining M j)) := by
  let a (t : PTm n) := Syn.shift t
  have all : Γ ⊢[PRAAx] .all (stageLaw (a V) (a d) (a N) (a M) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_stageLaw,Syn.subst_var,Syn.inst_zero,a,Syn.subst_inst_shift]
      exact .impI ((grid_zero _ _).eqTrans (slice_congr (grid_zero V N).eqSymm
        (congrSucc (monus_zero M).eqSymm))).wk
    · simp only [subst_stageLaw,Syn.subst_var,Syn.repl_zero,a,subst_repl_shift]
      refine .impI ?_
      let i : PTm (n+1) := var 0
      let J := stageLaw (a V) (a d) (a N) (a M) i
      let Δ := le (succ i) (a M) :: J :: Γ.map Fm.shift
      let k := remaining (a M) i
      let l := remaining (a N) i
      let W := grid (a V) (a N) i
      have h : Δ ⊢[PRAAx] le (a d+a M) (a N) := by
        simpa [Δ,a,Fm.shift,Syn.shift] using hd.shift.wk.wk
      have next : Δ ⊢[PRAAx] lt i (a M) := Prf.hyp0
      have old := le_trans (le_succ_self _) next
      have ih := Prf.impE (Prf.hyp1 : Δ ⊢[PRAAx] J) old
      have compatible : Δ ⊢[PRAAx] le (a d+k) l := remaining_window (a d) (a N) (a M) i h old
      exact (grid_succ _ _ _).eqTrans ((adjacent_congr (L := k) ih).eqTrans
        ((adjacent_slice W (a d) l k compatible).eqTrans
          (slice_congr (grid_succ (a V) (a N) i).eqSymm (remaining_step (a M) i next))))
  have rule : Γ ⊢[PRAAx] stageLaw V d N M j := by
    simpa only [a,subst_stageLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE rule hj

theorem terminal_slice (V d N M : PTm n) (hd : Γ ⊢[PRAAx] le (d+M) N) :
    Γ ⊢[PRAAx] value (slice V d (succ M)) M ≐ entry (grid V N M) d :=
  (entry_congr (grid_slice V d N M M hd (le_refl _)) (.eqRefl zero)).eqTrans
    ((slice_at _ d _ zero (zero_lt_succ _)).eqTrans (entry_congr (.eqRefl _) (add_zero d)))

theorem value_increment (V e : PTm n) :
    Γ ⊢[PRAAx] value V (succ e) ≐ qsub (value (slice V one (succ e)) e) (value (slice V zero (succ e)) e) := by
  have first : Γ ⊢[PRAAx] le (one+e) (succ e) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_refl (succ e))
  have last : Γ ⊢[PRAAx] le (zero+e) (succ e) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_succ_self e)
  have positive := remaining_positive (succ e) e (le_refl (Γ := Γ) (succ e))
  exact (entry_congr (grid_succ V (succ e) e) (.eqRefl zero)).eqTrans
    ((adjacent_lookup _ _ zero positive).eqTrans
      (qsub_congr (terminal_slice V one (succ e) e first).eqSymm (terminal_slice V zero (succ e) e last).eqSymm))

theorem normalized_increment (V e h : PTm n) :
    Γ ⊢[PRAAx] qmul (reciprocal h) (qsub (normalized (slice V one (succ e)) e h)
      (normalized (slice V zero (succ e)) e h)) ≐ normalized V (succ e) h := by
  let P := inversePower h e
  let X := value (slice V one (succ e)) e
  let Y := value (slice V zero (succ e)) e
  let Z := value V (succ e)
  let s := reciprocal h
  have step : Γ ⊢[PRAAx] qmul s P ≐ inversePower h (succ e) :=
    (GaussianRationalPowerAlgebra.qmul_commutative s P).eqTrans (power_succ s e).eqSymm
  exact (qmul_congr (.eqRefl s) (GaussianRationalRoundedPower.multiplication_difference P X Y)).eqTrans
    ((GaussianReciprocalHorner.qmul_associative s P (qsub X Y)).eqSymm.eqTrans
      (qmul_congr step (value_increment V e).eqSymm))

theorem actual_Gaussian_normalized_grid_increment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (let V := var 0
     let e := var 1
     let h := var 2
     qmul (reciprocal h) (qsub (normalized (slice V one (succ e)) e h)
       (normalized (slice V zero (succ e)) e h)) ≐ normalized V (succ e) h) :=
  closeUniv 3 (normalized_increment _ _ _)

end LeanProofs.IPRA.Analysis.GaussianPolynomialForwardDifferenceGridIncrement
