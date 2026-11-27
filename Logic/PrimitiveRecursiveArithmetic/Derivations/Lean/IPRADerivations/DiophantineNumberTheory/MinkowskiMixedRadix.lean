import IPRADerivations.DiophantineNumberTheory.MinkowskiResidues
import IPRADerivations.Core.ProdLemmas

/-!
# Actual runtime mixed-radix digits for finite boxes

The Minkowski packet, paper/02_finite_proof.tex, refines each integer box
using its own positive coordinate widths. The lower-order radix product is
`P(k)=∏_{t<k} width(t)` and digit `k` of index `i` is literally
`rem (quo i P(k)) width(k)`. Both dimension and the width sequence are
runtime numerical inputs. Zero dimension has product one.

A proved natural division identity reconstructs each prefix remainder.
Quantifier-free induction on that identity proves that equal decoded digits
of indices below the actual product imply equality of the indices. No
enumeration, range, cardinality or injectivity law is an input assumption.
The total entry decoder is used literally, without a zero-padding promise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiMixedRadix

open_ipra exports
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.DiophantineNumberTheory.SignedEuclidean (natural_divmod positive_form)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Actual lower-order product of the decoded coordinate widths. -/
def widthBody : PTm 2 := entry (var 1) (var 0)
def count (N W : PTm n) : PTm n := ap2 (prodF widthBody) N W
/-- Actual independent quotient/remainder random-access digit. -/
def digit (W i k : PTm n) : PTm n := rem (quo i (count k W)) (entry W k)

@[simp] theorem subst_count {l : ℕ} (σ : Fin n → PTm l) (N W : PTm n) :
    Syn.subst σ (count N W) = count (Syn.subst σ N) (Syn.subst σ W) := subst_ap2 _ _ _ _
@[simp] theorem subst_digit {l : ℕ} (σ : Fin n → PTm l) (W i k : PTm n) :
    Syn.subst σ (digit W i k) = digit (Syn.subst σ W) (Syn.subst σ i) (Syn.subst σ k) := by
  simp only [digit, subst_ap2, subst_count, subst_entry]

theorem count_zero (W : PTm n) : Γ ⊢[PRAAx] count zero W ≐ one := prod_zero _ _
theorem count_succ (N W : PTm n) : Γ ⊢[PRAAx] count (succ N) W ≐ count N W * entry W N := by
  simpa only [count, widthBody, subst_entry, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one] using prod_succ (Γ := Γ) widthBody N W

def positive (N W : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ le one (entry (Syn.shift W) (var 0)))

@[simp] theorem subst_positive {l : ℕ} (σ : Fin n → PTm l) (N W : PTm n) :
    (positive N W).subst σ = positive (Syn.subst σ N) (Syn.subst σ W) := by
  simp only [positive, Fm.subst_all, Fm.subst_imp, subst_lt, subst_le, subst_entry,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
    Syn.subst_var, Syn.up_zero, Syn.up_succ, Syn.subst_shift, Syn.shift_subst]

theorem positive_at (N W k : PTm n) (h : Γ ⊢[PRAAx] positive N W)
    (hk : Γ ⊢[PRAAx] lt k N) : Γ ⊢[PRAAx] le one (entry W k) := by
  have all := Prf.allE k h
  simp only [positive, Fm.subst_imp, subst_lt, subst_le, subst_entry, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at all
  exact .impE all hk

theorem positive_prefix (N W k : PTm n) (h : Γ ⊢[PRAAx] positive N W)
    (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx] positive k W := by
  refine .allI (.impI ?_)
  have bounded : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift k) (Syn.shift N) := by
    simpa only [Fm.shift, subst_le, Syn.shift] using hk.shift
  have pos : Γ.map Fm.shift ⊢[PRAAx] positive (Syn.shift N) (Syn.shift W) := by
    simpa only [Fm.shift, subst_positive, Syn.shift] using h.shift
  exact positive_at _ _ _ pos.wk (lt_of_lt_of_le Prf.hyp0 bounded.wk)

theorem count_positive (N W : PTm n) (h : Γ ⊢[PRAAx] positive N W) :
    Γ ⊢[PRAAx] le one (count N W) := by
  refine prod_one_le_bounded widthBody W N (.allI (.impI ?_))
  have pos : Γ.map Fm.shift ⊢[PRAAx] positive (Syn.shift N) (Syn.shift W) := by
    simpa only [Fm.shift, subst_positive, Syn.shift] using h.shift
  have hp : lt (var 0) (Syn.shift N) :: Γ.map Fm.shift ⊢[PRAAx]
      le one (entry (Syn.shift W) (var 0)) :=
    positive_at (Syn.shift N) (Syn.shift W) (var 0) pos.wk Prf.hyp0
  simpa only [widthBody, inst2, subst_entry, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one] using hp

/-- Division below a positive divisor returns the original remainder. -/
theorem rem_small (i P : PTm n) (hP : Γ ⊢[PRAAx] le one P)
    (hi : Γ ⊢[PRAAx] lt i P) : Γ ⊢[PRAAx] rem i P ≐ i := by
  have split := natural_divmod i P hP
  exact Prf.andE₂ (euclid_unique ((Prf.andE₁ split).eqSymm.eqTrans
    (by ipra_ring : Γ ⊢[PRAAx] i ≐ P*zero+i)) (Prf.andE₂ split) hi)

theorem rem_one (i : PTm n) : Γ ⊢[PRAAx] rem i one ≐ zero := by
  have h : Γ ⊢[PRAAx] lt (rem i one) one := Prf.andE₂ (natural_divmod i one (le_refl one))
  exact (monus_zero _).eqSymm.eqTrans ((succ_monus_succ _ _).eqSymm.eqTrans h)

/-- Exact prefix decomposition; the arithmetic is proved from two actual
natural divmods and uniqueness, including either radix equal to one. -/
theorem rem_product (i P d : PTm n) (hP : Γ ⊢[PRAAx] le one P)
    (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] rem i (P*d) ≐ rem i P+P*rem (quo i P) d := by
  have first := natural_divmod i P hP
  have second := natural_divmod (quo i P) d hd
  have hp : Γ ⊢[PRAAx] le one (P*d) :=
    le_congr (one_mul one) (.eqRefl _) (le_mul_mono hP hd)
  have bound : Γ ⊢[PRAAx] lt (rem i P+P*rem (quo i P) d) (P*d) :=
    lt_congr (add_comm _ _) (mul_comm _ _) (MinkowskiResidues.range_step (Prf.andE₂ second) (Prf.andE₂ first))
  have reconstruct : Γ ⊢[PRAAx] i ≐ (P*d)*quo (quo i P) d+(rem i P+P*rem (quo i P) d) := by
    ipra_lc natEq (Prf.andE₁ first) + Groth.ι (Q.mk Γ P)*natEq (Prf.andE₁ second)
  have actual := natural_divmod i (P*d) hp
  exact Prf.andE₂ (euclid_unique ((Prf.andE₁ actual).eqSymm.eqTrans reconstruct) (Prf.andE₂ actual) bound)

theorem digit_bound (N W i k : PTm n) (h : Γ ⊢[PRAAx] positive N W)
    (hk : Γ ⊢[PRAAx] lt k N) : Γ ⊢[PRAAx] lt (digit W i k) (entry W k) :=
  Prf.andE₂ (natural_divmod _ _ (positive_at N W k h hk))

/-- The true count and each true digit reconstruct the next prefix remainder. -/
theorem prefix_remainder_step (N W i k : PTm n) (h : Γ ⊢[PRAAx] positive N W)
    (hk : Γ ⊢[PRAAx] lt k N) :
    Γ ⊢[PRAAx] rem i (count (succ k) W) ≐ rem i (count k W)+count k W*digit W i k :=
  (congrAp2 remF (.eqRefl _) (count_succ k W)).eqTrans
    (rem_product i (count k W) (entry W k) (count_positive k W (positive_prefix N W k h (le_of_lt hk)))
      (positive_at N W k h hk))

def digitsEqual (N W i j : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ (digit (Syn.shift W) (Syn.shift i) (var 0) ≐ digit (Syn.shift W) (Syn.shift j) (var 0)))

@[simp] theorem subst_digitsEqual {l : ℕ} (σ : Fin n → PTm l) (N W i j : PTm n) :
    (digitsEqual N W i j).subst σ = digitsEqual (Syn.subst σ N) (Syn.subst σ W) (Syn.subst σ i) (Syn.subst σ j) := by
  simp only [digitsEqual, Fm.subst_all, Fm.subst_imp, Fm.subst_eq, subst_lt, subst_digit,
    Syn.subst_var, Syn.up_zero, Syn.up_succ, Syn.subst_shift, Syn.shift_subst]

theorem digitsEqual_at (N W i j k : PTm n) (h : Γ ⊢[PRAAx] digitsEqual N W i j)
    (hk : Γ ⊢[PRAAx] lt k N) : Γ ⊢[PRAAx] digit W i k ≐ digit W j k := by
  have all := Prf.allE k h
  simp only [digitsEqual, Fm.subst_imp, Fm.subst_eq, subst_lt, subst_digit, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift] at all
  exact .impE all hk

/-- This induction is quantifier-free: its invariant is an implication between
natural order and one equality of actual prefix remainders. -/
theorem prefix_remainders_equal (N W i j : PTm n) (h : Γ ⊢[PRAAx] positive N W)
    (he : Γ ⊢[PRAAx] digitsEqual N W i j) :
    Γ ⊢[PRAAx] rem i (count N W) ≐ rem j (count N W) := by
  let P : Fm PTm (n + 1) :=
    rem (Syn.shift i) (count (var 0) (Syn.shift W)) ≐ rem (Syn.shift j) (count (var 0) (Syn.shift W))
  have atBound : Γ ⊢[PRAAx] P.subst (Syn.inst N) := by
    refine qfIndUpTo N trivial ?_ ?_
    · simp only [P, Fm.subst_eq, subst_ap2, subst_count, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift]
      exact ((congrAp2 remF (.eqRefl _) (count_zero W)).eqTrans (rem_one i)).eqTrans
        ((congrAp2 remF (.eqRefl _) (count_zero W)).eqTrans (rem_one j)).eqSymm
    · simp only [P, Fm.subst_eq, subst_ap2, subst_count, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift]
      refine .impI ?_
      let Δ := lt (var 0) (Syn.shift N) :: P :: Γ.map Fm.shift
      have pos : Γ.map Fm.shift ⊢[PRAAx] positive (Syn.shift N) (Syn.shift W) := by
        simpa only [Fm.shift, subst_positive, Syn.shift] using h.shift
      have eqs : Γ.map Fm.shift ⊢[PRAAx] digitsEqual (Syn.shift N) (Syn.shift W) (Syn.shift i) (Syn.shift j) := by
        simpa only [Fm.shift, subst_digitsEqual, Syn.shift] using he.shift
      have hk : Δ ⊢[PRAAx] lt (var 0) (Syn.shift N) := Prf.hyp0
      have ih : Δ ⊢[PRAAx] P := Prf.hyp1
      exact (prefix_remainder_step _ _ _ _ pos.wk.wk hk).eqTrans
        ((congrAdd ih (congrMul (.eqRefl _) (digitsEqual_at _ _ _ _ _ eqs.wk.wk hk))).eqTrans
          (prefix_remainder_step _ _ _ _ pos.wk.wk hk).eqSymm)
  simpa [P, rem] using atBound

/-- Injectivity of the actual mixed-radix digit program throughout its full
computed product range. The width-one and empty-dimension cases are included. -/
theorem index_injective (N W i j : PTm n) (h : Γ ⊢[PRAAx] positive N W)
    (hi : Γ ⊢[PRAAx] lt i (count N W)) (hj : Γ ⊢[PRAAx] lt j (count N W))
    (he : Γ ⊢[PRAAx] digitsEqual N W i j) : Γ ⊢[PRAAx] i ≐ j :=
  (rem_small i _ (count_positive N W h) hi).eqSymm.eqTrans
    ((prefix_remainders_equal N W i j h he).eqTrans (rem_small j _ (count_positive N W h) hj))

/-- Test actual digits; zero means a genuine natural digit difference. -/
def comparisonData (W i j : PTm n) : PTm n := pairT W (pairT i j)
def comparisonBody : PTm 2 := eqb
  (digit (fstT (var 1)) (fstT (sndT (var 1))) (var 0))
  (digit (fstT (var 1)) (sndT (sndT (var 1))) (var 0))
def differentIndex (N W i j : PTm n) : PTm n := Search.mu comparisonBody N (comparisonData W i j)

@[simp] theorem subst_comparisonData {l : ℕ} (σ : Fin n → PTm l) (W i j : PTm n) :
    Syn.subst σ (comparisonData W i j) = comparisonData (Syn.subst σ W) (Syn.subst σ i) (Syn.subst σ j) := by
  simp only [comparisonData, subst_pairT]
@[simp] theorem subst_differentIndex {l : ℕ} (σ : Fin n → PTm l) (N W i j : PTm n) :
    Syn.subst σ (differentIndex N W i j) = differentIndex (Syn.subst σ N) (Syn.subst σ W) (Syn.subst σ i) (Syn.subst σ j) := by
  simp only [differentIndex, Search.mu, subst_ap2, subst_comparisonData]

theorem comparisonBody_at (W i j k : PTm n) :
    Γ ⊢[PRAAx] inst2 comparisonBody k (comparisonData W i j) ≐ eqb (digit W i k) (digit W j k) := by
  have h := Prf.eqCongr (Γ := Γ) (eqb (digit (var 0) (var 1) (var 3)) (digit (var 0) (var 2) (var 3)) : PTm 4)
    (σ := ![fstT (comparisonData W i j),fstT (sndT (comparisonData W i j)),sndT (sndT (comparisonData W i j)),k])
    (σ' := ![W,i,j,k]) (fun a => by
      fin_cases a
      · exact fst_pair _ _
      · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
      · exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
      · exact .eqRefl _)
  simpa only [comparisonBody, inst2, subst_eqb, subst_digit, subst_fstT, subst_sndT,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using h

/-- A genuine unequal pair of indices makes the actual finite coordinate search
succeed. Its no-success branch would reconstruct equal prefix remainders. -/
theorem differentIndex_spec (N W i j : PTm n) (h : Γ ⊢[PRAAx] positive N W)
    (hi : Γ ⊢[PRAAx] lt i (count N W)) (hj : Γ ⊢[PRAAx] lt j (count N W))
    (hne : Γ ⊢[PRAAx] neg (i ≐ j)) :
    Γ ⊢[PRAAx] lt (differentIndex N W i j) N ⋏
      neg (digit W i (differentIndex N W i j) ≐ digit W j (differentIndex N W i j)) := by
  have spec := Search.search_spec (Γ := Γ) (f := comparisonBody) N zero (comparisonData W i j)
  have found : Γ ⊢[PRAAx] lt (differentIndex N W i j) N := by
    refine .orE (lt_or_eq_of_le (Prf.andE₁ spec)) Prf.hyp0 ?_
    let E := differentIndex N W i j ≐ N
    have equal : E :: Γ ⊢[PRAAx] digitsEqual N W i j := by
      refine .allI (.impI ?_)
      let Δ := lt (var 0) (Syn.shift N) :: (E :: Γ).map Fm.shift
      have nozero : Δ ⊢[PRAAx] neg (inst2 comparisonBody (var 0)
          (comparisonData (Syn.shift W) (Syn.shift i) (Syn.shift j)) ≐ zero) := by
        have searchEq : (E :: Γ).map Fm.shift ⊢[PRAAx]
            differentIndex (Syn.shift N) (Syn.shift W) (Syn.shift i) (Syn.shift j) ≐ Syn.shift N := by
          simpa only [E, Fm.shift, Fm.subst_eq, subst_differentIndex, Syn.shift] using
            (Prf.hyp0 : E :: Γ ⊢[PRAAx] E).shift
        exact Search.search_minimal (lt_congr (.eqRefl _) searchEq.wk.eqSymm Prf.hyp0)
      refine .orE (eq_or_ne (digit (Syn.shift W) (Syn.shift i) (var 0))
        (digit (Syn.shift W) (Syn.shift j) (var 0))) Prf.hyp0 ?_
      exact .botE _ (.impE nozero.wk ((comparisonBody_at _ _ _ _).eqTrans (eqb_of_ne Prf.hyp0)))
    exact .botE _ (.impE hne.wk (index_injective N W i j h.wk hi.wk hj.wk equal))
  have zero : Γ ⊢[PRAAx] eqb (digit W i (differentIndex N W i j)) (digit W j (differentIndex N W i j)) ≐ zero :=
    (comparisonBody_at _ _ _ _).eqSymm.eqTrans (.impE (Prf.andE₁ (Prf.andE₂ spec)) found)
  exact .andI found (.impI (succ_ne_zero ((eqb_of_eq Prf.hyp0).eqSymm.eqTrans zero.wk)))

theorem digit_bound_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (positive (var 0) (var 1) ⟶ lt (var 3) (var 0) ⟶
        lt (digit (var 1) (var 2) (var 3)) (entry (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (digit_bound _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem index_injective_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (positive (var 0) (var 1) ⟶ lt (var 2) (count (var 0) (var 1)) ⟶
        lt (var 3) (count (var 0) (var 1)) ⟶ digitsEqual (var 0) (var 1) (var 2) (var 3) ⟶
          (var 2 ≐ var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (index_injective _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiMixedRadix
