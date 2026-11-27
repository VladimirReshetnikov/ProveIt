import IPRADerivations.Core.SumOrder
import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.Foundations.MasterCertificate
import IPRADerivations.Foundations.SequenceComposition

/-!
# Counting actual nonzero pivot tags and selecting a free column

Zero is the skipped-column tag and every positive tag marks a pivot.
The actual bounded sum counts nonzero tags in an arbitrary numerical
history. Its deficit derives a genuine zero tag and the actual least
free-column scan, with the numerical bound as its no-hit default.
No history validity, rank profile or successful-search law is input.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalPivotHistoryCount

open_ipra
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open LeanProofs.IPRA.Foundations.BoundedReflection (eqb_cases)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def tagBody : PTm 2 := entry (var 1) (var 0)
def markedBit (H j : PTm n) : PTm n := monus one (eqb (entry H j) zero)
def markedBody : PTm 2 := markedBit (var 1) (var 0)
def zeroBody : PTm 2 := eqb (entry (var 1) (var 0)) zero
def count (H N : PTm n) : PTm n := ap2 (sumF markedBody) N H
def zeroCount (H N : PTm n) : PTm n := ap2 (sumF zeroBody) N H
def free (H N : PTm n) : PTm n := Search.mu tagBody N H
def allMarked (H N : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift N) ⟶ neg (entry (Syn.shift H) (var 0) ≐ zero))

ipra_subst markedBit
ipra_subst count
ipra_subst zeroCount
ipra_subst free
ipra_subst allMarked [Syn.subst_shift, Syn.shift_subst]

theorem tag_body_at (H j : PTm n) : inst2 tagBody j H = entry H j := by simp [tagBody,inst2]
theorem marked_body_at (H j : PTm n) : inst2 markedBody j H = markedBit H j := by simp [markedBody,inst2]
theorem zero_body_at (H j : PTm n) : inst2 zeroBody j H = eqb (entry H j) zero := by simp [zeroBody,inst2]

theorem marked_zero (H j : PTm n) (h : Γ ⊢[PRAAx] entry H j ≐ zero) : Γ ⊢[PRAAx] markedBit H j ≐ zero :=
  (congrMonus (.eqRefl _) (eqb_of_eq h)).eqTrans (monus_self _)
theorem marked_one (H j : PTm n) (h : Γ ⊢[PRAAx] neg (entry H j ≐ zero)) : Γ ⊢[PRAAx] markedBit H j ≐ one :=
  (congrMonus (.eqRefl _) (eqb_of_ne h)).eqTrans (monus_zero _)
theorem marked_cases (H j : PTm n) : Γ ⊢[PRAAx] (markedBit H j ≐ zero) ⋎ (markedBit H j ≐ one) := by
  refine .orE (eq_or_ne (entry H j) zero) (.orI₁ (marked_zero _ _ Prf.hyp0)) (.orI₂ (marked_one _ _ Prf.hyp0))
theorem marked_bound (H j : PTm n) : Γ ⊢[PRAAx] le (markedBit H j) one := by
  refine .orE (marked_cases H j) ?_ ?_
  · exact le_congr Prf.hyp0.eqSymm (.eqRefl _) (zero_le _)
  · exact le_congr Prf.hyp0.eqSymm (.eqRefl _) (le_refl _)
theorem bit_partition (H j : PTm n) : Γ ⊢[PRAAx] markedBit H j + eqb (entry H j) zero ≐ one := by
  refine .orE (eq_or_ne (entry H j) zero) ?_ ?_
  · exact (congrAdd (marked_zero _ _ Prf.hyp0) (eqb_of_eq Prf.hyp0)).eqTrans (zero_add _)
  · exact (congrAdd (marked_one _ _ Prf.hyp0) (eqb_of_ne Prf.hyp0)).eqTrans (add_zero _)

theorem count_zero (H : PTm n) : Γ ⊢[PRAAx] count H zero ≐ zero := sum_zero _ _
theorem zeroCount_zero (H : PTm n) : Γ ⊢[PRAAx] zeroCount H zero ≐ zero := sum_zero _ _
theorem count_succ (H N : PTm n) : Γ ⊢[PRAAx] count H (succ N) ≐ count H N + markedBit H N := by
  simpa only [count,marked_body_at] using sum_succ' (Γ := Γ) markedBody N H
theorem zeroCount_succ (H N : PTm n) : Γ ⊢[PRAAx] zeroCount H (succ N) ≐ zeroCount H N + eqb (entry H N) zero := by
  simpa only [zeroCount,zero_body_at] using sum_succ' (Γ := Γ) zeroBody N H

theorem sum_units (N H : PTm n) : Γ ⊢[PRAAx] ap2 (sumF (one : PTm 2)) N H ≐ N := by
  have all : Γ ⊢[PRAAx] .all (ap2 (sumF (one : PTm 2)) (var 0) (Syn.shift H) ≐ var 0) := by
    ipra_qfind [subst_ap2]
    · exact sum_zero _ _
    · have s := sum_succ' (Γ := (ap2 (sumF (one : PTm 2)) (var 0) (Syn.shift H) ≐ var 0) :: Γ.map Fm.shift)
        (one : PTm 2) (var 0) (Syn.shift H)
      have e := (congrAdd (Prf.hyp0 : (ap2 (sumF (one : PTm 2)) (var 0) (Syn.shift H) ≐ var 0) :: Γ.map Fm.shift ⊢[PRAAx] _)
        (.eqRefl one)).eqTrans (succ_eq_add_one (var 0)).eqSymm
      exact s.eqTrans (by simpa [inst2] using e)
  simpa only [Fm.subst_eq,subst_ap2,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem count_bound (H N : PTm n) : Γ ⊢[PRAAx] le (count H N) N := by
  have h : Γ ⊢[PRAAx] le (count H N) (ap2 (sumF (one : PTm 2)) N H) := by
    refine sum_le_params markedBody (one : PTm 2) H H N (.allI (.impI ?_))
    simpa [markedBody,inst2] using
      marked_bound (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) (Syn.shift H) (var 0)
  exact le_congr (.eqRefl _) (sum_units N H) h

theorem count_partition (H N : PTm n) : Γ ⊢[PRAAx] count H N + zeroCount H N ≐ N := by
  have pointwise : Γ ⊢[PRAAx] ap2 (sumF (addBody markedBody zeroBody)) N H ≐ ap2 (sumF (one : PTm 2)) N H := by
    refine LeanProofs.IPRA.sum_congr_bounded (addBody markedBody zeroBody) (one : PTm 2) H H N (.allI (.impI ?_))
    simpa [addBody,markedBody,zeroBody,inst2] using bit_partition (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) (Syn.shift H) (var 0)
  exact (sum_add markedBody zeroBody N H).eqSymm.eqTrans (pointwise.eqTrans (sum_units N H))

theorem count_congr_bounded (H K N : PTm n) (h : Γ ⊢[PRAAx] .all
    (lt (var 0) (Syn.shift N) ⟶ (entry (Syn.shift H) (var 0) ≐ entry (Syn.shift K) (var 0)))) :
    Γ ⊢[PRAAx] count H N ≐ count K N := by
  refine LeanProofs.IPRA.sum_congr_bounded markedBody markedBody H K N (.allI (.impI ?_))
  simpa only [marked_body_at,markedBit] using congrMonus (.eqRefl _) (AnalyticNumberTheory.Euler.congrEqb
    (.impE h.allOpen.wk Prf.hyp0) (.eqRefl zero))

theorem allMarked_at (H N j : PTm n) (h : Γ ⊢[PRAAx] allMarked H N) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] neg (entry H j ≐ zero) := by
  have rule : Γ ⊢[PRAAx] lt j N ⟶ neg (entry H j ≐ zero) := by simpa [allMarked] using h.allE j
  exact .impE rule hj
theorem allMarked_count (H N : PTm n) (h : Γ ⊢[PRAAx] allMarked H N) : Γ ⊢[PRAAx] count H N ≐ N := by
  have s : Γ ⊢[PRAAx] count H N ≐ ap2 (sumF (one : PTm 2)) N H := by
    refine LeanProofs.IPRA.sum_congr_bounded markedBody (one : PTm 2) H H N (.allI (.impI ?_))
    simpa [markedBody,inst2] using
      marked_one (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) (Syn.shift H) (var 0) (.impE h.allOpen.wk Prf.hyp0)
  exact s.eqTrans (sum_units N H)

theorem free_bound (H N : PTm n) : Γ ⊢[PRAAx] le (free H N) N := .andE₁ (Search.search_spec N zero H)
theorem free_entry (H N : PTm n) (h : Γ ⊢[PRAAx] lt (free H N) N) : Γ ⊢[PRAAx] entry H (free H N) ≐ zero := by
  simpa [free,tagBody,inst2] using Prf.impE (Prf.andE₁ (Prf.andE₂ (Search.search_spec (f := tagBody) N zero H))) h
theorem before_free (H N j : PTm n) (hj : Γ ⊢[PRAAx] lt j (free H N)) : Γ ⊢[PRAAx] neg (entry H j ≐ zero) := by
  simpa only [tag_body_at] using Search.search_minimal (f := tagBody) hj
theorem free_least (H N j : PTm n) (hj : Γ ⊢[PRAAx] entry H j ≐ zero) : Γ ⊢[PRAAx] le (free H N) j := by
  refine .orE (lt_or_le j (free H N)) ?_ Prf.hyp0
  exact .botE _ (.impE (before_free H N j Prf.hyp0) hj.wk)

theorem free_correct (H N : PTm n) (h : Γ ⊢[PRAAx] lt (count H N) N) : Γ ⊢[PRAAx]
    lt (free H N) N ⋏ (entry H (free H N) ≐ zero) := by
  have bound : Γ ⊢[PRAAx] lt (free H N) N := by
    refine .orE (lt_or_eq_of_le (free_bound H N)) Prf.hyp0 ?_
    have all : (free H N ≐ N) :: Γ ⊢[PRAAx] allMarked H N := by
      refine .allI (.impI ?_)
      have hs : ((free H N ≐ N) :: Γ).map Fm.shift ⊢[PRAAx] free (Syn.shift H) (Syn.shift N) ≐ Syn.shift N := by
        simpa only [Fm.shift,Fm.subst_eq,subst_free,Syn.shift] using (Prf.hyp0 : (free H N ≐ N) :: Γ ⊢[PRAAx] _).shift
      exact before_free _ _ _ (lt_congr (.eqRefl _) hs.wk.eqSymm Prf.hyp0)
    exact .botE _ (lt_irrefl N _ (lt_congr (allMarked_count H N all) (.eqRefl _) h.wk))
  exact .andI bound (free_entry H N bound)

theorem zeroCount_positive (H N j : PTm n) (hj : Γ ⊢[PRAAx] lt j N)
    (hTag : Γ ⊢[PRAAx] entry H j ≐ zero) : Γ ⊢[PRAAx] le one (zeroCount H N) := by
  have term : Γ ⊢[PRAAx] le (eqb (entry H j) zero) (zeroCount H N) := by
    simpa only [zero_body_at,zeroCount] using term_le_sum (Γ := Γ) zeroBody (x := H) hj
  exact le_congr (eqb_of_eq hTag) (.eqRefl _) term

theorem count_lt_of_zero (H N j : PTm n) (hj : Γ ⊢[PRAAx] lt j N)
    (hTag : Γ ⊢[PRAAx] entry H j ≐ zero) : Γ ⊢[PRAAx] lt (count H N) N :=
  le_congr (succ_eq_add_one _).eqSymm (count_partition H N)
    (add_le_add₂ (le_refl _) (zeroCount_positive H N j hj hTag))

theorem free_success_iff (H N : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (lt (count H N) N) (lt (free H N) N) :=
  .andI (.impI (.andE₁ (free_correct H N Prf.hyp0)))
    (.impI (count_lt_of_zero H N (free H N) Prf.hyp0 (free_entry H N Prf.hyp0)))

theorem free_found (H N j : PTm n) (hj : Γ ⊢[PRAAx] lt j N)
    (hTag : Γ ⊢[PRAAx] entry H j ≐ zero) : Γ ⊢[PRAAx]
    lt (free H N) N ⋏ ((entry H (free H N) ≐ zero) ⋏ le (free H N) j) :=
  .andI (.andE₁ (free_correct H N (count_lt_of_zero H N j hj hTag)))
    (.andI (.andE₂ (free_correct H N (count_lt_of_zero H N j hj hTag))) (free_least H N j hTag))

theorem free_default (H N : PTm n) (h : Γ ⊢[PRAAx] count H N ≐ N) : Γ ⊢[PRAAx] free H N ≐ N := by
  refine .orE (lt_or_eq_of_le (free_bound H N)) ?_ Prf.hyp0
  exact .botE _ (lt_irrefl N _ (lt_congr h.wk (.eqRefl _)
    (count_lt_of_zero H N (free H N) Prf.hyp0 (free_entry H N Prf.hyp0))))

theorem before_free_marked (H N j : PTm n) (hj : Γ ⊢[PRAAx] lt j (free H N)) :
    Γ ⊢[PRAAx] markedBit H j ≐ one := marked_one H j (before_free H N j hj)

theorem count_zero_of_tags (H N : PTm n) (h : Γ ⊢[PRAAx] .all
    (lt (var 0) (Syn.shift N) ⟶ (entry (Syn.shift H) (var 0) ≐ zero))) :
    Γ ⊢[PRAAx] count H N ≐ zero := by
  refine sum_zero_of_bounded markedBody H N (.allI (.impI ?_))
  simpa [markedBody,inst2] using marked_zero (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift)
    (Syn.shift H) (var 0) (.impE h.allOpen.wk Prf.hyp0)

theorem count_succ_zero (H N : PTm n) (h : Γ ⊢[PRAAx] entry H N ≐ zero) :
    Γ ⊢[PRAAx] count H (succ N) ≐ count H N :=
  (count_succ H N).eqTrans ((congrAdd (.eqRefl _) (marked_zero H N h)).eqTrans (add_zero _))
theorem count_succ_marked (H N : PTm n) (h : Γ ⊢[PRAAx] neg (entry H N ≐ zero)) :
    Γ ⊢[PRAAx] count H (succ N) ≐ succ (count H N) :=
  (count_succ H N).eqTrans ((congrAdd (.eqRefl _) (marked_one H N h)).eqTrans (succ_eq_add_one _).eqSymm)

theorem count_congr {H K N M : PTm n} (hH : Γ ⊢[PRAAx] H ≐ K) (hN : Γ ⊢[PRAAx] N ≐ M) :
    Γ ⊢[PRAAx] count H N ≐ count K M := congrAp2 (sumF markedBody) hN hH
theorem free_congr {H K N M : PTm n} (hH : Γ ⊢[PRAAx] H ≐ K) (hN : Γ ⊢[PRAAx] N ≐ M) :
    Γ ⊢[PRAAx] free H N ≐ free K M := congrAp2 (Search.muF tagBody) hN hH
theorem free_zero (H : PTm n) : Γ ⊢[PRAAx] free H zero ≐ zero := Search.mu_zero H
theorem full_zero_count (H N : PTm n) (h : Γ ⊢[PRAAx] count H N ≐ N) :
    Γ ⊢[PRAAx] zeroCount H N ≐ zero := by
  ipra_lc natEq ((congrAdd h (.eqRefl _)).eqSymm.eqTrans (count_partition H N))

def output (H N : PTm n) : PTm n := pairT (count H N)
  (pairT (free H N) (pairT (entry H (free H N)) (zeroCount H N)))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (H N : PTm n) : PTm n := app outputF ![H,N]
def outputField (p : PTm n) (i : Fin 4) : PTm n :=
  ![fstT p,fstT (sndT p),fstT (sndT (sndT p)),sndT (sndT (sndT p))] i

ipra_subst output
ipra_subst run
@[simp] theorem subst_outputField {k : ℕ} (σ : Fin n → PTm k) (p : PTm n) (i : Fin 4) :
    Syn.subst σ (outputField p i) = outputField (Syn.subst σ p) i :=
  subst_pairVectorField σ 3 p i

theorem program_at (H N : PTm n) : Γ ⊢[PRAAx] run H N ≐ output H N := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![H,N]
theorem output_fields (H N : PTm n) (i : Fin 4) : Γ ⊢[PRAAx]
    outputField (output H N) i ≐ ![count H N,free H N,entry H (free H N),zeroCount H N] i :=
  pairVectorField_eq 3 ![count H N,free H N,entry H (free H N),zeroCount H N] (.eqRefl _) i
theorem returned_fields (H N : PTm n) (i : Fin 4) : Γ ⊢[PRAAx]
    outputField (run H N) i ≐ ![count H N,free H N,entry H (free H N),zeroCount H N] i :=
  pairVectorField_eq 3 _ (program_at H N) i
theorem returned_count_bound (H N : PTm n) : Γ ⊢[PRAAx] le (outputField (run H N) 0) N :=
  le_congr (returned_fields H N 0).eqSymm (.eqRefl _) (count_bound H N)
theorem returned_free_bound (H N : PTm n) : Γ ⊢[PRAAx] le (outputField (run H N) 1) N :=
  le_congr (returned_fields H N 1).eqSymm (.eqRefl _) (free_bound H N)
theorem returned_free_correct (H N : PTm n) (h : Γ ⊢[PRAAx] lt (count H N) N) : Γ ⊢[PRAAx]
    lt (outputField (run H N) 1) N ⋏ (entry H (outputField (run H N) 1) ≐ zero) :=
  .andI (lt_congr (returned_fields H N 1).eqSymm (.eqRefl _) (.andE₁ (free_correct H N h)))
    ((entry_congr (.eqRefl _) (returned_fields H N 1)).eqTrans (.andE₂ (free_correct H N h)))
theorem returned_tag_zero (H N : PTm n) (h : Γ ⊢[PRAAx] lt (count H N) N) :
    Γ ⊢[PRAAx] outputField (run H N) 2 ≐ zero :=
  (returned_fields H N 2).eqTrans (.andE₂ (free_correct H N h))

theorem actual_count_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (count (var 0) (var 1)) (var 1)) := closeUniv 2 (count_bound _ _)
theorem actual_count_partition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (count (var 0) (var 1) + zeroCount (var 0) (var 1) ≐ var 1) := closeUniv 2 (count_partition _ _)
theorem actual_free_column_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (count (var 0) (var 1)) (var 1) ⟶
      lt (free (var 0) (var 1)) (var 1) ⋏ (entry (var 0) (free (var 0) (var 1)) ≐ zero)) :=
  closeUniv 2 (.impI (free_correct _ _ Prf.hyp0))
theorem actual_free_least_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((entry (var 0) (var 2) ≐ zero) ⟶ le (free (var 0) (var 1)) (var 2)) :=
  closeUniv 3 (.impI (free_least _ _ _ Prf.hyp0))
theorem actual_before_free_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (free (var 0) (var 1)) ⟶ neg (entry (var 0) (var 2) ≐ zero)) :=
  closeUniv 3 (.impI (before_free _ _ _ Prf.hyp0))
theorem actual_zero_implies_deficit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (var 1) ⟶ (entry (var 0) (var 2) ≐ zero) ⟶ lt (count (var 0) (var 1)) (var 1)) :=
  closeUniv 3 (.impI (.impI (count_lt_of_zero _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_search_default_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((count (var 0) (var 1) ≐ var 1) ⟶ (free (var 0) (var 1) ≐ var 1)) :=
  closeUniv 2 (.impI (free_default _ _ Prf.hyp0))
theorem actual_count_succ_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (count (var 0) (succ (var 1)) ≐ count (var 0) (var 1) + markedBit (var 0) (var 1)) :=
  closeUniv 2 (count_succ _ _)
theorem actual_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)
theorem actual_returned_free_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (count (var 0) (var 1)) (var 1) ⟶
      lt (outputField (run (var 0) (var 1)) 1) (var 1) ⋏
        (entry (var 0) (outputField (run (var 0) (var 1)) 1) ≐ zero)) :=
  closeUniv 2 (.impI (returned_free_correct _ _ Prf.hyp0))
theorem actual_returned_tag_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (count (var 0) (var 1)) (var 1) ⟶ (outputField (run (var 0) (var 1)) 2 ≐ zero)) :=
  closeUniv 2 (.impI (returned_tag_zero _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalPivotHistoryCount
