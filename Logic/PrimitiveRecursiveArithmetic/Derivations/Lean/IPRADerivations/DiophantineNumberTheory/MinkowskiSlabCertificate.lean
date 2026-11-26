import IPRADerivations.DiophantineNumberTheory.MinkowskiSlabLinearity
import IPRADerivations.DiophantineNumberTheory.MinkowskiCertificate
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# A numerical rational slab certificate for the actual Minkowski extractor

The input slabs are in lattice coordinates. Their rows are doubled by an
actual vector program before the interval checker is run on each original
box. Thus acceptance derives Inside for the original slabs, while symmetry
and midpoint closure are proved from their actual rational inequalities.
No geometric closure or Inside conclusion is an input assumption.

This provides the numerical slab theorem for supplied lattice-coordinate
rows. Forming those rows from a physical basis B and checking nonzero Bz
are separate physical-coordinate obligations.
-/

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192

namespace LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiSlabCertificate

open_ipra
open LeanProofs.IPRA.Analysis
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Analysis.RationalArithmetic (multiply represents multiply_guard multiply_value)
open LeanProofs.IPRA.Analysis.RationalRepresentations (represents_self represents_multiply)
open LeanProofs.IPRA.Analysis.RationalAlgebra (multiply_congr positive_product)
open LeanProofs.IPRA.Analysis.RationalFiniteSum (termwiseEq sum_ext)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry subst_sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiInside
  (double doubleVector double_value double_lookup subst_doubleVector boxContains insideGuarded)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiSlabInterval
  (dot productBody product_at facetsMember rowMember coordinateBox subst_dot subst_facetsMember)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiCenterVectors
  (holdsAt oppositeVector midpointVector subst_holdsAt)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiWellFormed
  (vectorGuard symmetricGuarded midpointGuarded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem multiply_double_balance (a b : PTm n) : Γ ⊢[PRAAx]
    multiply (double a) b ≐ multiply a (double b) := by
  have hl := represents_multiply (Γ := Γ) (double a) b _ _ _ _ (double_value a) (represents_self b)
  have hr := represents_multiply (Γ := Γ) a (double b) _ _ _ _ (represents_self a) (double_value b)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (multiply_guard _ _) (multiply_guard _ _) hl hr
    (RationalArithmetic.product_denominator_positive a b) (RationalArithmetic.product_denominator_positive a b)
  ipra_lc [RationalArithmetic.productDenominator]

theorem dot_double_balance (N c q : PTm n) : Γ ⊢[PRAAx]
    dot N (doubleVector N c) q ≐ dot N c (doubleVector N q) := by
  apply sum_ext
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have left := (product_at (Γ := Δ) (doubleVector (Syn.shift N) (Syn.shift c)) (Syn.shift q) (var 0)).eqTrans
    (multiply_congr (double_lookup _ _ _ Prf.hyp0) (.eqRefl _))
  have right := (product_at (Γ := Δ) (Syn.shift c) (doubleVector (Syn.shift N) (Syn.shift q)) (var 0)).eqTrans
    (multiply_congr (.eqRefl _) (double_lookup _ _ _ Prf.hyp0))
  simpa only [Δ,Syn.shift,subst_pairT,subst_doubleVector] using
    MinkowskiSlabLinearity.value_equal_of_code (left.eqTrans ((multiply_double_balance _ _).eqTrans right.eqSymm))

def doubledFacetBody : PTm 2 := pairT
  (doubleVector (fstT (var 1)) (fstT (entry (sndT (var 1)) (var 0))))
  (sndT (entry (sndT (var 1)) (var 0)))
def doubledFacets (N F : PTm n) : PTm n := sequence doubledFacetBody (length F) (pairT N F)

@[simp] theorem subst_doubledFacets {m : ℕ} (σ : Fin n → PTm m) (N F : PTm n) :
    Syn.subst σ (doubledFacets N F) = doubledFacets (Syn.subst σ N) (Syn.subst σ F) := by
  simp only [doubledFacets,subst_sequence,subst_length,subst_pairT]

theorem doubled_facets_length (N F : PTm n) : Γ ⊢[PRAAx] length (doubledFacets N F) ≐ length F := sequence_length _ _ _

theorem doubled_facet_at (N F j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length F)) : Γ ⊢[PRAAx]
    entry (doubledFacets N F) j ≐ pairT (doubleVector N (fstT (entry F j))) (sndT (entry F j)) := by
  have b := sequence_decode (Γ := Γ) doubledFacetBody (x := pairT N F) hj
  have e := Prf.eqCongr (Ax := PRAAx) (Γ := Γ)
    (pairT (doubleVector (var 0) (fstT (entry (var 1) (var 2)))) (sndT (entry (var 1) (var 2))) : PTm 3)
    (σ := ![fstT (pairT N F),sndT (pairT N F),j]) (σ' := ![N,F,j])
    (fun i => by fin_cases i; exact fst_pair _ _; exact snd_pair _ _; exact .eqRefl _)
  exact b.eqTrans (by simpa only [doubledFacetBody,inst2,subst_pairT,subst_doubleVector,subst_fstT,
    subst_sndT,subst_entry,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using e)

theorem doubled_containment (N F q : PTm n) (h : Γ ⊢[PRAAx] facetsMember N (doubledFacets N F) q) :
    Γ ⊢[PRAAx] facetsMember N F (doubleVector N q) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift F)) :: Γ.map Fm.shift
  have original : Δ ⊢[PRAAx] facetsMember (Syn.shift N) (doubledFacets (Syn.shift N) (Syn.shift F)) (Syn.shift q) := by
    simpa only [Δ,Fm.shift,subst_facetsMember,subst_doubledFacets,Syn.shift] using h.shift.wk
  have jrange : Δ ⊢[PRAAx] lt (var 0) (length (doubledFacets (Syn.shift N) (Syn.shift F))) :=
    lt_congr (.eqRefl _) (doubled_facets_length _ _).eqSymm Prf.hyp0
  have row := MinkowskiSlabLinearity.member_at _ _ _ (var 0) original jrange
  have read := doubled_facet_at (Γ := Δ) (Syn.shift N) (Syn.shift F) (var 0) Prf.hyp0
  have c := (congrFst read).eqTrans (fst_pair _ _)
  have b := (congrSnd read).eqTrans (snd_pair _ _)
  have rowDot : Δ ⊢[PRAAx] dot (Syn.shift N)
      (fstT (entry (doubledFacets (Syn.shift N) (Syn.shift F)) (var 0))) (Syn.shift q) ≐
        dot (Syn.shift N) (doubleVector (Syn.shift N) (fstT (entry (Syn.shift F) (var 0)))) (Syn.shift q) :=
    (MinkowskiSlabInterval.dot_program _ _ _).eqSymm.eqTrans
      ((congrAp3 MinkowskiSlabInterval.dotF (.eqRefl _) c (.eqRefl _)).eqTrans
        (MinkowskiSlabInterval.dot_program _ _ _))
  have dotEq := rowDot.eqTrans (dot_double_balance (Γ := Δ) (Syn.shift N)
    (fstT (entry (Syn.shift F) (var 0))) (Syn.shift q))
  simpa only [Δ,Syn.shift,subst_doubleVector,rowMember] using Prf.andI
    (RationalArgmin.rationalLE_congr (RationalAlgebra.negative_congr b) dotEq (Prf.andE₁ row))
    (RationalArgmin.rationalLE_congr dotEq b (Prf.andE₂ row))

def slabFormula : Fm PTm 2 := facetsMember (fstT (var 1)) (sndT (var 1)) (var 0)

theorem holds_formula (q x : PTm n) :
    holdsAt slabFormula q x = facetsMember (fstT x) (sndT x) q := by
  simp only [holdsAt,slabFormula,subst_facetsMember,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]

theorem holds_to_member (N F q : PTm n) (h : Γ ⊢[PRAAx] holdsAt slabFormula q (pairT N F)) :
    Γ ⊢[PRAAx] facetsMember N F q := by
  rw [holds_formula] at h
  have e := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (facetsMember (var 0) (var 1) (var 2) : Fm PTm 3)
    ![fstT (pairT N F),sndT (pairT N F),q] ![N,F,q]
    (fun i => by fin_cases i; exact fst_pair _ _; exact snd_pair _ _; exact .eqRefl _) (by simpa using h)
  simpa using e

theorem member_to_holds (N F q : PTm n) (h : Γ ⊢[PRAAx] facetsMember N F q) :
    Γ ⊢[PRAAx] holdsAt slabFormula q (pairT N F) := by
  rw [holds_formula]
  have e := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (facetsMember (var 0) (var 1) (var 2) : Fm PTm 3)
    ![N,F,q] ![fstT (pairT N F),sndT (pairT N F),q]
    (fun i => by fin_cases i; exact (fst_pair _ _).eqSymm; exact (snd_pair _ _).eqSymm; exact .eqRefl _) (by simpa using h)
  simpa using e

theorem slab_symmetric (N F : PTm n) : Γ ⊢[PRAAx] symmetricGuarded slabFormula N (pairT N F) := by
  refine .allI (.impI (.impI ?_))
  let Δ := holdsAt slabFormula (var 0) (Syn.shift (pairT N F)) ::
    vectorGuard (Syn.shift N) (var 0) :: Γ.map Fm.shift
  have original : Δ ⊢[PRAAx] holdsAt slabFormula (var 0) (Syn.shift (pairT N F)) := Prf.hyp0
  have member : Δ ⊢[PRAAx] facetsMember (Syn.shift N) (Syn.shift F) (var 0) :=
    holds_to_member _ _ _ (by simpa only [Syn.shift,subst_pairT] using original)
  simpa only [Δ,Syn.shift,subst_pairT] using
    member_to_holds _ _ _ (MinkowskiSlabLinearity.facets_opposite _ _ _ member)

theorem slab_midpoint (N F : PTm n) : Γ ⊢[PRAAx] midpointGuarded slabFormula N (pairT N F) := by
  refine .allI (.allI (.impI (.impI (.impI (.impI ?_)))))
  let Δ := holdsAt slabFormula (var 0) (Syn.shift (Syn.shift (pairT N F))) ::
    holdsAt slabFormula (var 1) (Syn.shift (Syn.shift (pairT N F))) ::
    vectorGuard (Syn.shift (Syn.shift N)) (var 0) ::
    vectorGuard (Syn.shift (Syn.shift N)) (var 1) :: (Γ.map Fm.shift).map Fm.shift
  have oq : Δ ⊢[PRAAx] holdsAt slabFormula (var 1) (Syn.shift (Syn.shift (pairT N F))) := Prf.hyp1
  have or : Δ ⊢[PRAAx] holdsAt slabFormula (var 0) (Syn.shift (Syn.shift (pairT N F))) := Prf.hyp0
  have first : Δ ⊢[PRAAx] facetsMember (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift F)) (var 1) :=
    holds_to_member _ _ _ (by simpa only [Syn.shift,subst_pairT] using oq)
  have second : Δ ⊢[PRAAx] facetsMember (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift F)) (var 0) :=
    holds_to_member _ _ _ (by simpa only [Syn.shift,subst_pairT] using or)
  simpa only [Δ,Syn.shift,subst_pairT] using
    member_to_holds _ _ _ (MinkowskiSlabLinearity.facets_midpoint _ _ _ _ first second)

def boxTests (N B F : PTm n) : Fm PTm n :=
  .all (lt (var 0) (length (Syn.shift B)) ⟶
    (MinkowskiSlabInterval.check (Syn.shift N) (doubledFacets (Syn.shift N) (Syn.shift F))
      (MinkowskiRationalBoxes.lowerRow (Syn.shift B) (var 0))
      (MinkowskiRationalBoxes.upperRow (Syn.shift B) (var 0)) ≐ one))

@[simp] theorem subst_boxTests {m : ℕ} (σ : Fin n → PTm m) (N B F : PTm n) :
    (boxTests N B F).subst σ = boxTests (Syn.subst σ N) (Syn.subst σ B) (Syn.subst σ F) := by
  simp only [boxTests,Fm.subst_all,Fm.subst_imp,Fm.subst_eq,subst_lt,subst_length,
    MinkowskiSlabInterval.subst_check,subst_doubledFacets,MinkowskiRationalBoxes.subst_lowerRow,
    MinkowskiRationalBoxes.subst_upperRow,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,
    Syn.subst_var,Syn.up_zero,Syn.up_succ,Syn.subst_shift,Syn.shift_subst]

theorem box_test_at (N B F j : PTm n) (h : Γ ⊢[PRAAx] boxTests N B F)
    (hj : Γ ⊢[PRAAx] lt j (length B)) : Γ ⊢[PRAAx]
    MinkowskiSlabInterval.check N (doubledFacets N F) (MinkowskiRationalBoxes.lowerRow B j)
      (MinkowskiRationalBoxes.upperRow B j) ≐ one := by
  have rule : Γ ⊢[PRAAx] lt j (length B) ⟶
      (MinkowskiSlabInterval.check N (doubledFacets N F) (MinkowskiRationalBoxes.lowerRow B j)
        (MinkowskiRationalBoxes.upperRow B j) ≐ one) := by
    simpa only [Fm.subst_imp,Fm.subst_eq,subst_lt,subst_length,MinkowskiSlabInterval.subst_check,
      subst_doubledFacets,MinkowskiRationalBoxes.subst_lowerRow,MinkowskiRationalBoxes.subst_upperRow,
      ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE j
  exact .impE rule hj

/-- Each genuine interval test derives the original doubled-coordinate
Inside assertion. Canonical query guards are retained from the source. -/
theorem inside_from_tests (N B F : PTm n) (h : Γ ⊢[PRAAx] boxTests N B F) :
    Γ ⊢[PRAAx] insideGuarded slabFormula N B (pairT N F) := by
  refine .allI (.impI (.allI (.impI (.impI ?_))))
  let NN := Syn.shift (Syn.shift N)
  let BB := Syn.shift (Syn.shift B)
  let FF := Syn.shift (Syn.shift F)
  let Δ := boxContains NN BB (var 1) (var 0) :: vectorGuard NN (var 0) ::
    lt (var 1) (length BB) :: (Γ.map Fm.shift).map Fm.shift
  have tests : Δ ⊢[PRAAx] boxTests NN BB FF := by
    simpa only [Δ,NN,BB,FF,Fm.shift,subst_boxTests,Syn.shift] using h.shift.shift.wk.wk.wk
  have accepted := box_test_at NN BB FF (var 1) tests hyp2
  have original : Δ ⊢[PRAAx] boxContains NN BB (var 1) (var 0) := Prf.hyp0
  have point : Δ ⊢[PRAAx] coordinateBox NN (MinkowskiRationalBoxes.lowerRow BB (var 1))
      (MinkowskiRationalBoxes.upperRow BB (var 1)) (var 0) := by
    simpa only [coordinateBox,boxContains,Syn.shift,MinkowskiRationalBoxes.subst_lowerRow,
      MinkowskiRationalBoxes.subst_upperRow] using original
  have body := doubled_containment NN FF (var 0) (MinkowskiSlabInterval.accepted_containment _ _ _ _ _ accepted point)
  simpa only [Δ,NN,BB,FF,List.map_cons,Fm.shift,subst_lt,subst_length,Syn.subst_var,Fin.succ_zero_eq_one,
    Syn.shift,subst_pairT] using member_to_holds NN FF _ body

open LeanProofs.IPRA.Foundations

def certificateInput (N B F : PTm n) : Fm PTm n :=
  (MinkowskiBoxChecker.check N B ≐ one) ⋏ boxTests N B F

def certificateSyntax (N B F : PTm n) : BoundedSyntax.BFm n :=
  .and (.eq (MinkowskiBoxChecker.check N B) one)
    (.all (length B) (.eq
      (MinkowskiSlabInterval.check (Syn.shift N) (doubledFacets (Syn.shift N) (Syn.shift F))
        (MinkowskiRationalBoxes.lowerRow (Syn.shift B) (var 0))
        (MinkowskiRationalBoxes.upperRow (Syn.shift B) (var 0))) one))

theorem certificate_formula (N B F : PTm n) :
    BoundedSyntax.formula (certificateSyntax N B F) = certificateInput N B F := by
  simp only [certificateSyntax,BoundedSyntax.formula,certificateInput,boxTests,Syn.shift,subst_length]

@[simp] theorem subst_certificateInput {m : ℕ} (σ : Fin n → PTm m) (N B F : PTm n) :
    (certificateInput N B F).subst σ = certificateInput (Syn.subst σ N) (Syn.subst σ B) (Syn.subst σ F) := by
  simp only [certificateInput,Fm.subst_and,Fm.subst_eq,MinkowskiBoxChecker.check,subst_ap2,subst_boxTests,
    ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ]

def checkerF : PR 3 := BoundedSyntax.bitF (certificateSyntax (var 0) (var 1) (var 2) : BoundedSyntax.BFm 3)
def check (N B F : PTm n) : PTm n := ap3 checkerF N B F

@[simp] theorem subst_check {m : ℕ} (σ : Fin n → PTm m) (N B F : PTm n) :
    Syn.subst σ (check N B F) = check (Syn.subst σ N) (Syn.subst σ B) (Syn.subst σ F) := subst_ap3 _ _ _ _ _

theorem checker_program (N B F : PTm n) : Γ ⊢[PRAAx] check N B F ≐
    BoundedSyntax.bit (certificateSyntax (var 0) (var 1) (var 2) : BoundedSyntax.BFm 3) ![N,B,F] :=
  BoundedSyntax.program_correct _ _

theorem checker_reflection (N B F : PTm n) : Γ ⊢[PRAAx] Fm.iff (check N B F ≐ one) (certificateInput N B F) := by
  have r := BoundedSyntax.bounded_reflection (Γ := Γ)
    (certificateSyntax (var 0) (var 1) (var 2) : BoundedSyntax.BFm 3) ![N,B,F]
  rw [certificate_formula] at r
  simp only [subst_certificateInput,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] at r
  have p := checker_program (Γ := Γ) N B F
  exact .iffI (.impI (r.wk.iffMp (p.wk.eqSymm.eqTrans Prf.hyp0)))
    (.impI (p.wk.eqTrans (r.wk.iffMpr Prf.hyp0)))

theorem checker_boolean (N B F : PTm n) : Γ ⊢[PRAAx] (check N B F ≐ zero) ⋎ (check N B F ≐ one) := by
  have p := checker_program (Γ := Γ) N B F
  exact .orE (BoundedSyntax.bit_cases (certificateSyntax (var 0) (var 1) (var 2) : BoundedSyntax.BFm 3) ![N,B,F])
    (.orI₁ (p.wk.eqTrans Prf.hyp0)) (.orI₂ (p.wk.eqTrans Prf.hyp0))

/-- Original numerical box validity and the computed doubled-row interval
tests supply every geometric contract of the actual extractor. -/
theorem accepted_extractor (N B F : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] check N B F ≐ one) :
    Γ ⊢[PRAAx] MinkowskiCertificate.success slabFormula N B (pairT N F) := by
  have input := (checker_reflection N B F).iffMp h
  exact MinkowskiCertificate.certificate_correct slabFormula N B (pairT N F) hN
    (Prf.andE₁ input) (inside_from_tests N B F (Prf.andE₂ input)) (slab_symmetric N F) (slab_midpoint N F)

theorem accepted_membership (N B F : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] check N B F ≐ one) : Γ ⊢[PRAAx]
    facetsMember N F (MinkowskiCenterVectors.integerVector N (MinkowskiCertificate.integerOutput N B)) := by
  have out := accepted_extractor N B F hN h
  exact holds_to_member _ _ _ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ out))))

theorem slab_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ check (var 0) (var 1) (var 2) ≐ one ⟶
      (MinkowskiCertificate.success slabFormula (var 0) (var 1) (pairT (var 0) (var 2)) ⋏
        facetsMember (var 0) (var 2) (MinkowskiCenterVectors.integerVector (var 0)
          (MinkowskiCertificate.integerOutput (var 0) (var 1))))) :=
  closeUniv 3 (.impI (.impI (.andI (accepted_extractor _ _ _ Prf.hyp1 Prf.hyp0)
    (accepted_membership _ _ _ Prf.hyp1 Prf.hyp0))))

theorem slab_certificate_checker_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (Fm.iff (check (var 0) (var 1) (var 2) ≐ one) (certificateInput (var 0) (var 1) (var 2)) ⋏
      ((check (var 0) (var 1) (var 2) ≐ zero) ⋎ (check (var 0) (var 1) (var 2) ≐ one))) :=
  closeUniv 3 (.andI (checker_reflection _ _ _) (checker_boolean _ _ _))

theorem slab_inside_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (boxTests (var 0) (var 1) (var 2) ⟶ insideGuarded slabFormula (var 0) (var 1) (pairT (var 0) (var 2))) :=
  closeUniv 3 (.impI (inside_from_tests _ _ _ Prf.hyp0))

theorem slab_closure_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (symmetricGuarded slabFormula (var 0) (pairT (var 0) (var 1)) ⋏
      midpointGuarded slabFormula (var 0) (pairT (var 0) (var 1))) :=
  closeUniv 2 (.andI (slab_symmetric _ _) (slab_midpoint _ _))

def doubledFacetsF : PR 2 := PTm.toPR (doubledFacets (var 0) (var 1))

theorem doubled_facets_program (N F : PTm n) : Γ ⊢[PRAAx]
    ap2 doubledFacetsF N F ≐ doubledFacets N F := by
  simpa only [doubledFacetsF,ap2,subst_doubledFacets,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one] using toPR_eq (Γ := Γ) (doubledFacets (var 0) (var 1) : PTm 2) ![N,F]

theorem slab_certificate_programs_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((check (var 0) (var 1) (var 2) ≐
      BoundedSyntax.bit (certificateSyntax (var 0) (var 1) (var 2) : BoundedSyntax.BFm 3)
        ![var 0,var 1,var 2]) ⋏
      (ap2 doubledFacetsF (var 0) (var 2) ≐ doubledFacets (var 0) (var 2))) :=
  closeUniv 3 (.andI (checker_program _ _ _) (doubled_facets_program _ _))

end LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiSlabCertificate
