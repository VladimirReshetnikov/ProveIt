import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalIdentities.RationalFiniteSum
import IPRADerivations.Foundations.BoundedSyntax
import IPRADerivations.Core.Header

/-!
# The actual rational slab interval checker

For the numerical specialization following equation (slab) in Minkowski
paper 01, the supplied lattice-coordinate row is alpha = 2 a B. Actual
signed rational products, min/max selectors and finite sum programs compute
its box interval. Coordinate containment implies these computed dot-product
bounds. A fixed PR4 checker tests the interval against every supplied facet
bound and therefore proves containment for every point of the box.

Dimension, facets, coefficients, endpoints, bounds and query vectors are
internal numerical inputs. Coordinates use the total sequence decoder in
the first N positions. This does not construct alpha from a physical basis,
or prove the separate doubled-coordinate geometric transport.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiSlabInterval

open_ipra exports
open LeanProofs.IPRA.Foundations
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.Analysis.RationalArgmin (left rationalLE)
open LeanProofs.IPRA.Analysis.RationalArithmetic
  (multiply minimum maximum negative multiplyF minimumF maximumF)
open LeanProofs.IPRA.Analysis.RationalFiniteSum (term sum termwiseLE sum_monotone)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Runtime data are the coefficient vector paired with the query vector. -/
def productBody : PTm 2 := ap2 multiplyF
  (entry (fstT (var 1)) (var 0)) (entry (sndT (var 1)) (var 0))

/-- Runtime data are `(coefficients,(lower endpoints,upper endpoints))`. -/
def lowerBody : PTm 2 := ap2 minimumF
  (ap2 multiplyF (entry (fstT (var 1)) (var 0)) (entry (fstT (sndT (var 1))) (var 0)))
  (ap2 multiplyF (entry (fstT (var 1)) (var 0)) (entry (sndT (sndT (var 1))) (var 0)))
def upperBody : PTm 2 := ap2 maximumF
  (ap2 multiplyF (entry (fstT (var 1)) (var 0)) (entry (fstT (sndT (var 1))) (var 0)))
  (ap2 multiplyF (entry (fstT (var 1)) (var 0)) (entry (sndT (sndT (var 1))) (var 0)))

def dot (N c q : PTm n) : PTm n := sum productBody N (pairT c q)
def lowerSum (N c l u : PTm n) : PTm n := sum lowerBody N (pairT c (pairT l u))
def upperSum (N c l u : PTm n) : PTm n := sum upperBody N (pairT c (pairT l u))

@[simp] theorem subst_dot {k : ℕ} (σ : Fin n → PTm k) (N c q : PTm n) :
    Syn.subst σ (dot N c q) = dot (Syn.subst σ N) (Syn.subst σ c) (Syn.subst σ q) := by
  simp only [dot,Analysis.RationalFiniteSum.subst_sum,subst_pairT]
@[simp] theorem subst_lowerSum {k : ℕ} (σ : Fin n → PTm k) (N c l u : PTm n) :
    Syn.subst σ (lowerSum N c l u) = lowerSum (Syn.subst σ N) (Syn.subst σ c) (Syn.subst σ l) (Syn.subst σ u) := by
  simp only [lowerSum,Analysis.RationalFiniteSum.subst_sum,subst_pairT]
@[simp] theorem subst_upperSum {k : ℕ} (σ : Fin n → PTm k) (N c l u : PTm n) :
    Syn.subst σ (upperSum N c l u) = upperSum (Syn.subst σ N) (Syn.subst σ c) (Syn.subst σ l) (Syn.subst σ u) := by
  simp only [upperSum,Analysis.RationalFiniteSum.subst_sum,subst_pairT]

theorem product_at (c q i : PTm n) : Γ ⊢[PRAAx] term productBody i (pairT c q) ≐
    multiply (entry c i) (entry q i) := by
  change Γ ⊢[PRAAx] inst2 productBody i (pairT c q) ≐ _
  simp only [productBody,inst2,subst_ap2,subst_entry,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact (congrAp2 multiplyF (entry_congr (fst_pair _ _) (.eqRefl _))
    (entry_congr (snd_pair _ _) (.eqRefl _))).eqTrans (Analysis.RationalArithmetic.multiply_at _ _)

private theorem endpointProduct_at (c l u i : PTm n) : Γ ⊢[PRAAx]
    ap2 multiplyF (entry (fstT (pairT c (pairT l u))) i)
      (entry (fstT (sndT (pairT c (pairT l u)))) i) ≐ multiply (entry c i) (entry l i) :=
  (congrAp2 multiplyF (entry_congr (fst_pair _ _) (.eqRefl _))
    (entry_congr ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)) (.eqRefl _))).eqTrans
      (Analysis.RationalArithmetic.multiply_at _ _)
private theorem endpointProduct_upper_at (c l u i : PTm n) : Γ ⊢[PRAAx]
    ap2 multiplyF (entry (fstT (pairT c (pairT l u))) i)
      (entry (sndT (sndT (pairT c (pairT l u)))) i) ≐ multiply (entry c i) (entry u i) :=
  (congrAp2 multiplyF (entry_congr (fst_pair _ _) (.eqRefl _))
    (entry_congr ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)) (.eqRefl _))).eqTrans
      (Analysis.RationalArithmetic.multiply_at _ _)

theorem lower_at (c l u i : PTm n) : Γ ⊢[PRAAx] term lowerBody i (pairT c (pairT l u)) ≐
    minimum (multiply (entry c i) (entry l i)) (multiply (entry c i) (entry u i)) := by
  change Γ ⊢[PRAAx] inst2 lowerBody i (pairT c (pairT l u)) ≐ _
  simp only [lowerBody,inst2,subst_ap2,subst_entry,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact (congrAp2 minimumF (endpointProduct_at c l u i) (endpointProduct_upper_at c l u i)).eqTrans
    (Analysis.RationalArithmetic.minimum_at _ _)

theorem upper_at (c l u i : PTm n) : Γ ⊢[PRAAx] term upperBody i (pairT c (pairT l u)) ≐
    maximum (multiply (entry c i) (entry l i)) (multiply (entry c i) (entry u i)) := by
  change Γ ⊢[PRAAx] inst2 upperBody i (pairT c (pairT l u)) ≐ _
  simp only [upperBody,inst2,subst_ap2,subst_entry,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact (congrAp2 maximumF (endpointProduct_at c l u i) (endpointProduct_upper_at c l u i)).eqTrans
    (Analysis.RationalArithmetic.maximum_at _ _)

/-- Literal original rational coordinate interval membership. -/
def coordinateBox (N l u q : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶
    (rationalLE (entry (Syn.shift l) (var 0)) (entry (Syn.shift q) (var 0)) ⋏
      rationalLE (entry (Syn.shift q) (var 0)) (entry (Syn.shift u) (var 0))))

@[simp] theorem subst_coordinateBox {k : ℕ} (σ : Fin n → PTm k) (N l u q : PTm n) :
    (coordinateBox N l u q).subst σ = coordinateBox (Syn.subst σ N) (Syn.subst σ l)
      (Syn.subst σ u) (Syn.subst σ q) := by
  simp only [coordinateBox,Fm.subst_all,Fm.subst_imp,Fm.subst_and,subst_lt,
    Analysis.RationalArgmin.subst_rationalLE,subst_entry,Syn.subst_var,Syn.up_zero,Syn.up_succ,
    Syn.subst_shift,Syn.shift_subst]

theorem coordinate_at (N l u q i : PTm n) (h : Γ ⊢[PRAAx] coordinateBox N l u q)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    rationalLE (entry l i) (entry q i) ⋏ rationalLE (entry q i) (entry u i) := by
  have ht : Γ ⊢[PRAAx] lt i N ⟶
      (rationalLE (entry l i) (entry q i) ⋏ rationalLE (entry q i) (entry u i)) := by
    simpa only [Fm.subst_imp,Fm.subst_and,subst_lt,Analysis.RationalArgmin.subst_rationalLE,
      subst_entry,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE i
  exact .impE ht hi

/-- The sum inequalities are derived from genuine coordinate inequalities. -/
theorem dot_interval (N c l u q : PTm n) (h : Γ ⊢[PRAAx] coordinateBox N l u q) :
    Γ ⊢[PRAAx] rationalLE (lowerSum N c l u) (dot N c q) ⋏
      rationalLE (dot N c q) (upperSum N c l u) := by
  have point : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift N) ⟶
      (rationalLE (term lowerBody (var 0) (pairT (Syn.shift c) (pairT (Syn.shift l) (Syn.shift u))))
        (term productBody (var 0) (pairT (Syn.shift c) (Syn.shift q))) ⋏
       rationalLE (term productBody (var 0) (pairT (Syn.shift c) (Syn.shift q)))
        (term upperBody (var 0) (pairT (Syn.shift c) (pairT (Syn.shift l) (Syn.shift u)))))) := by
    refine .allI (.impI ?_)
    have source : Γ.map Fm.shift ⊢[PRAAx] coordinateBox (Syn.shift N) (Syn.shift l) (Syn.shift u) (Syn.shift q) := by
      simpa only [Fm.shift,subst_coordinateBox,Syn.shift] using h.shift
    have ih := coordinate_at _ _ _ _ (var 0) source.wk Prf.hyp0
    have bounds := Analysis.RationalArithmetic.multiply_interval (entry (Syn.shift c) (var 0)) _ _ _
      (Prf.andE₁ ih) (Prf.andE₂ ih)
    exact .andI
      (Analysis.RationalArgmin.rationalLE_congr (lower_at _ _ _ _).eqSymm (product_at _ _ _).eqSymm (Prf.andE₁ bounds))
      (Analysis.RationalArgmin.rationalLE_congr (product_at _ _ _).eqSymm (upper_at _ _ _ _).eqSymm (Prf.andE₂ bounds))
  have low : Γ ⊢[PRAAx] termwiseLE lowerBody productBody N (pairT c (pairT l u)) (pairT c q) := by
    refine .allI (.impI ?_)
    have bound := Prf.impE (point.allOpen.wk (ψ := lt (var 0) (Syn.shift N))) Prf.hyp0
    simpa only [Syn.shift,subst_pairT] using Prf.andE₁ bound
  have high : Γ ⊢[PRAAx] termwiseLE productBody upperBody N (pairT c q) (pairT c (pairT l u)) := by
    refine .allI (.impI ?_)
    have bound := Prf.impE (point.allOpen.wk (ψ := lt (var 0) (Syn.shift N))) Prf.hyp0
    simpa only [Syn.shift,subst_pairT] using Prf.andE₂ bound
  exact .andI (sum_monotone _ _ _ _ _ low) (sum_monotone _ _ _ _ _ high)

/-- The numerical interval test for one supplied row and rational bound. -/
def rowCertificate (N c b l u : PTm n) : Fm PTm n :=
  rationalLE (negative b) (lowerSum N c l u) ⋏ rationalLE (upperSum N c l u) b

def rowMember (N c b q : PTm n) : Fm PTm n :=
  rationalLE (negative b) (dot N c q) ⋏ rationalLE (dot N c q) b

@[simp] theorem subst_rowCertificate {k : ℕ} (σ : Fin n → PTm k) (N c b l u : PTm n) :
    (rowCertificate N c b l u).subst σ = rowCertificate (Syn.subst σ N) (Syn.subst σ c)
      (Syn.subst σ b) (Syn.subst σ l) (Syn.subst σ u) := by
  simp only [rowCertificate,Fm.subst_and,Analysis.RationalArgmin.subst_rationalLE,
    Analysis.RationalArithmetic.subst_negative,subst_lowerSum,subst_upperSum]
@[simp] theorem subst_rowMember {k : ℕ} (σ : Fin n → PTm k) (N c b q : PTm n) :
    (rowMember N c b q).subst σ = rowMember (Syn.subst σ N) (Syn.subst σ c)
      (Syn.subst σ b) (Syn.subst σ q) := by
  simp only [rowMember,Fm.subst_and,Analysis.RationalArgmin.subst_rationalLE,
    Analysis.RationalArithmetic.subst_negative,subst_dot]

theorem row_containment (N c b l u q : PTm n)
    (hc : Γ ⊢[PRAAx] rowCertificate N c b l u) (hq : Γ ⊢[PRAAx] coordinateBox N l u q) :
    Γ ⊢[PRAAx] rowMember N c b q := by
  have interval := dot_interval N c l u q hq
  exact .andI (Analysis.RationalArgmin.transitive (Prf.andE₁ hc) (Prf.andE₁ interval))
    (Analysis.RationalArgmin.transitive (Prf.andE₂ interval) (Prf.andE₂ hc))

/-- Facet entry j is decoded as (lattice-coordinate row,rational bound). -/
def facetsCertificate (N F l u : PTm n) : Fm PTm n :=
  .all (lt (var 0) (length (Syn.shift F)) ⟶
    rowCertificate (Syn.shift N) (fstT (entry (Syn.shift F) (var 0)))
      (sndT (entry (Syn.shift F) (var 0))) (Syn.shift l) (Syn.shift u))

def facetsMember (N F q : PTm n) : Fm PTm n :=
  .all (lt (var 0) (length (Syn.shift F)) ⟶
    rowMember (Syn.shift N) (fstT (entry (Syn.shift F) (var 0)))
      (sndT (entry (Syn.shift F) (var 0))) (Syn.shift q))

@[simp] theorem subst_facetsCertificate {k : ℕ} (σ : Fin n → PTm k) (N F l u : PTm n) :
    (facetsCertificate N F l u).subst σ = facetsCertificate (Syn.subst σ N) (Syn.subst σ F)
      (Syn.subst σ l) (Syn.subst σ u) := by
  simp only [facetsCertificate,Fm.subst_all,Fm.subst_imp,subst_lt,subst_length,subst_rowCertificate,
    subst_fstT,subst_sndT,subst_entry,Syn.subst_var,Syn.up_zero,Syn.up_succ,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_facetsMember {k : ℕ} (σ : Fin n → PTm k) (N F q : PTm n) :
    (facetsMember N F q).subst σ = facetsMember (Syn.subst σ N) (Syn.subst σ F) (Syn.subst σ q) := by
  simp only [facetsMember,Fm.subst_all,Fm.subst_imp,subst_lt,subst_length,subst_rowMember,
    subst_fstT,subst_sndT,subst_entry,Syn.subst_var,Syn.up_zero,Syn.up_succ,Syn.subst_shift,Syn.shift_subst]

theorem facet_at (N F l u j : PTm n) (h : Γ ⊢[PRAAx] facetsCertificate N F l u)
    (hj : Γ ⊢[PRAAx] lt j (length F)) : Γ ⊢[PRAAx]
    rowCertificate N (fstT (entry F j)) (sndT (entry F j)) l u := by
  have ht : Γ ⊢[PRAAx] lt j (length F) ⟶ rowCertificate N (fstT (entry F j)) (sndT (entry F j)) l u := by
    simpa only [Fm.subst_imp,subst_lt,subst_length,subst_rowCertificate,subst_fstT,subst_sndT,
      subst_entry,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE j
  exact .impE ht hj

theorem facets_containment (N F l u q : PTm n)
    (hc : Γ ⊢[PRAAx] facetsCertificate N F l u) (hq : Γ ⊢[PRAAx] coordinateBox N l u q) :
    Γ ⊢[PRAAx] facetsMember N F q := by
  refine .allI (.impI ?_)
  have cert : Γ.map Fm.shift ⊢[PRAAx] facetsCertificate (Syn.shift N) (Syn.shift F) (Syn.shift l) (Syn.shift u) := by
    simpa only [Fm.shift,subst_facetsCertificate,Syn.shift] using hc.shift
  have point : Γ.map Fm.shift ⊢[PRAAx] coordinateBox (Syn.shift N) (Syn.shift l) (Syn.shift u) (Syn.shift q) := by
    simpa only [Fm.shift,subst_coordinateBox,Syn.shift] using hq.shift
  exact row_containment _ _ _ _ _ _ (facet_at _ _ _ _ (var 0) cert.wk Prf.hyp0) point.wk

/-- Literal bounded syntax for the numerical rational interval test. -/
def rowSyntax (N c b l u : PTm n) : BoundedSyntax.BFm n :=
  .and (.le (left (negative b) (lowerSum N c l u)) (left (lowerSum N c l u) (negative b)))
    (.le (left (upperSum N c l u) b) (left b (upperSum N c l u)))

def certificateSyntax (N F l u : PTm n) : BoundedSyntax.BFm n :=
  .all (length F) (rowSyntax (Syn.shift N) (fstT (entry (Syn.shift F) (var 0)))
    (sndT (entry (Syn.shift F) (var 0))) (Syn.shift l) (Syn.shift u))

theorem row_formula (N c b l u : PTm n) :
    BoundedSyntax.formula (rowSyntax N c b l u) = rowCertificate N c b l u := rfl

theorem certificate_formula (N F l u : PTm n) :
    BoundedSyntax.formula (certificateSyntax N F l u) = facetsCertificate N F l u := by
  simp only [certificateSyntax,BoundedSyntax.formula,row_formula,facetsCertificate,Syn.shift,subst_length]

def checkerF : PR 4 := BoundedSyntax.bitF (certificateSyntax (var 0) (var 1) (var 2) (var 3) : BoundedSyntax.BFm 4)
def check (N F l u : PTm n) : PTm n := app checkerF ![N,F,l,u]

@[simp] theorem subst_check {k : ℕ} (σ : Fin n → PTm k) (N F l u : PTm n) :
    Syn.subst σ (check N F l u) = check (Syn.subst σ N) (Syn.subst σ F) (Syn.subst σ l) (Syn.subst σ u) := by
  simp only [check,PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem checker_program (N F l u : PTm n) : Γ ⊢[PRAAx] check N F l u ≐
    BoundedSyntax.bit (certificateSyntax (var 0) (var 1) (var 2) (var 3) : BoundedSyntax.BFm 4) ![N,F,l,u] :=
  BoundedSyntax.program_correct _ _

theorem checker_reflection (N F l u : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (check N F l u ≐ one) (facetsCertificate N F l u) := by
  have reflect := BoundedSyntax.bounded_reflection (Γ := Γ)
    (certificateSyntax (var 0) (var 1) (var 2) (var 3) : BoundedSyntax.BFm 4) ![N,F,l,u]
  rw [certificate_formula] at reflect
  simp only [subst_facetsCertificate,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three] at reflect
  have p := checker_program (Γ := Γ) N F l u
  exact .iffI (.impI (reflect.wk.iffMp (p.wk.eqSymm.eqTrans Prf.hyp0)))
    (.impI (p.wk.eqTrans (reflect.wk.iffMpr Prf.hyp0)))

theorem checker_boolean (N F l u : PTm n) : Γ ⊢[PRAAx] (check N F l u ≐ zero) ⋎ (check N F l u ≐ one) := by
  have p := checker_program (Γ := Γ) N F l u
  exact .orE (BoundedSyntax.bit_cases (certificateSyntax (var 0) (var 1) (var 2) (var 3) : BoundedSyntax.BFm 4) ![N,F,l,u])
    (.orI₁ (p.wk.eqTrans Prf.hyp0)) (.orI₂ (p.wk.eqTrans Prf.hyp0))

theorem accepted_containment (N F l u q : PTm n) (hc : Γ ⊢[PRAAx] check N F l u ≐ one)
    (hq : Γ ⊢[PRAAx] coordinateBox N l u q) : Γ ⊢[PRAAx] facetsMember N F q :=
  facets_containment N F l u q ((checker_reflection N F l u).iffMp hc) hq

/-- Checker acceptance covers every query code in the original box, with
no global containment premise or fixed dimension. -/
theorem accepted_box (N F l u : PTm n) (hc : Γ ⊢[PRAAx] check N F l u ≐ one) : Γ ⊢[PRAAx]
    .all (coordinateBox (Syn.shift N) (Syn.shift l) (Syn.shift u) (var 0) ⟶
      facetsMember (Syn.shift N) (Syn.shift F) (var 0)) := by
  refine .allI (.impI ?_)
  have checked : Γ.map Fm.shift ⊢[PRAAx] check (Syn.shift N) (Syn.shift F) (Syn.shift l) (Syn.shift u) ≐ one := by
    simpa only [Fm.shift,Fm.subst_eq,subst_check,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hc.shift
  exact accepted_containment _ _ _ _ _ checked.wk Prf.hyp0

/-- Executable numerical metadata for the actual sums, independently of
the certificate Boolean. -/
def dotF : PR 3 := PTm.toPR (dot (var 0) (var 1) (var 2))
def lowerF : PR 4 := PTm.toPR (lowerSum (var 0) (var 1) (var 2) (var 3))
def upperF : PR 4 := PTm.toPR (upperSum (var 0) (var 1) (var 2) (var 3))

theorem dot_program (N c q : PTm n) : Γ ⊢[PRAAx] ap3 dotF N c q ≐ dot N c q := by
  simpa only [dotF,ap3,subst_dot,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using toPR_eq (Γ := Γ) (dot (var 0) (var 1) (var 2) : PTm 3) ![N,c,q]

theorem lower_program (N c l u : PTm n) : Γ ⊢[PRAAx] app lowerF ![N,c,l,u] ≐ lowerSum N c l u := by
  simpa only [lowerF,subst_lowerSum,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (lowerSum (var 0) (var 1) (var 2) (var 3) : PTm 4) ![N,c,l,u]

theorem upper_program (N c l u : PTm n) : Γ ⊢[PRAAx] app upperF ![N,c,l,u] ≐ upperSum N c l u := by
  simpa only [upperF,subst_upperSum,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (upperSum (var 0) (var 1) (var 2) (var 3) : PTm 4) ![N,c,l,u]

theorem dot_interval_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (coordinateBox (var 0) (var 2) (var 3) (var 4) ⟶
      (rationalLE (lowerSum (var 0) (var 1) (var 2) (var 3)) (dot (var 0) (var 1) (var 4)) ⋏
        rationalLE (dot (var 0) (var 1) (var 4)) (upperSum (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 5 (.impI (dot_interval _ _ _ _ _ Prf.hyp0))

theorem row_containment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (rowCertificate (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      coordinateBox (var 0) (var 3) (var 4) (var 5) ⟶ rowMember (var 0) (var 1) (var 2) (var 5)) :=
  closeUniv 6 (.impI (.impI (row_containment _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem slab_checker_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (Fm.iff (check (var 0) (var 1) (var 2) (var 3) ≐ one)
      (facetsCertificate (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (checker_reflection _ _ _ _)

theorem slab_checker_boolean_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((check (var 0) (var 1) (var 2) (var 3) ≐ zero) ⋎ (check (var 0) (var 1) (var 2) (var 3) ≐ one)) :=
  closeUniv 4 (checker_boolean _ _ _ _)

theorem accepted_containment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (check (var 0) (var 1) (var 2) (var 3) ≐ one ⟶
      coordinateBox (var 0) (var 2) (var 3) (var 4) ⟶ facetsMember (var 0) (var 1) (var 4)) :=
  closeUniv 5 (.impI (.impI (accepted_containment _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem accepted_box_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (check (var 0) (var 1) (var 2) (var 3) ≐ one ⟶
      .all (coordinateBox (Syn.shift (var 0)) (Syn.shift (var 2)) (Syn.shift (var 3)) (var 0) ⟶
        facetsMember (Syn.shift (var 0)) (Syn.shift (var 1)) (var 0))) :=
  closeUniv 4 (.impI (accepted_box _ _ _ _ Prf.hyp0))

theorem slab_programs_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((ap3 dotF (var 0) (var 1) (var 2) ≐ dot (var 0) (var 1) (var 2)) ⋏
      ((app lowerF ![var 0,var 1,var 2,var 3] ≐ lowerSum (var 0) (var 1) (var 2) (var 3)) ⋏
        (app upperF ![var 0,var 1,var 2,var 3] ≐ upperSum (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (.andI (dot_program _ _ _) (.andI (lower_program _ _ _ _) (upper_program _ _ _ _)))

theorem slab_checker_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (check (var 0) (var 1) (var 2) (var 3) ≐
      BoundedSyntax.bit (certificateSyntax (var 0) (var 1) (var 2) (var 3) : BoundedSyntax.BFm 4)
        ![var 0,var 1,var 2,var 3]) := closeUniv 4 (checker_program _ _ _ _)

end LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiSlabInterval
