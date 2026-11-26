import IPRADerivations.Foundations.FiniteHausdorff
import IPRADerivations.AnalyticNumberTheory.Multiplicative
import IPRADerivations.Core.Header

/-!
# Actual finite Cartesian products in the sup metric

Finite-demand packet, `lem:aggregate-calculus`, clause 3. The product list
is a genuine primitive recursive sequence, in quotient/remainder order.
Its length, arbitrary-index lookup, and inverse pair-index equations are
proved internally. Product distance is the actual maximum of the two fixed
component distance programs. Actual nearest indices in both target lists
supply the product witness; neither a covering certificate nor product-code
correctness is a premise.

Distances are natural numerators in the common rational scale of
`FiniteHausdorff`; a rational-vector/common-scale adapter remains separate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.FiniteHausdorffProduct

open_ipra
open LeanProofs.IPRA.Foundations.FiniteHausdorff
open LeanProofs.IPRA.Foundations.MasterCertificate
  (sequence entry sequence_length sequence_decode subst_sequence subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.Foundations.DemandClosure
  (maximum subst_maximum maximum_left maximum_right maximum_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_lt' quo_lt)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Quotient/remainder enumerates the literal pair of entries. -/
def productValue (S S' i : PTm n) : PTm n :=
  pairT (entry S (quo i (length S'))) (entry S' (rem i (length S')))

def productBody : PTm 2 := productValue (fstT (var 1)) (sndT (var 1)) (var 0)

/-- The actual finite Cartesian list; empty factors give length zero. -/
def product (S S' : PTm n) : PTm n :=
  sequence productBody (length S*length S') (pairT S S')

@[simp] theorem subst_productValue {m : ℕ} (σ : Fin n → PTm m) (S S' i : PTm n) :
    Syn.subst σ (productValue S S' i) =
      productValue (Syn.subst σ S) (Syn.subst σ S') (Syn.subst σ i) := by
  simp only [productValue, subst_pairT, subst_entry, subst_ap2, subst_length]

@[simp] theorem subst_product {m : ℕ} (σ : Fin n → PTm m) (S S' : PTm n) :
    Syn.subst σ (product S S') = product (Syn.subst σ S) (Syn.subst σ S') := by
  simp only [product, subst_sequence, PTm.subst_mul, subst_length, subst_pairT]

theorem product_length (S S' : PTm n) :
    Γ ⊢[PRAAx] length (product S S') ≐ length S*length S' := sequence_length _ _ _

theorem product_value_at (S S' i : PTm n) :
    Γ ⊢[PRAAx] inst2 productBody i (pairT S S') ≐ productValue S S' i := by
  have h := Prf.eqCongr (Γ := Γ) (productValue (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![fstT (pairT S S'), sndT (pairT S S'), i]) (σ' := ![S,S',i])
    (fun j => by fin_cases j; exact fst_pair _ _; exact snd_pair _ _; exact .eqRefl _)
  simpa only [inst2, productBody, subst_productValue, subst_fstT, subst_sndT,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] using h

/-- Every actual in-range product-list lookup decodes to its component entries. -/
theorem product_lookup {S S' i : PTm n}
    (hi : Γ ⊢[PRAAx] lt i (length (product S S'))) :
    Γ ⊢[PRAAx] entry (product S S') i ≐ productValue S S' i :=
  (sequence_decode productBody (lt_congr (.eqRefl _) (product_length S S') hi)).eqTrans
    (product_value_at S S' i)

/-- Both decoded coordinates of an arbitrary internal product index are in range. -/
theorem product_indices {S S' i : PTm n} (hS' : Γ ⊢[PRAAx] le one (length S'))
    (hi : Γ ⊢[PRAAx] lt i (length (product S S'))) :
    Γ ⊢[PRAAx] lt (quo i (length S')) (length S) ⋏ lt (rem i (length S')) (length S') :=
  .andI (quo_lt (positive_length hS')
      (lt_congr (.eqRefl _) ((product_length S S').eqTrans (mul_comm _ _)) hi))
    (rem_lt' (positive_length hS') i)

/-- The inverse pair index is itself an actual internal natural-number term. -/
def pairIndex (T' j l : PTm n) : PTm n := j*length T'+l

@[simp] theorem subst_pairIndex {m : ℕ} (σ : Fin n → PTm m) (T' j l : PTm n) :
    Syn.subst σ (pairIndex T' j l) =
      pairIndex (Syn.subst σ T') (Syn.subst σ j) (Syn.subst σ l) := by
  simp only [pairIndex, PTm.subst_add, PTm.subst_mul, subst_length]

theorem pair_index_range {T T' j l : PTm n}
    (hj : Γ ⊢[PRAAx] lt j (length T)) (hl : Γ ⊢[PRAAx] lt l (length T')) :
    Γ ⊢[PRAAx] lt (pairIndex T' j l) (length (product T T')) := by
  have first : Γ ⊢[PRAAx] le (succ (j*length T'+l)) (succ j*length T') :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ (le_refl (j*length T')) hl)
  exact lt_congr (.eqRefl _) (product_length T T').eqSymm
    (le_trans first (le_mul_mono hj (le_refl (length T'))))

/-- Division uniqueness verifies both coordinates of the constructed pair index. -/
theorem pair_index_decode {T' j l : PTm n} (hT' : Γ ⊢[PRAAx] le one (length T'))
    (hl : Γ ⊢[PRAAx] lt l (length T')) :
    Γ ⊢[PRAAx] (quo (pairIndex T' j l) (length T') ≐ j) ⋏
      (rem (pairIndex T' j l) (length T') ≐ l) := by
  have pos := positive_length hT'
  have eq : Γ ⊢[PRAAx] pairIndex T' j l ≐ succ (pred (length T'))*j+l :=
    (by unfold pairIndex; ipra_ring : Γ ⊢[PRAAx] pairIndex T' j l ≐ length T'*j+l).eqTrans
      (congrAdd (congrMul pos (.eqRefl _)) (.eqRefl _))
  have div := div_mod_unique eq (lt_congr (.eqRefl _) pos hl)
  exact .andI ((congrAp2 quoF (.eqRefl _) pos).eqTrans (.andE₁ div))
    ((congrAp2 remF (.eqRefl _) pos).eqTrans (.andE₂ div))

/-- A chosen pair of target indices decodes to the actual pair of target entries. -/
theorem product_pair_entry {T T' j l : PTm n}
    (hT' : Γ ⊢[PRAAx] le one (length T'))
    (hj : Γ ⊢[PRAAx] lt j (length T)) (hl : Γ ⊢[PRAAx] lt l (length T')) :
    Γ ⊢[PRAAx] entry (product T T') (pairIndex T' j l) ≐ pairT (entry T j) (entry T' l) := by
  have dec := pair_index_decode (j := j) hT' hl
  exact (product_lookup (pair_index_range hj hl)).eqTrans
    (congrPairT (entry_congr (.eqRefl _) (.andE₁ dec)) (entry_congr (.eqRefl _) (.andE₂ dec)))

/-- The actual sup product distance program, evaluated on paired point codes. -/
def metric (d e : PR 3) : PR 3 := PTm.toPR
  (maximum (distance d (fstT (var 0)) (fstT (var 1)) (var 2))
    (distance e (sndT (var 0)) (sndT (var 1)) (var 2)))

theorem metric_at (d e : PR 3) (x y p : PTm n) :
    Γ ⊢[PRAAx] distance (metric d e) x y p ≐
      maximum (distance d (fstT x) (fstT y) p) (distance e (sndT x) (sndT y) p) := by
  have h := toPR_eq (Γ := Γ)
    (maximum (distance d (fstT (var 0)) (fstT (var 1)) (var 2))
      (distance e (sndT (var 0)) (sndT (var 1)) (var 2))) ![x,y,p]
  simp only [subst_maximum, subst_distance, subst_fstT, subst_sndT,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h
  simpa only [distance, metric, ap3] using h

theorem maximum_congr {a a' b b' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a')
    (hb : Γ ⊢[PRAAx] b ≐ b') : Γ ⊢[PRAAx] maximum a b ≐ maximum a' b' :=
  congrAdd ha (congrMonus hb ha)

theorem metric_pair (d e : PR 3) (x x' y y' p : PTm n) :
    Γ ⊢[PRAAx] distance (metric d e) (pairT x x') (pairT y y') p ≐
      maximum (distance d x y p) (distance e x' y' p) :=
  (metric_at d e _ _ p).eqTrans
    (maximum_congr (congrAp3 d (fst_pair _ _) (fst_pair _ _) (.eqRefl _))
      (congrAp3 e (snd_pair _ _) (snd_pair _ _) (.eqRefl _)))

/-- The Cartesian-list constructor is itself one fixed PR program. -/
def productF : PR 2 := PTm.toPR (product (var 0) (var 1))

theorem product_at (S S' : PTm n) :
    Γ ⊢[PRAAx] ap2 productF S S' ≐ product S S' := by
  have h := toPR_eq (Γ := Γ) (product (var 0) (var 1)) ![S,S']
  simpa only [productF, ap2, subst_product, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one] using h

/-- Two independent actual least-neighbor scans yield a single product neighbor. -/
theorem pair_distance_bound (d e : PR 3) (S S' T T' p a b : PTm n)
    (hT : Γ ⊢[PRAAx] le one (length T)) (hT' : Γ ⊢[PRAAx] le one (length T'))
    (ha : Γ ⊢[PRAAx] lt a (length S)) (hb : Γ ⊢[PRAAx] lt b (length S')) :
    Γ ⊢[PRAAx] le
      (distanceTo (metric d e) (pairT (entry S a) (entry S' b)) (product T T') p)
      (maximum (directed d S T p) (directed e S' T' p)) := by
  let j := nearest d (entry S a) T p
  let l := nearest e (entry S' b) T' p
  have hj : Γ ⊢[PRAAx] lt j (length T) := .andE₁ (nearest_spec d (entry S a) T p hT)
  have hl : Γ ⊢[PRAAx] lt l (length T') := .andE₁ (nearest_spec e (entry S' b) T' p hT')
  have decoded := product_pair_entry hT' hj hl
  have eq : Γ ⊢[PRAAx]
      distance (metric d e) (pairT (entry S a) (entry S' b))
        (entry (product T T') (pairIndex T' j l)) p ≐
      maximum (distance d (entry S a) (entry T j) p) (distance e (entry S' b) (entry T' l) p) :=
    (congrAp3 (metric d e) (.eqRefl _) decoded (.eqRefl _)).eqTrans (metric_pair d e _ _ _ _ _)
  have bound : Γ ⊢[PRAAx] le
      (maximum (distance d (entry S a) (entry T j) p) (distance e (entry S' b) (entry T' l) p))
      (maximum (directed d S T p) (directed e S' T' p)) :=
    maximum_le (le_trans (nearest_error d S T p a hT ha) (maximum_left _ _))
      (le_trans (nearest_error e S' T' p b hT' hb) (maximum_right _ _))
  exact le_trans (distanceTo_le (metric d e) _ (product T T') p (pairIndex T' j l) (pair_index_range hj hl))
    (le_congr eq.eqSymm (.eqRefl _) bound)

theorem distanceTo_congr_point (d : PR 3) {z z' T p : PTm n} (h : Γ ⊢[PRAAx] z ≐ z') :
    Γ ⊢[PRAAx] distanceTo d z T p ≐ distanceTo d z' T p := by
  have eq := Prf.eqCongr (Γ := Γ) (distanceTo d (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![z,T,p]) (σ' := ![z',T,p])
    (fun i => by fin_cases i; exact h; exact .eqRefl _; exact .eqRefl _)
  simpa only [subst_distanceTo, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using eq

/-- Every actual product-list point receives its computed pair of neighbors. -/
theorem product_point_bound (d e : PR 3) (S S' T T' p i : PTm n)
    (hS' : Γ ⊢[PRAAx] le one (length S'))
    (hT : Γ ⊢[PRAAx] le one (length T)) (hT' : Γ ⊢[PRAAx] le one (length T'))
    (hi : Γ ⊢[PRAAx] lt i (length (product S S'))) :
    Γ ⊢[PRAAx] le (distanceTo (metric d e) (entry (product S S') i) (product T T') p)
      (maximum (directed d S T p) (directed e S' T' p)) := by
  have ranges := product_indices hS' hi
  exact le_congr (distanceTo_congr_point (metric d e) (product_lookup hi)).eqSymm (.eqRefl _)
    (pair_distance_bound d e S S' T T' p _ _ hT hT' (.andE₁ ranges) (.andE₂ ranges))

/-- The directed Hausdorff scan of the genuine Cartesian lists has the exact sup bound. -/
theorem directed_product (d e : PR 3) (S S' T T' p : PTm n)
    (hS' : Γ ⊢[PRAAx] le one (length S'))
    (hT : Γ ⊢[PRAAx] le one (length T)) (hT' : Γ ⊢[PRAAx] le one (length T')) :
    Γ ⊢[PRAAx] le (directed (metric d e) (product S S') (product T T') p)
      (maximum (directed d S T p) (directed e S' T' p)) := by
  apply directed_bound
  refine .allI (.impI ?_)
  have s' : Γ.map Fm.shift ⊢[PRAAx] le one (length (Syn.shift S')) := by
    simpa only [Fm.shift, subst_le, subst_length, ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero, Syn.shift] using hS'.shift
  have t : Γ.map Fm.shift ⊢[PRAAx] le one (length (Syn.shift T)) := by
    simpa only [Fm.shift, subst_le, subst_length, ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero, Syn.shift] using hT.shift
  have t' : Γ.map Fm.shift ⊢[PRAAx] le one (length (Syn.shift T')) := by
    simpa only [Fm.shift, subst_le, subst_length, ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero, Syn.shift] using hT'.shift
  have hi : (lt (var 0) (length (Syn.shift (product S S'))) :: Γ.map Fm.shift) ⊢[PRAAx]
      lt (var 0) (length (product (Syn.shift S) (Syn.shift S'))) := by
    simpa only [Syn.shift, subst_product] using
      (Prf.hyp0 : (lt (var 0) (length (Syn.shift (product S S'))) :: Γ.map Fm.shift) ⊢[PRAAx] _)
  have result := product_point_bound d e (Syn.shift S) (Syn.shift S') (Syn.shift T) (Syn.shift T')
    (Syn.shift p) (var 0) s'.wk t.wk t'.wk hi
  simpa only [Syn.shift, subst_product, subst_maximum, subst_directed] using result

/-- `lem:aggregate-calculus`(3), on the actual Cartesian lists and actual sup metric. -/
theorem hausdorff_product (d e : PR 3) (S S' T T' p : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hS' : Γ ⊢[PRAAx] le one (length S'))
    (hT : Γ ⊢[PRAAx] le one (length T)) (hT' : Γ ⊢[PRAAx] le one (length T')) :
    Γ ⊢[PRAAx] le (hausdorff (metric d e) (product S S') (product T T') p)
      (maximum (hausdorff d S T p) (hausdorff e S' T' p)) := by
  have forward : Γ ⊢[PRAAx] le (maximum (directed d S T p) (directed e S' T' p))
      (maximum (hausdorff d S T p) (hausdorff e S' T' p)) :=
    maximum_le (le_trans (maximum_left _ _) (maximum_left _ _))
      (le_trans (maximum_left _ _) (maximum_right _ _))
  have backward : Γ ⊢[PRAAx] le (maximum (directed d T S p) (directed e T' S' p))
      (maximum (hausdorff d S T p) (hausdorff e S' T' p)) :=
    maximum_le (le_trans (maximum_right _ _) (maximum_left _ _))
      (le_trans (maximum_right _ _) (maximum_right _ _))
  exact maximum_le (le_trans (directed_product d e S S' T T' p hS' hT hT') forward)
    (le_trans (directed_product d e T T' S S' p hT' hS hS') backward)

/-- All four lists and the persistent metric data are arbitrary internal values. -/
def productFormula (d e : PR 3) : Fm PTm 5 :=
  le one (length (var 0)) ⟶ le one (length (var 1)) ⟶
    le one (length (var 2)) ⟶ le one (length (var 3)) ⟶
    le (hausdorff (metric d e) (product (var 0) (var 1)) (product (var 2) (var 3)) (var 4))
      (maximum (hausdorff d (var 0) (var 2) (var 4)) (hausdorff e (var 1) (var 3) (var 4)))

theorem hausdorff_product_closed (d e : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 (productFormula d e) :=
  closeUniv 5 (.impI (.impI (.impI (.impI
    (hausdorff_product d e (var 0) (var 1) (var 2) (var 3) (var 4)
      Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

/-- Closed exact coding facts, with no nonempty guard needed for the product length. -/
theorem product_program_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      ((ap2 productF (var 0) (var 1) ≐ product (var 0) (var 1)) ⋏
        (length (product (var 0) (var 1)) ≐ length (var 0)*length (var 1))) :=
  closeUniv 2 (.andI (product_at _ _) (product_length _ _))

#print axioms product_length
#print axioms product_lookup
#print axioms product_indices
#print axioms pair_index_range
#print axioms pair_index_decode
#print axioms product_pair_entry
#print axioms metric_pair
#print axioms product_at
#print axioms product_point_bound
#print axioms directed_product
#print axioms hausdorff_product_closed
#print axioms product_program_closed

end LeanProofs.IPRA.Foundations.FiniteHausdorffProduct
