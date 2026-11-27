import IPRADerivations.DiophantineNumberTheory.MinkowskiBoxes
import IPRADerivations.Core.Fubini

/-!
# Actual global indexing and separation of concatenated integer boxes

The finite Minkowski certificate uses a union of boxes. This file locates an
arbitrary index of the actual concatenation by a genuine bounded prefix-count
search, then derives decoded distinctness from within-box mixed-radix
injectivity and the supplied separating-coordinate condition between boxes.
No correctness of an enumeration, locator or decoded-distinctness predicate
is supplied as an assumption. Rational common-denominator conversion and the
geometric membership/volume producer remain separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiBoxUnion

open_ipra exports
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiBoxes
  (points point count sides side_at inside insideAt point_inside_at prefixCount boxes
    subst_prefixCount subst_boxes subst_count subst_sides subst_point)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The true cumulative product count of the entire outer box list. -/
def total (N B : PTm n) : PTm n := prefixCount N B (length B)
def locationData (N B q : PTm n) : PTm n := pairT N (pairT B q)
/-- Zero precisely when q lies below the next cumulative count. -/
def locationBody : PTm 2 := monus (succ (sndT (sndT (var 1))))
  (prefixCount (fstT (var 1)) (fstT (sndT (var 1))) (succ (var 0)))
def location (N B q : PTm n) : PTm n := Search.mu locationBody (length B) (locationData N B q)
def localIndex (N B q : PTm n) : PTm n := monus q (prefixCount N B (location N B q))
def locationF : PR 3 := PTm.toPR (location (var 0) (var 1) (var 2))

@[simp] theorem subst_total {l : ℕ} (σ : Fin n → PTm l) (N B : PTm n) :
    Syn.subst σ (total N B) = total (Syn.subst σ N) (Syn.subst σ B) := by
  simp only [total, subst_prefixCount, subst_length]
@[simp] theorem subst_locationData {l : ℕ} (σ : Fin n → PTm l) (N B q : PTm n) :
    Syn.subst σ (locationData N B q) = locationData (Syn.subst σ N) (Syn.subst σ B) (Syn.subst σ q) := by
  simp only [locationData, subst_pairT]
@[simp] theorem subst_location {l : ℕ} (σ : Fin n → PTm l) (N B q : PTm n) :
    Syn.subst σ (location N B q) = location (Syn.subst σ N) (Syn.subst σ B) (Syn.subst σ q) := by
  simp only [location, Search.mu, subst_ap2, subst_length, subst_locationData]
@[simp] theorem subst_localIndex {l : ℕ} (σ : Fin n → PTm l) (N B q : PTm n) :
    Syn.subst σ (localIndex N B q) = localIndex (Syn.subst σ N) (Syn.subst σ B) (Syn.subst σ q) := by
  simp only [localIndex, PTm.subst_monus, subst_prefixCount, subst_location]

theorem location_at (N B q : PTm n) : Γ ⊢[PRAAx] ap3 locationF N B q ≐ location N B q := by
  have h := toPR_eq (Γ := Γ) (location (var 0) (var 1) (var 2) : PTm 3) ![N,B,q]
  simpa only [locationF, ap3, subst_location, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h

theorem locationBody_at (N B q j : PTm n) :
    Γ ⊢[PRAAx] inst2 locationBody j (locationData N B q) ≐ monus (succ q) (prefixCount N B (succ j)) := by
  simpa [locationBody, locationData, inst2, pairVector, pairVectorField] using
    (subst_pairVector_eq (Γ := Γ) (monus (succ (var 3)) (prefixCount (var 1) (var 2) (succ (var 0))) : PTm 4) j ![N, B, q])

/-- A global valid position makes the actual finite locator succeed, including
lists with zero-count blocks. An empty outer list admits no valid position. -/
theorem location_found (N B q : PTm n) (hq : Γ ⊢[PRAAx] lt q (total N B)) :
    Γ ⊢[PRAAx] lt (location N B q) (length B) ⋏
      lt q (prefixCount N B (succ (location N B q))) := by
  have positive : Γ ⊢[PRAAx] le one (length B) := by
    refine .orE (zero_or_succ (length B)) ?_ ?_
    · have zeroCount : (length B ≐ zero) :: Γ ⊢[PRAAx] total N B ≐ zero :=
        (congrAp3 _ Prf.hyp0 (.eqRefl B) (.eqRefl N)).eqTrans (MinkowskiBoxes.prefixCount_zero N B)
      exact lt_zero_absurd _ (lt_congr (.eqRefl _) zeroCount hq.wk)
    · exact Order.zero_lt_of_eq_succ Prf.hyp0
  have e := SignedEuclidean.positive_form (length B) positive
  have bound : Γ ⊢[PRAAx] lt (pred (length B)) (length B) :=
    lt_congr (.eqRefl _) e.eqSymm (le_refl _)
  have next : Γ ⊢[PRAAx] prefixCount N B (succ (pred (length B))) ≐ total N B :=
    congrAp3 _ e.eqSymm (.eqRefl B) (.eqRefl N)
  have zero : Γ ⊢[PRAAx] inst2 locationBody (pred (length B)) (locationData N B q) ≐ zero :=
    (locationBody_at N B q _).eqTrans (le_congr (.eqRefl _) next.eqSymm hq)
  have found := Search.search_found zero bound
  exact .andI (Prf.andE₁ found) ((locationBody_at _ _ _ _).eqSymm.eqTrans (Prf.andE₁ (Prf.andE₂ found)))

/-- Minimality of the actual locator supplies the lower endpoint inequality;
this is derived, not a supplied prefix-location correctness contract. -/
theorem location_lower (N B q : PTm n) :
    Γ ⊢[PRAAx] le (prefixCount N B (location N B q)) q := by
  refine .orE (zero_or_succ (location N B q)) ?_ ?_
  · exact le_congr ((congrAp3 _ Prf.hyp0 (.eqRefl B) (.eqRefl N)).eqTrans (MinkowskiBoxes.prefixCount_zero N B)).eqSymm
      (.eqRefl _) (zero_le q)
  · let E := location N B q ≐ succ (pred (location N B q))
    have smaller : E :: Γ ⊢[PRAAx] lt (pred (location N B q)) (location N B q) :=
      lt_congr (.eqRefl _) Prf.hyp0.eqSymm (le_refl _)
    have minimal := Search.search_minimal (f := locationBody) smaller
    refine .orE (lt_or_le q (prefixCount N B (location N B q))) ?_ Prf.hyp0
    have next : lt q (prefixCount N B (location N B q)) :: E :: Γ ⊢[PRAAx]
        prefixCount N B (succ (pred (location N B q))) ≐ prefixCount N B (location N B q) :=
      congrAp3 _ Prf.hyp1.eqSymm (.eqRefl B) (.eqRefl N)
    exact .botE _ (.impE minimal.wk ((locationBody_at _ _ _ _).eqTrans
      (le_congr (.eqRefl _) next.eqSymm Prf.hyp0)))

/-- Full numerical location information for the actual global index. -/
theorem location_spec (N B q : PTm n) (hq : Γ ⊢[PRAAx] lt q (total N B)) :
    Γ ⊢[PRAAx] lt (location N B q) (length B) ⋏
      (lt (localIndex N B q) (count N (fstT (entry B (location N B q))) (sndT (entry B (location N B q)))) ⋏
        (q ≐ prefixCount N B (location N B q)+localIndex N B q)) := by
  have found := location_found N B q hq
  have lower : Γ ⊢[PRAAx] le (prefixCount N B (location N B q)) q := location_lower N B q
  have localBound : Γ ⊢[PRAAx] lt (localIndex N B q)
      (count N (fstT (entry B (location N B q))) (sndT (entry B (location N B q)))) :=
    Foundations.SequenceComposition.offset_lt lower
      (lt_congr (.eqRefl _) (MinkowskiBoxes.prefixCount_succ N B _) (Prf.andE₂ found))
  exact .andI (Prf.andE₁ found) (.andI localBound (eq_add_of_le lower))

/-- Every arbitrary valid global index decodes to the actual mixed-radix point
at the actual located block and actual local offset. -/
theorem located_point (N B q : PTm n) (hq : Γ ⊢[PRAAx] lt q (total N B)) :
    Γ ⊢[PRAAx] entry (boxes N B) q ≐
      point N (fstT (entry B (location N B q))) (sndT (entry B (location N B q))) (localIndex N B q) := by
  have spec := location_spec N B q hq
  exact (entry_congr (.eqRefl _) (Prf.andE₂ (Prf.andE₂ spec))).eqTrans
    (MinkowskiBoxes.boxes_lookup _ _ _ _ (Prf.andE₁ spec) (Prf.andE₁ (Prf.andE₂ spec)))


/-- Signed upper/lower endpoint separation, allowing touching boundaries. -/
def separationAt (L U L' U' k : PTm n) : Fm PTm n :=
  le ((MinkowskiBoxes.upper U k).pos+(MinkowskiBoxes.lower L' k).neg)
      ((MinkowskiBoxes.lower L' k).pos+(MinkowskiBoxes.upper U k).neg) ⋎
  le ((MinkowskiBoxes.upper U' k).pos+(MinkowskiBoxes.lower L k).neg)
      ((MinkowskiBoxes.lower L k).pos+(MinkowskiBoxes.upper U' k).neg)
def separated (N L U L' U' : PTm n) : Fm PTm n :=
  .ex (lt (var 0) (Syn.shift N) ⋏ separationAt (Syn.shift L) (Syn.shift U) (Syn.shift L') (Syn.shift U') (var 0))

@[simp] theorem subst_separationAt {l : ℕ} (σ : Fin n → PTm l) (L U L' U' k : PTm n) :
    (separationAt L U L' U' k).subst σ = separationAt (Syn.subst σ L) (Syn.subst σ U)
      (Syn.subst σ L') (Syn.subst σ U') (Syn.subst σ k) := by
  simp only [separationAt, MinkowskiBoxes.lower, MinkowskiBoxes.upper, decode, Fm.subst_or,
    subst_le, PTm.subst_add, subst_fstT, subst_sndT, subst_entry]
@[simp] theorem subst_separated {l : ℕ} (σ : Fin n → PTm l) (N L U L' U' : PTm n) :
    (separated N L U L' U').subst σ = separated (Syn.subst σ N) (Syn.subst σ L) (Syn.subst σ U)
      (Syn.subst σ L') (Syn.subst σ U') := by
  simp only [separated, Fm.subst_ex, Fm.subst_and, subst_lt, subst_separationAt, Syn.subst_var,
    Syn.up_zero, Syn.up_succ, Syn.subst_shift, Syn.shift_subst]

/-- A strict upper bound followed by two weak signed bounds rules out equality.
Only natural gap witnesses are added; no order on an external number system
or unproved signed comparison decision procedure is used. -/
theorem separated_integer_ne (a u l b : ZT n)
    (ha : Γ ⊢[PRAAx] lt (a.pos+u.neg) (u.pos+a.neg))
    (hm : Γ ⊢[PRAAx] le (u.pos+l.neg) (l.pos+u.neg))
    (hb : Γ ⊢[PRAAx] le (l.pos+b.neg) (b.pos+l.neg)) : Γ ⊢[PRAAx] neg (ZT.eq a b) := by
  refine .impI ?_
  have e1 := natEq (eq_add_of_le (ha.wk (ψ := ZT.eq a b)))
  have e2 := natEq (eq_add_of_le (hm.wk (ψ := ZT.eq a b)))
  have e3 := natEq (eq_add_of_le (hb.wk (ψ := ZT.eq a b)))
  have same := ZT.toZ_eq (Prf.hyp0 : ZT.eq a b :: Γ ⊢[PRAAx] _)
  refine succ_ne_zero (a := monus (u.pos+a.neg) (succ (a.pos+u.neg))+
    monus (l.pos+u.neg) (u.pos+l.neg)+monus (b.pos+l.neg) (l.pos+b.neg)) ?_
  apply deriveNat
  simp only [ZT.toZ] at same
  ipra_simps
  linear_combination -e1-e2-e3-same

/-- The source separating-coordinate witness gives an explicit decoded point
inequality, using half-open box membership to handle touching boundaries. -/
theorem separated_points (N L U L' U' i j : PTm n)
    (h : Γ ⊢[PRAAx] sides N L U) (h' : Γ ⊢[PRAAx] sides N L' U')
    (hs : Γ ⊢[PRAAx] separated N L U L' U') :
    Γ ⊢[PRAAx] MinkowskiMesh.differentCoordinate N (point N L U i) (point N L' U' j) := by
  refine .exE hs ?_
  let E : Fm PTm (n+1) := lt (var 0) (Syn.shift N) ⋏
    separationAt (Syn.shift L) (Syn.shift U) (Syn.shift L') (Syn.shift U') (var 0)
  have pos : Γ.map Fm.shift ⊢[PRAAx] sides (Syn.shift N) (Syn.shift L) (Syn.shift U) := by
    simpa only [Fm.shift, subst_sides, Syn.shift] using h.shift
  have pos' : Γ.map Fm.shift ⊢[PRAAx] sides (Syn.shift N) (Syn.shift L') (Syn.shift U') := by
    simpa only [Fm.shift, subst_sides, Syn.shift] using h'.shift
  have a := point_inside_at (Syn.shift N) (Syn.shift L) (Syn.shift U) (Syn.shift i) (var 0) pos.wk
    (Prf.andE₁ (Prf.hyp0 : E :: Γ.map Fm.shift ⊢[PRAAx] E))
  have b := point_inside_at (Syn.shift N) (Syn.shift L') (Syn.shift U') (Syn.shift j) (var 0) pos'.wk
    (Prf.andE₁ (Prf.hyp0 : E :: Γ.map Fm.shift ⊢[PRAAx] E))
  have different : E :: Γ.map Fm.shift ⊢[PRAAx]
      neg (ZT.eq (decode (entry (point (Syn.shift N) (Syn.shift L) (Syn.shift U) (Syn.shift i)) (var 0)))
        (decode (entry (point (Syn.shift N) (Syn.shift L') (Syn.shift U') (Syn.shift j)) (var 0)))) := by
    refine .orE (Prf.andE₂ (Prf.hyp0 : E :: Γ.map Fm.shift ⊢[PRAAx] E)) ?_ ?_
    · exact separated_integer_ne _ _ _ _ (Prf.andE₂ a).wk Prf.hyp0 (Prf.andE₁ b).wk
    · exact Order.ne_symm (separated_integer_ne _ _ _ _ (Prf.andE₂ b).wk Prf.hyp0 (Prf.andE₁ a).wk)
  have out : E :: Γ.map Fm.shift ⊢[PRAAx] MinkowskiMesh.differentCoordinate (Syn.shift N)
      (point (Syn.shift N) (Syn.shift L) (Syn.shift U) (Syn.shift i))
      (point (Syn.shift N) (Syn.shift L') (Syn.shift U') (Syn.shift j)) := by
    refine .exI (var 0) ?_
    simpa only [MinkowskiMesh.differentCoordinate, Fm.subst_and, subst_lt, subst_neg, ZT.subst_eq,
      SignedEuclidean.subst_decode, subst_entry, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using
      (Prf.andI (Prf.andE₁ (Prf.hyp0 : E :: Γ.map Fm.shift ⊢[PRAAx] E)) different)
  simpa only [E, Fm.shift, MinkowskiMesh.subst_differentCoordinate, subst_point, Syn.shift] using out

/-- Reversing an explicit decoded-coordinate witness preserves its scope. -/
theorem differentCoordinate_symm (N a b : PTm n)
    (h : Γ ⊢[PRAAx] MinkowskiMesh.differentCoordinate N a b) :
    Γ ⊢[PRAAx] MinkowskiMesh.differentCoordinate N b a := by
  refine .exE h ?_
  let E : Fm PTm (n+1) := lt (var 0) (Syn.shift N) ⋏
    neg (ZT.eq (decode (entry (Syn.shift a) (var 0))) (decode (entry (Syn.shift b) (var 0))))
  have out : E :: Γ.map Fm.shift ⊢[PRAAx] MinkowskiMesh.differentCoordinate (Syn.shift N) (Syn.shift b) (Syn.shift a) := by
    refine .exI (var 0) ?_
    have ne : E :: Γ.map Fm.shift ⊢[PRAAx] neg
        (ZT.eq (decode (entry (Syn.shift b) (var 0))) (decode (entry (Syn.shift a) (var 0)))) :=
      .impI (.impE (Prf.andE₂ (Prf.hyp0 : E :: Γ.map Fm.shift ⊢[PRAAx] E)).wk Prf.hyp0.eqSymm)
    simpa only [MinkowskiMesh.differentCoordinate, Fm.subst_and, subst_lt, subst_neg, ZT.subst_eq,
      SignedEuclidean.subst_decode, subst_entry, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using
      (Prf.andI (Prf.andE₁ (Prf.hyp0 : E :: Γ.map Fm.shift ⊢[PRAAx] E)) ne)
  simpa only [E, Fm.shift, MinkowskiMesh.subst_differentCoordinate, Syn.shift] using out

/-- Genuine endpoint guards for every supplied numerical box. -/
def allSides (N B : PTm n) : Fm PTm n :=
  .all (lt (var 0) (length (Syn.shift B)) ⟶ sides (Syn.shift N)
    (fstT (entry (Syn.shift B) (var 0))) (sndT (entry (Syn.shift B) (var 0))))
/-- Literal source eq:box-disjoint on the supplied box endpoints. -/
def disjoint (N B : PTm n) : Fm PTm n :=
  .all (lt (var 0) (length (Syn.shift B)) ⟶ .all (lt (var 0) (var 1) ⟶
    separated (Syn.shift (Syn.shift N)) (fstT (entry (Syn.shift (Syn.shift B)) (var 0)))
      (sndT (entry (Syn.shift (Syn.shift B)) (var 0)))
      (fstT (entry (Syn.shift (Syn.shift B)) (var 1)))
      (sndT (entry (Syn.shift (Syn.shift B)) (var 1)))))

@[simp] theorem subst_allSides {l : ℕ} (σ : Fin n → PTm l) (N B : PTm n) :
    (allSides N B).subst σ = allSides (Syn.subst σ N) (Syn.subst σ B) := by
  simp only [allSides, Fm.subst_all, Fm.subst_imp, subst_lt, subst_length, subst_sides,
    subst_fstT, subst_sndT, subst_entry, Syn.subst_var, Syn.up_zero, Syn.up_succ,
    Syn.subst_shift, Syn.shift_subst]
@[simp] theorem subst_disjoint {l : ℕ} (σ : Fin n → PTm l) (N B : PTm n) :
    (disjoint N B).subst σ = disjoint (Syn.subst σ N) (Syn.subst σ B) := by
  simp only [disjoint, Fm.subst_all, Fm.subst_imp, subst_lt, subst_length, subst_separated,
    subst_fstT, subst_sndT, subst_entry, Syn.subst_var, Syn.up_zero, Syn.up_one, Syn.up_succ,
    Syn.subst_shift, Syn.shift_subst, Syn.shift_var, Fin.succ_zero_eq_one]

theorem allSides_at (N B j : PTm n) (h : Γ ⊢[PRAAx] allSides N B)
    (hj : Γ ⊢[PRAAx] lt j (length B)) :
    Γ ⊢[PRAAx] sides N (fstT (entry B j)) (sndT (entry B j)) := by
  have all := Prf.allE j h
  simp only [allSides, Fm.subst_imp, subst_lt, subst_length, subst_sides, subst_fstT, subst_sndT,
    subst_entry, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at all
  exact .impE all hj

theorem disjoint_at (N B i j : PTm n) (h : Γ ⊢[PRAAx] disjoint N B)
    (hj : Γ ⊢[PRAAx] lt j (length B)) (hij : Γ ⊢[PRAAx] lt i j) :
    Γ ⊢[PRAAx] separated N (fstT (entry B i)) (sndT (entry B i)) (fstT (entry B j)) (sndT (entry B j)) := by
  have first : Γ ⊢[PRAAx] lt j (length B) ⟶ .all (lt (var 0) (Syn.shift j) ⟶
      separated (Syn.shift N) (fstT (entry (Syn.shift B) (var 0))) (sndT (entry (Syn.shift B) (var 0)))
        (fstT (entry (Syn.shift B) (Syn.shift j))) (sndT (entry (Syn.shift B) (Syn.shift j)))) := by
    simpa only [disjoint, Fm.subst_all, Fm.subst_imp, subst_lt, subst_length, subst_separated,
      subst_fstT, subst_sndT, subst_entry, Syn.subst_var, Syn.inst_zero, Syn.up_zero, Syn.up_one,
      Syn.up_succ, Syn.subst_inst_shift, LeanProofs.IPRA.AnalyticNumberTheory.Fermat.subst_up_shift'] using Prf.allE j h
  have contract : Γ ⊢[PRAAx] lt i j ⟶ separated N (fstT (entry B i)) (sndT (entry B i)) (fstT (entry B j)) (sndT (entry B j)) := by
    simpa only [Fm.subst_imp, subst_lt, subst_separated, subst_fstT, subst_sndT, subst_entry,
      Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE i (Prf.impE first hj)
  exact .impE contract hij


/-- Congruence through the actual sequence constructor avoids expanding its
primitive-recursion program during endpoint equality replacement. -/
theorem sequence_parameter_congr (body : PTm 2) (N x y : PTm n) (he : Γ ⊢[PRAAx] x ≐ y) :
    Γ ⊢[PRAAx] Foundations.MasterCertificate.sequence body N x ≐ Foundations.MasterCertificate.sequence body N y :=
  congrPairT (.eqRefl N) (congrAp2 (Foundations.MasterCertificate.stackF body) (.eqRefl N) he)

theorem widths_box_congr (N B j j' : PTm n) (he : Γ ⊢[PRAAx] j ≐ j') :
    Γ ⊢[PRAAx] MinkowskiBoxes.widths N (fstT (entry B j)) (sndT (entry B j)) ≐
      MinkowskiBoxes.widths N (fstT (entry B j')) (sndT (entry B j')) :=
  sequence_parameter_congr MinkowskiBoxes.widthsBody N _ _
    (congrPairT (congrFst (entry_congr (.eqRefl B) he)) (congrSnd (entry_congr (.eqRefl B) he)))

theorem count_box_congr (N B j j' : PTm n) (he : Γ ⊢[PRAAx] j ≐ j') :
    Γ ⊢[PRAAx] count N (fstT (entry B j)) (sndT (entry B j)) ≐ count N (fstT (entry B j')) (sndT (entry B j')) :=
  congrAp2 (prodF MinkowskiMixedRadix.widthBody) (.eqRefl N) (widths_box_congr N B j j' he)

theorem point_box_congr (N B j j' i : PTm n) (he : Γ ⊢[PRAAx] j ≐ j') :
    Γ ⊢[PRAAx] point N (fstT (entry B j)) (sndT (entry B j)) i ≐ point N (fstT (entry B j')) (sndT (entry B j')) i :=
  sequence_parameter_congr MinkowskiBoxes.pointBody N _ _
    (congrPairT (congrFst (entry_congr (.eqRefl B) he))
      (congrPairT (widths_box_congr N B j j' he) (.eqRefl i)))

/-- Two ordered global indices located in one box have ordered local indices,
so the proved within-box digit search supplies their decoded difference. -/
theorem same_box_distinct (N B q r : PTm n) (h : Γ ⊢[PRAAx] allSides N B)
    (hq : Γ ⊢[PRAAx] lt q (total N B)) (hr : Γ ⊢[PRAAx] lt r (total N B))
    (hqr : Γ ⊢[PRAAx] lt q r) (he : Γ ⊢[PRAAx] location N B q ≐ location N B r) :
    Γ ⊢[PRAAx] MinkowskiMesh.differentCoordinate N (entry (boxes N B) q) (entry (boxes N B) r) := by
  have sq := location_spec N B q hq
  have sr := location_spec N B r hr
  have sideq := allSides_at N B (location N B q) h (Prf.andE₁ sq)
  have countEq := count_box_congr N B _ _ he
  have lrBound := lt_congr (.eqRefl _) countEq.eqSymm (Prf.andE₁ (Prf.andE₂ sr))
  have prefixEq : Γ ⊢[PRAAx] prefixCount N B (location N B q) ≐ prefixCount N B (location N B r) :=
    congrAp3 _ he (.eqRefl B) (.eqRefl N)
  have reindex : Γ ⊢[PRAAx] lt
      (prefixCount N B (location N B q)+localIndex N B q)
      (prefixCount N B (location N B q)+localIndex N B r) :=
    lt_congr (Prf.andE₂ (Prf.andE₂ sq))
      ((Prf.andE₂ (Prf.andE₂ sr)).eqTrans (congrAdd prefixEq.eqSymm (.eqRefl _))) hqr
  have localLt : Γ ⊢[PRAAx] lt (localIndex N B q) (localIndex N B r) :=
    le_of_add_le_add_right (le_congr (by ipra_ring) (by ipra_ring) reindex)
  have different := MinkowskiBoxes.point_distinct N (fstT (entry B (location N B q))) (sndT (entry B (location N B q)))
    (localIndex N B q) (localIndex N B r) sideq (Prf.andE₁ (Prf.andE₂ sq)) lrBound localLt
  exact MinkowskiBoxes.differentCoordinate_congr N _ _ _ _ (located_point N B q hq).eqSymm
    ((point_box_congr N B _ _ _ he).eqTrans (located_point N B r hr).eqSymm) different

/-- Two different ordered located boxes have a source-provided separating axis;
the derived half-open bounds make their actual selected points different. -/
theorem cross_box_distinct (N B q r : PTm n) (h : Γ ⊢[PRAAx] allSides N B)
    (hd : Γ ⊢[PRAAx] disjoint N B) (hq : Γ ⊢[PRAAx] lt q (total N B)) (hr : Γ ⊢[PRAAx] lt r (total N B))
    (hl : Γ ⊢[PRAAx] lt (location N B q) (location N B r)) :
    Γ ⊢[PRAAx] MinkowskiMesh.differentCoordinate N (entry (boxes N B) q) (entry (boxes N B) r) := by
  have sq := location_spec N B q hq
  have sr := location_spec N B r hr
  have different := separated_points N _ _ _ _ (localIndex N B q) (localIndex N B r)
    (allSides_at N B (location N B q) h (Prf.andE₁ sq))
    (allSides_at N B (location N B r) h (Prf.andE₁ sr))
    (disjoint_at N B (location N B q) (location N B r) hd (Prf.andE₁ sr) hl)
  exact MinkowskiBoxes.differentCoordinate_congr N _ _ _ _ (located_point N B q hq).eqSymm
    (located_point N B r hr).eqSymm different

/-- Full decoded-coordinate distinctness at arbitrary global indices of the
actual concatenation, from actual endpoint guards and source separation. -/
theorem boxes_distinct (N B q r : PTm n) (h : Γ ⊢[PRAAx] allSides N B)
    (hd : Γ ⊢[PRAAx] disjoint N B) (hq : Γ ⊢[PRAAx] lt q (total N B)) (hr : Γ ⊢[PRAAx] lt r (total N B))
    (hqr : Γ ⊢[PRAAx] lt q r) :
    Γ ⊢[PRAAx] MinkowskiMesh.differentCoordinate N (entry (boxes N B) q) (entry (boxes N B) r) := by
  refine .orE (lt_or_le (location N B q) (location N B r)) ?_ ?_
  · exact cross_box_distinct _ _ _ _ h.wk hd.wk hq.wk hr.wk Prf.hyp0
  · refine .orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_
    · exact differentCoordinate_symm _ _ _ (cross_box_distinct _ _ _ _ h.wk.wk hd.wk.wk hr.wk.wk hq.wk.wk Prf.hyp0)
    · exact same_box_distinct _ _ _ _ h.wk.wk hq.wk.wk hr.wk.wk hqr.wk.wk Prf.hyp0.eqSymm

/-- Arbitrary actual global lookup has a proved box location, stored point
shape, and half-open membership in that supplied box. -/
theorem located_inside (N B q : PTm n) (h : Γ ⊢[PRAAx] allSides N B)
    (hq : Γ ⊢[PRAAx] lt q (total N B)) :
    Γ ⊢[PRAAx] (length (entry (boxes N B) q) ≐ N) ⋏
      inside N (fstT (entry B (location N B q))) (sndT (entry B (location N B q))) (entry (boxes N B) q) := by
  have spec := location_spec N B q hq
  have guards := allSides_at N B _ h (Prf.andE₁ spec)
  exact .andI ((congrFst (located_point N B q hq)).eqTrans (MinkowskiBoxes.point_length _ _ _ _))
    (MinkowskiBoxes.inside_congr _ _ _ _ _ (located_point N B q hq).eqSymm (MinkowskiBoxes.point_inside _ _ _ _ guards))


/-- Restrict the actual global distinctness theorem to the actual m^N+1 prefix. -/
theorem union_prefixDistinct (N m B : PTm n) (h : Γ ⊢[PRAAx] allSides N B)
    (hd : Γ ⊢[PRAAx] disjoint N B)
    (hsize : Γ ⊢[PRAAx] le (succ (MinkowskiMesh.horizon N m)) (total N B)) :
    Γ ⊢[PRAAx] MinkowskiMesh.prefixDistinct N m (boxes N B) := by
  refine .allI (.impI (.allI (.impI ?_)))
  let Δ := lt (var 0) (var 1) ::
    le (var 1) (MinkowskiMesh.horizon (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift m))) ::
      (Γ.map Fm.shift).map Fm.shift
  have guards : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      allSides (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift B)) := by
    simpa only [Fm.shift, subst_allSides, Syn.shift] using h.shift.shift
  have apart : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      disjoint (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift B)) := by
    simpa only [Fm.shift, subst_disjoint, Syn.shift] using hd.shift.shift
  have enough : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      le (succ (MinkowskiMesh.horizon (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift m))))
        (total (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift B))) := by
    simpa only [Fm.shift, subst_le, ConciseIPRA.PTm.subst_succ,
      MinkowskiMesh.subst_horizon, subst_total, Syn.shift] using hsize.shift.shift
  have rbound : Δ ⊢[PRAAx] lt (var 1) (total (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift B))) :=
    le_trans ((succ_monus_succ _ _).eqTrans Prf.hyp1) enough.wk.wk
  have qbound := lt_of_lt_of_le (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (var 1)) (le_of_lt rbound)
  have out := boxes_distinct _ _ _ _ guards.wk.wk apart.wk.wk qbound rbound Prf.hyp0
  simpa only [List.map_cons, Fm.shift, subst_le, MinkowskiMesh.subst_horizon, Syn.shift,
    Syn.subst_var, Fin.succ_zero_eq_one, subst_boxes] using out

/-- Full integer-box-union mesh extraction. Only source endpoint positivity,
separating axes, positive modulus and an actual total-count inequality are
premises; the enumeration, location and decoded-distinctness are proved. -/
theorem union_mesh (N m B : PTm n) (h : Γ ⊢[PRAAx] allSides N B)
    (hd : Γ ⊢[PRAAx] disjoint N B) (hm : Γ ⊢[PRAAx] le one m)
    (hsize : Γ ⊢[PRAAx] le (succ (MinkowskiMesh.horizon N m)) (total N B)) :
    Γ ⊢[PRAAx] MinkowskiMesh.correct N m (boxes N B) (ap3 MinkowskiMesh.meshF N m (boxes N B)) :=
  MinkowskiMesh.mesh_correct N m (boxes N B) hm
    (le_congr (.eqRefl _) (MinkowskiBoxes.boxes_length N B).eqSymm hsize)
    (union_prefixDistinct N m B h hd hsize)

/-- Closed actual locator program metadata. -/
theorem location_program_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (ap3 locationF (var 0) (var 1) (var 2) ≐ location (var 0) (var 1) (var 2)) :=
  closeUniv 3 (location_at _ _ _)

/-- The three variables are dimension, supplied box list, and global index. -/
theorem location_spec_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (lt (var 2) (total (var 0) (var 1)) ⟶
        (lt (location (var 0) (var 1) (var 2)) (length (var 1)) ⋏
          (lt (localIndex (var 0) (var 1) (var 2))
            (count (var 0) (fstT (entry (var 1) (location (var 0) (var 1) (var 2))))
              (sndT (entry (var 1) (location (var 0) (var 1) (var 2))))) ⋏
            (var 2 ≐ prefixCount (var 0) (var 1) (location (var 0) (var 1) (var 2))+localIndex (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.impI (location_spec _ _ _ Prf.hyp0))

theorem located_inside_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (allSides (var 0) (var 1) ⟶ lt (var 2) (total (var 0) (var 1)) ⟶
        ((length (entry (boxes (var 0) (var 1)) (var 2)) ≐ var 0) ⋏
          inside (var 0) (fstT (entry (var 1) (location (var 0) (var 1) (var 2))))
            (sndT (entry (var 1) (location (var 0) (var 1) (var 2)))) (entry (boxes (var 0) (var 1)) (var 2)))) :=
  closeUniv 3 (.impI (.impI (located_inside _ _ _ Prf.hyp1 Prf.hyp0)))

/-- Fully closed decoded distinctness at arbitrary internal global indices. -/
theorem boxes_distinct_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (allSides (var 0) (var 1) ⟶ disjoint (var 0) (var 1) ⟶
        lt (var 2) (total (var 0) (var 1)) ⟶ lt (var 3) (total (var 0) (var 1)) ⟶ lt (var 2) (var 3) ⟶
          MinkowskiMesh.differentCoordinate (var 0) (entry (boxes (var 0) (var 1)) (var 2)) (entry (boxes (var 0) (var 1)) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI
    (boxes_distinct (var 0) (var 1) (var 2) (var 3) Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))

/-- Closed source integer certificate kernel. The variables are dimension,
modulus, and numerical box list. The source additionally assumes N≥1;
the stronger arithmetic sentence includes zero dimension vacuously. -/
theorem union_mesh_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (allSides (var 0) (var 2) ⟶ disjoint (var 0) (var 2) ⟶ le one (var 1) ⟶
        le (succ (MinkowskiMesh.horizon (var 0) (var 1))) (total (var 0) (var 2)) ⟶
          MinkowskiMesh.correct (var 0) (var 1) (boxes (var 0) (var 2))
            (ap3 MinkowskiMesh.meshF (var 0) (var 1) (boxes (var 0) (var 2)))) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (union_mesh (var 0) (var 1) (var 2) Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiBoxUnion
