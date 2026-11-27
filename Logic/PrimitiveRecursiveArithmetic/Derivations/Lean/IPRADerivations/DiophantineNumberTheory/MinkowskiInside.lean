import IPRADerivations.DiophantineNumberTheory.MinkowskiWellFormed
import IPRADerivations.DiophantineNumberTheory.MinkowskiRationalBoxes

/-!
# The original guarded Inside scheme at canonical half-cell centers

The point supplied to the source's `Inside` certificate is the actual
canonical rational vector with coordinates `(2a_k+1)/(2m)`. Doubling is an
actual normalized rational operation. Its result is literally the existing
doubled-center vector, by canonical scalar uniqueness and constructed
sequence equality. Arbitrary membership formulas are transported only by
that literal code equality. Numerical membership parameters remain internal.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiInside

open_ipra exports
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (normalize normalize_preserves_value)
open LeanProofs.IPRA.Analysis.RationalNormalForm (wellFormed normalize_well_formed well_formed_unique denominator_positive)
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiCenters
  (center centerNumerator center_value integer_cancel)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiCenterVectors
  (signedCoordinate centerVector centerBody center_lookup center_body_at center_congr holdsAt holdsAt_congr)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiWellFormed
  (vectorGuard constructed_guard scalar_guard_congr center_vector_guard)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiRationalBoxes (lowerRow upperRow)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_decode sequence_length)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def halfCenter (a : ZT n) (m : PTm n) : PTm n := center a (two*m)
def double (c : PTm n) : PTm n := normalize (ZT.ofNat two*numeratorOf c) (denominatorOf c)
def halfVector (N m a : PTm n) : PTm n := centerVector N (two*m) a
def doubleBody : PTm 2 := double (entry (var 1) (var 0))
def doubleVector (N C : PTm n) : PTm n := sequence doubleBody N C

ipra_subst halfCenter
ipra_subst double
ipra_subst halfVector
ipra_subst doubleVector

theorem doubled_mesh_positive (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] le one (two*m) :=
  le_congr (one_mul one) (.eqRefl _) (le_mul_mono (le_of_eq_add (d := one) (by ipra_ring)) hm)

theorem half_value (a : ZT n) (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] ZT.eq (centerNumerator a*ZT.ofNat (denominatorOf (halfCenter a m)))
      (numeratorOf (halfCenter a m)*ZT.ofNat (two*m)) := center_value _ _ (doubled_mesh_positive m hm)

theorem double_value (c : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (ZT.ofNat two*numeratorOf c*ZT.ofNat (denominatorOf (double c)))
      (numeratorOf (double c)*ZT.ofNat (denominatorOf c)) :=
  normalize_preserves_value _ _ (denominator_positive c)

theorem double_guard (c : PTm n) : Γ ⊢[PRAAx] wellFormed (double c) :=
  normalize_well_formed _ _ (denominator_positive c)

/-- Equality of canonical natural codes, including negative cell indices. -/
theorem double_half_center (a : ZT n) (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] double (halfCenter a m) ≐ center a m := by
  apply well_formed_unique (double (halfCenter a m)) (center a m) (double_guard _) (normalize_well_formed _ _ hm)
  have positive : Γ ⊢[PRAAx] le one (m*denominatorOf (halfCenter a m)) :=
    le_congr (one_mul one) (.eqRefl _) (le_mul_mono hm (denominator_positive _))
  apply integer_cancel (m*denominatorOf (halfCenter a m)) _ _ positive
  ipra_lc [centerNumerator] -𝔞(m)*𝔞(denominatorOf (center a m))*ZT.toZ_eq (double_value (halfCenter a m))- 𝔞(denominatorOf (center a m))*𝔞(denominatorOf (double (halfCenter a m)))*ZT.toZ_eq (half_value a m hm)+ 𝔞(denominatorOf (halfCenter a m))*𝔞(denominatorOf (double (halfCenter a m)))*ZT.toZ_eq (center_value a m hm)

theorem double_congr {c d : PTm n} (h : Γ ⊢[PRAAx] c ≐ d) : Γ ⊢[PRAAx] double c ≐ double d := by
  ipra_congr (double (var 0) : PTm 1) with [h]

theorem half_lookup (N m a k : PTm n) (hk : Γ ⊢[PRAAx] lt k N) :
    Γ ⊢[PRAAx] entry (halfVector N m a) k ≐ halfCenter (signedCoordinate a k) m := center_lookup _ _ _ _ hk

theorem double_lookup (N C k : PTm n) (hk : Γ ⊢[PRAAx] lt k N) :
    Γ ⊢[PRAAx] entry (doubleVector N C) k ≐ double (entry C k) := by
  simpa [doubleVector,doubleBody,inst2] using sequence_decode (Γ := Γ) doubleBody (x := C) hk

theorem half_vector_guard (N m a : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] vectorGuard N (halfVector N m a) := center_vector_guard _ _ _ (doubled_mesh_positive m hm)

theorem double_vector_guard (N C : PTm n) : Γ ⊢[PRAAx] vectorGuard N (doubleVector N C) := by
  apply constructed_guard
  refine .allI (.impI ?_)
  have e := double_lookup (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift)
    (Syn.shift N) (Syn.shift C) (var 0) Prf.hyp0
  simpa only [Syn.shift,doubleVector,Foundations.MasterCertificate.subst_sequence] using
    scalar_guard_congr e.eqSymm (double_guard _)

theorem double_half_vector (N m a : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] doubleVector N (halfVector N m a) ≐ centerVector N m a := by
  apply sequence_equal doubleBody centerBody N (halfVector N m a) (pairT m a)
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have pos : Δ ⊢[PRAAx] le one (Syn.shift m) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hm.shift.wk
  have e := (double_congr (half_lookup (Γ := Δ) (Syn.shift N) (Syn.shift m) (Syn.shift a) (var 0) Prf.hyp0)).eqTrans
    ((double_half_center _ _ pos).eqTrans (center_body_at _ _ _).eqSymm)
  simpa [Δ,doubleBody,inst2,Syn.shift] using e

/-- Original closed rational box membership. Endpoints keep their independent
positive decoded denominators. -/
def boxContains (N B j q : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶
    (rationalLE (entry (lowerRow (Syn.shift B) (Syn.shift j)) (var 0)) (entry (Syn.shift q) (var 0)) ⋏
      rationalLE (entry (Syn.shift q) (var 0)) (entry (upperRow (Syn.shift B) (Syn.shift j)) (var 0))))

@[simp] theorem subst_boxContains {k : ℕ} (σ : Fin n → PTm k) (N B j q : PTm n) :
    (boxContains N B j q).subst σ = boxContains (Syn.subst σ N) (Syn.subst σ B) (Syn.subst σ j) (Syn.subst σ q) := by
  simp only [boxContains,Fm.subst_all,Fm.subst_imp,Fm.subst_and,subst_lt,
    Analysis.RationalArgmin.subst_rationalLE,Foundations.MasterCertificate.subst_entry,
    MinkowskiRationalBoxes.subst_lowerRow,MinkowskiRationalBoxes.subst_upperRow,
    Syn.subst_var,Syn.up_zero,Syn.up_succ,Syn.subst_shift,Syn.shift_subst]

def insideGuarded (Φ : Fm PTm 2) (N B x : PTm n) : Fm PTm n :=
  .all (lt (var 0) (length (Syn.shift B)) ⟶
    .all (vectorGuard (Syn.shift (Syn.shift N)) (var 0) ⟶
      boxContains (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift B)) (var 1) (var 0) ⟶
        holdsAt Φ (doubleVector (Syn.shift (Syn.shift N)) (var 0)) (Syn.shift (Syn.shift x))))

theorem inside_at (Φ : Fm PTm 2) (N B x j q : PTm n)
    (h : Γ ⊢[PRAAx] insideGuarded Φ N B x) (hj : Γ ⊢[PRAAx] lt j (length B))
    (hq : Γ ⊢[PRAAx] vectorGuard N q) (hb : Γ ⊢[PRAAx] boxContains N B j q) :
    Γ ⊢[PRAAx] holdsAt Φ (doubleVector N q) x := by
  have first := Prf.allE j h
  simp only [Fm.subst_imp, Fm.subst_all, subst_lt, MinkowskiWellFormed.subst_vectorGuard,
    Foundations.SequenceComposition.subst_length, subst_boxContains, MinkowskiCenterVectors.subst_holdsAt,
    subst_doubleVector, Syn.subst_var, Syn.up_zero, Syn.up_one, Syn.up_succ, Syn.inst_zero, Syn.inst_succ,
    Syn.subst_shift, Syn.subst_id] at first
  have second := Prf.allE q (Prf.impE first hj)
  have cancel (t : PTm n) : Syn.subst (Syn.inst q) (Syn.subst (fun i => Syn.shift (var i)) t) = t := by
    simpa only [Syn.shift,Syn.subst_var] using Syn.subst_inst_shift q t
  have rule : Γ ⊢[PRAAx] vectorGuard N q ⟶ boxContains N B j q ⟶ holdsAt Φ (doubleVector N q) x := by
    simpa only [Fm.subst_imp,MinkowskiWellFormed.subst_vectorGuard,subst_boxContains,
      MinkowskiCenterVectors.subst_holdsAt,subst_doubleVector,Syn.subst_var,Syn.inst_zero,
      Syn.subst_inst_shift,cancel] using second
  exact .impE (.impE rule hq) hb

/-- This legitimate Inside application takes point-in-box evidence for the
actual canonical half-center; it never assumes membership of the final center. -/
theorem center_from_inside (Φ : Fm PTm 2) (N B x j m a : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (h : Γ ⊢[PRAAx] insideGuarded Φ N B x)
    (hj : Γ ⊢[PRAAx] lt j (length B)) (hb : Γ ⊢[PRAAx] boxContains N B j (halfVector N m a)) :
    Γ ⊢[PRAAx] holdsAt Φ (centerVector N m a) x :=
  holdsAt_congr Φ x (double_half_vector N m a hm)
    (inside_at Φ N B x j _ h hj (half_vector_guard N m a hm) hb)

/-! ## The half-center lies in its original rational box -/

def lowerGap (l : PTm n) (a : ZT n) (c : PTm n) : PTm n :=
  monus (a.pos+(MinkowskiRationalScaling.scaled l c).neg) ((MinkowskiRationalScaling.scaled l c).pos+a.neg)
def upperGap (u : PTm n) (a : ZT n) (c : PTm n) : PTm n :=
  monus ((MinkowskiRationalScaling.scaled u c).pos+a.neg) (succ (a.pos+(MinkowskiRationalScaling.scaled u c).neg))

theorem half_lower_bound (l : PTm n) (a : ZT n) (m c : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hc : Γ ⊢[PRAAx] denominatorOf l*c ≐ m)
    (ha : Γ ⊢[PRAAx] le ((MinkowskiRationalScaling.scaled l c).pos+a.neg)
      (a.pos+(MinkowskiRationalScaling.scaled l c).neg)) :
    Γ ⊢[PRAAx] rationalLE l (halfCenter a m) := by
  change Γ ⊢[PRAAx] le (Analysis.RationalArgmin.left l (halfCenter a m))
    (Analysis.RationalArgmin.left (halfCenter a m) l)
  apply MinkowskiRationalScaling.positive_cancel (doubled_mesh_positive m hm)
  refine le_of_eq_add (d := denominatorOf (halfCenter a m)*denominatorOf l*(two*lowerGap l a c+one)) ?_
  have h := ZT.toZ_eq (half_value (Γ := Γ) a m hm)
  have g := natEq (eq_add_of_le ha)
  have clear := natEq hc
  apply deriveNat
  simp only [centerNumerator,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat] at h
  simp only [ZT.toZ] at h
  unfold Analysis.RationalArgmin.left lowerGap
  simp only [MinkowskiRationalScaling.scaled] at g ⊢
  ipra_simps
  linear_combination -𝔞(denominatorOf l)*h+
    2*𝔞(denominatorOf (halfCenter a m))*𝔞(denominatorOf l)*g+
    2*𝔞(denominatorOf (halfCenter a m))*(𝔞((numeratorOf l).pos)-𝔞((numeratorOf l).neg))*clear

theorem half_upper_bound (u : PTm n) (a : ZT n) (m c : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hc : Γ ⊢[PRAAx] denominatorOf u*c ≐ m)
    (ha : Γ ⊢[PRAAx] lt (a.pos+(MinkowskiRationalScaling.scaled u c).neg)
      ((MinkowskiRationalScaling.scaled u c).pos+a.neg)) :
    Γ ⊢[PRAAx] rationalLE (halfCenter a m) u := by
  change Γ ⊢[PRAAx] le (Analysis.RationalArgmin.left (halfCenter a m) u)
    (Analysis.RationalArgmin.left u (halfCenter a m))
  apply MinkowskiRationalScaling.positive_cancel (doubled_mesh_positive m hm)
  refine le_of_eq_add (d := denominatorOf (halfCenter a m)*denominatorOf u*(two*upperGap u a c+one)) ?_
  have h := ZT.toZ_eq (half_value (Γ := Γ) a m hm)
  have g := natEq (eq_add_of_le ha)
  have clear := natEq hc
  apply deriveNat
  simp only [centerNumerator,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat] at h
  simp only [ZT.toZ] at h
  unfold Analysis.RationalArgmin.left upperGap
  simp only [MinkowskiRationalScaling.scaled] at g ⊢
  ipra_simps
  linear_combination 𝔞(denominatorOf u)*h+
    2*𝔞(denominatorOf (halfCenter a m))*𝔞(denominatorOf u)*g-
    2*𝔞(denominatorOf (halfCenter a m))*(𝔞((numeratorOf u).pos)-𝔞((numeratorOf u).neg))*clear

def cellInside (N B j a : PTm n) : Fm PTm n :=
  MinkowskiBoxes.inside N (fstT (entry (MinkowskiRationalBoxes.integerBoxes N B) j))
    (sndT (entry (MinkowskiRationalBoxes.integerBoxes N B) j)) a

@[simp] theorem subst_cellInside {k : ℕ} (σ : Fin n → PTm k) (N B j a : PTm n) :
    (cellInside N B j a).subst σ = cellInside (Syn.subst σ N) (Syn.subst σ B) (Syn.subst σ j) (Syn.subst σ a) := by simp [cellInside]

theorem cell_inside_at (N B j a k : PTm n) (h : Γ ⊢[PRAAx] cellInside N B j a) (hk : Γ ⊢[PRAAx] lt k N) :
    Γ ⊢[PRAAx] MinkowskiBoxes.insideAt (fstT (entry (MinkowskiRationalBoxes.integerBoxes N B) j))
      (sndT (entry (MinkowskiRationalBoxes.integerBoxes N B) j)) a k := by
  have rule : Γ ⊢[PRAAx] lt k N ⟶ MinkowskiBoxes.insideAt
      (fstT (entry (MinkowskiRationalBoxes.integerBoxes N B) j))
      (sndT (entry (MinkowskiRationalBoxes.integerBoxes N B) j)) a k := by
    simpa only [cellInside,MinkowskiBoxes.inside,Fm.subst_imp,subst_lt,
      MinkowskiBoxes.subst_insideAt,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE k h
  exact .impE rule hk

theorem half_box_coordinate (N B j a k : PTm n) (hj : Γ ⊢[PRAAx] lt j (length B))
    (hk : Γ ⊢[PRAAx] lt k N) (hi : Γ ⊢[PRAAx] cellInside N B j a) :
    Γ ⊢[PRAAx] rationalLE (entry (lowerRow B j) k) (entry (halfVector N (MinkowskiRationalBoxes.mesh N B) a) k) ⋏
      rationalLE (entry (halfVector N (MinkowskiRationalBoxes.mesh N B) a) k) (entry (upperRow B j) k) := by
  have lo := MinkowskiRationalBoxes.normalized_parts N B j (lowerRow B j) k
    (MinkowskiRationalBoxes.lower_row_bound B j hj) hk (MinkowskiRationalBoxes.pool_lower B j hj)
  have up := MinkowskiRationalBoxes.normalized_parts N B (MinkowskiRationalBoxes.upperIndex B j) (upperRow B j) k
    (MinkowskiRationalBoxes.upper_row_bound B j hj) hk (MinkowskiRationalBoxes.pool_upper B j hj)
  have lowerEntry := entry_congr (MinkowskiRationalBoxes.integer_lower N B j hj) (.eqRefl k)
  have upperEntry := entry_congr (MinkowskiRationalBoxes.integer_upper N B j hj) (.eqRefl k)
  have lp := (congrFst lowerEntry).eqTrans (Prf.andE₁ lo)
  have lm := (congrSnd lowerEntry).eqTrans (Prf.andE₁ (Prf.andE₂ lo))
  have up' := (congrFst upperEntry).eqTrans (Prf.andE₁ up)
  have um := (congrSnd upperEntry).eqTrans (Prf.andE₁ (Prf.andE₂ up))
  have hc := cell_inside_at N B j a k hi hk
  have lower : Γ ⊢[PRAAx] le
      ((MinkowskiRationalScaling.scaled (entry (lowerRow B j) k) (Analysis.RationalSupMetric.cofactor (MinkowskiRationalBoxes.pool B) N j k)).pos+(signedCoordinate a k).neg)
      ((signedCoordinate a k).pos+(MinkowskiRationalScaling.scaled (entry (lowerRow B j) k) (Analysis.RationalSupMetric.cofactor (MinkowskiRationalBoxes.pool B) N j k)).neg) :=
    le_congr (congrAdd lp (.eqRefl _)) (congrAdd (.eqRefl _) lm) (Prf.andE₁ hc)
  have upper : Γ ⊢[PRAAx] lt
      ((signedCoordinate a k).pos+(MinkowskiRationalScaling.scaled (entry (upperRow B j) k)
        (Analysis.RationalSupMetric.cofactor (MinkowskiRationalBoxes.pool B) N (MinkowskiRationalBoxes.upperIndex B j) k)).neg)
      ((MinkowskiRationalScaling.scaled (entry (upperRow B j) k)
        (Analysis.RationalSupMetric.cofactor (MinkowskiRationalBoxes.pool B) N (MinkowskiRationalBoxes.upperIndex B j) k)).pos+(signedCoordinate a k).neg) :=
    lt_congr (congrAdd (.eqRefl _) um) (congrAdd up' (.eqRefl _)) (Prf.andE₂ hc)
  have lbound := half_lower_bound _ (signedCoordinate a k) _ _ (MinkowskiRationalBoxes.mesh_positive N B)
    (Prf.andE₂ (Prf.andE₂ lo)) lower
  have ubound := half_upper_bound _ (signedCoordinate a k) _ _ (MinkowskiRationalBoxes.mesh_positive N B)
    (Prf.andE₂ (Prf.andE₂ up)) upper
  have look := half_lookup N (MinkowskiRationalBoxes.mesh N B) a k hk
  exact .andI (Analysis.RationalArgmin.rationalLE_congr (.eqRefl _) look.eqSymm lbound)
    (Analysis.RationalArgmin.rationalLE_congr look.eqSymm (.eqRefl _) ubound)

theorem half_box_contains (N B j a : PTm n) (hj : Γ ⊢[PRAAx] lt j (length B))
    (hi : Γ ⊢[PRAAx] cellInside N B j a) :
    Γ ⊢[PRAAx] boxContains N B j (halfVector N (MinkowskiRationalBoxes.mesh N B) a) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have jbound : Δ ⊢[PRAAx] lt (Syn.shift j) (length (Syn.shift B)) := by
    simpa only [Fm.shift,subst_lt,Foundations.SequenceComposition.subst_length,Syn.shift] using hj.shift.wk
  have member : Δ ⊢[PRAAx] cellInside (Syn.shift N) (Syn.shift B) (Syn.shift j) (Syn.shift a) := by
    simpa only [Fm.shift,subst_cellInside,Syn.shift] using hi.shift.wk
  have r := half_box_coordinate (Syn.shift N) (Syn.shift B) (Syn.shift j) (Syn.shift a) (var 0) jbound Prf.hyp0 member
  simpa only [Δ,Syn.shift,subst_halfVector,MinkowskiRationalBoxes.subst_mesh] using r

/-- The producer-facing original Inside endpoint. Both the box location and
the canonical rational half-center's original endpoint bounds are derived
from the actual enumerated integer cell. -/
theorem enumerated_center_membership (Φ : Fm PTm 2) (N B x q : PTm n)
    (hSides : Γ ⊢[PRAAx] MinkowskiRationalBoxes.rationalSides N B)
    (hInside : Γ ⊢[PRAAx] insideGuarded Φ N B x)
    (hq : Γ ⊢[PRAAx] lt q (MinkowskiBoxUnion.total N (MinkowskiRationalBoxes.integerBoxes N B))) :
    Γ ⊢[PRAAx] holdsAt Φ (centerVector N (MinkowskiRationalBoxes.mesh N B)
      (entry (MinkowskiBoxes.boxes N (MinkowskiRationalBoxes.integerBoxes N B)) q)) x := by
  have loc := MinkowskiBoxUnion.location_spec N (MinkowskiRationalBoxes.integerBoxes N B) q hq
  have hj := lt_congr (.eqRefl _) (MinkowskiRationalBoxes.integerBoxes_length N B) (Prf.andE₁ loc)
  have point := MinkowskiBoxUnion.located_inside N (MinkowskiRationalBoxes.integerBoxes N B) q
    (MinkowskiRationalBoxes.integer_allSides N B hSides) hq
  exact center_from_inside Φ N B x _ _ _ (MinkowskiRationalBoxes.mesh_positive N B) hInside hj
    (half_box_contains N B _ _ hj (Prf.andE₂ point))

/-! ## Actual PR metadata and fully internal closed endpoints -/

def halfVectorF : PR 3 := PTm.toPR (halfVector (var 0) (var 1) (var 2))
def doubleVectorF : PR 2 := PTm.toPR (doubleVector (var 0) (var 1))
def doubleF : PR 1 := PTm.toPR (double (var 0))

theorem half_vector_at (N m a : PTm n) : Γ ⊢[PRAAx] ap3 halfVectorF N m a ≐ halfVector N m a := by
  simpa [halfVectorF,ap3] using toPR_eq (Γ := Γ) (halfVector (var 0) (var 1) (var 2) : PTm 3) ![N,m,a]
theorem double_vector_at (N C : PTm n) : Γ ⊢[PRAAx] ap2 doubleVectorF N C ≐ doubleVector N C := by
  simpa [doubleVectorF,ap2] using toPR_eq (Γ := Γ) (doubleVector (var 0) (var 1) : PTm 2) ![N,C]
theorem double_at (c : PTm n) : Γ ⊢[PRAAx] ap1 doubleF c ≐ double c := by
  simpa [doubleF,ap1] using toPR_eq (Γ := Γ) (double (var 0) : PTm 1) ![c]

theorem canonical_doubling_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶
      (vectorGuard (var 0) (halfVector (var 0) (var 1) (var 2)) ⋏
        (vectorGuard (var 0) (doubleVector (var 0) (halfVector (var 0) (var 1) (var 2))) ⋏
          (doubleVector (var 0) (halfVector (var 0) (var 1) (var 2)) ≐ centerVector (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.impI (.andI (half_vector_guard _ _ _ Prf.hyp0)
    (.andI (double_vector_guard _ _) (double_half_vector _ _ _ Prf.hyp0))))

theorem half_center_containment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2) (length (var 1)) ⟶ cellInside (var 0) (var 1) (var 2) (var 3) ⟶
      boxContains (var 0) (var 1) (var 2) (halfVector (var 0) (MinkowskiRationalBoxes.mesh (var 0) (var 1)) (var 3))) :=
  closeUniv 4 (.impI (.impI (half_box_contains _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem enumerated_membership_closed (Φ : Fm PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (MinkowskiRationalBoxes.rationalSides (var 0) (var 1) ⟶ insideGuarded Φ (var 0) (var 1) (var 2) ⟶
      lt (var 3) (MinkowskiBoxUnion.total (var 0) (MinkowskiRationalBoxes.integerBoxes (var 0) (var 1))) ⟶
        holdsAt Φ (centerVector (var 0) (MinkowskiRationalBoxes.mesh (var 0) (var 1))
          (entry (MinkowskiBoxes.boxes (var 0) (MinkowskiRationalBoxes.integerBoxes (var 0) (var 1))) (var 3))) (var 2)) :=
  closeUniv 4 (.impI (.impI (.impI (enumerated_center_membership Φ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem inside_programs_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((ap3 halfVectorF (var 0) (var 1) (var 2) ≐ halfVector (var 0) (var 1) (var 2)) ⋏
      ((ap2 doubleVectorF (var 0) (var 1) ≐ doubleVector (var 0) (var 1)) ⋏
        (ap1 doubleF (var 0) ≐ double (var 0)))) :=
  closeUniv 3 (.andI (half_vector_at _ _ _) (.andI (double_vector_at _ _) (double_at _)))

end LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiInside
