import IPRADerivations.DiophantineNumberTheory.MinkowskiMixedRadix
import IPRADerivations.DiophantineNumberTheory.MinkowskiMesh
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# Runtime-dimensional integer-box point lists

Minkowski packet, paper/01_foundations.tex and paper/02_finite_proof.tex:
the exact integer box associated to signed lower and upper vectors is
enumerated by the mixed-radix digits of its actual positive side widths.
Every bound, endpoint, coordinate and enumeration index is internal.

Endpoint coordinates denote arbitrary natural pairs. Their positive
natural difference is computed by monus of cross sums and proved to be
exact from the strict endpoint inequalities. The actual list has the
product of those widths as its stored length. Its point entries have the
runtime dimension as stored length, are in the half-open integer box, and
are decoded-coordinate distinct at different in-range indices.

Coordinate lookup uses the literal total MasterCertificate decoder. Input
endpoint-vector stored lengths are not assumed, and no zero padding is
asserted. Rational denominator clearing, geometric containment, and the
BoxOK volume/disjoint-box producer remain separate from this integer kernel.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiBoxes

open_ipra
open LeanProofs.IPRA.Foundations.MasterCertificate
  (entry sequence sequence_length sequence_decode subst_entry subst_sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.DiophantineNumberTheory.SignedEuclidean (decode pack)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev lower (L k : PTm n) : ZT n := decode (entry L k)
abbrev upper (U k : PTm n) : ZT n := decode (entry U k)
/-- Exact positive signed width, when the endpoint guard holds. -/
def width (L U k : PTm n) : PTm n :=
  monus ((upper U k).pos+(lower L k).neg) ((lower L k).pos+(upper U k).neg)
def side (L U k : PTm n) : Fm PTm n :=
  lt ((lower L k).pos+(upper U k).neg) ((upper U k).pos+(lower L k).neg)
def sides (N L U : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ side (Syn.shift L) (Syn.shift U) (var 0))

@[simp] theorem subst_width {l : ℕ} (σ : Fin n → PTm l) (L U k : PTm n) :
    Syn.subst σ (width L U k) = width (Syn.subst σ L) (Syn.subst σ U) (Syn.subst σ k) := by
  simp only [width, lower, upper, decode, PTm.subst_monus, PTm.subst_add, subst_fstT, subst_sndT, subst_entry]
@[simp] theorem subst_side {l : ℕ} (σ : Fin n → PTm l) (L U k : PTm n) :
    (side L U k).subst σ = side (Syn.subst σ L) (Syn.subst σ U) (Syn.subst σ k) := by
  simp only [side, lower, upper, decode, subst_lt, PTm.subst_add, subst_fstT, subst_sndT, subst_entry]
@[simp] theorem subst_sides {l : ℕ} (σ : Fin n → PTm l) (N L U : PTm n) :
    (sides N L U).subst σ = sides (Syn.subst σ N) (Syn.subst σ L) (Syn.subst σ U) := by
  simp only [sides, Fm.subst_all, Fm.subst_imp, subst_lt, subst_side, Syn.subst_var,
    Syn.up_zero, Syn.up_succ, Syn.subst_shift, Syn.shift_subst]

theorem side_at (N L U k : PTm n) (h : Γ ⊢[PRAAx] sides N L U)
    (hk : Γ ⊢[PRAAx] lt k N) : Γ ⊢[PRAAx] side L U k := by
  have all := Prf.allE k h
  simp only [sides, Fm.subst_imp, subst_lt, subst_side, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at all
  exact .impE all hk

theorem width_positive (L U k : PTm n) (h : Γ ⊢[PRAAx] side L U k) :
    Γ ⊢[PRAAx] le one (width L U k) := by
  have reconstruct := eq_add_of_le (le_of_lt h)
  exact le_of_add_le_add_right (le_congr (by ipra_ring)
    (reconstruct.eqTrans (add_comm _ _)) h)

/-- The natural width is proved equal to the difference of the decoded signed
endpoints. This is not a width supplied alongside the endpoints. -/
theorem width_exact (L U k : PTm n) (h : Γ ⊢[PRAAx] side L U k) :
    Γ ⊢[PRAAx] ZT.eq (upper U k-lower L k) (ZT.ofNat (width L U k)) := by
  apply ZT.derive
  have e := natEq (eq_add_of_le (le_of_lt h))
  rw [ZT.toZ_sub, ZT.toZ_ofNat]
  simp only [ZT.toZ, width]
  simp only [Q.mk_add, map_add] at e
  linear_combination e

def widthsBody : PTm 2 := width (fstT (var 1)) (sndT (var 1)) (var 0)
def widths (N L U : PTm n) : PTm n := sequence widthsBody N (pairT L U)

@[simp] theorem subst_widths {l : ℕ} (σ : Fin n → PTm l) (N L U : PTm n) :
    Syn.subst σ (widths N L U) = widths (Syn.subst σ N) (Syn.subst σ L) (Syn.subst σ U) := by
  simp only [widths, subst_sequence, subst_pairT]

theorem widths_length (N L U : PTm n) : Γ ⊢[PRAAx] length (widths N L U) ≐ N := sequence_length _ _ _

theorem widthsBody_at (L U k : PTm n) :
    Γ ⊢[PRAAx] inst2 widthsBody k (pairT L U) ≐ width L U k := by
  have h := Prf.eqCongr (Γ := Γ) (width (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![fstT (pairT L U),sndT (pairT L U),k]) (σ' := ![L,U,k])
    (fun a => by fin_cases a; exact fst_pair _ _; exact snd_pair _ _; exact .eqRefl _)
  simpa only [widthsBody, inst2, subst_width, subst_fstT, subst_sndT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h

theorem widths_lookup (N L U k : PTm n) (hk : Γ ⊢[PRAAx] lt k N) :
    Γ ⊢[PRAAx] entry (widths N L U) k ≐ width L U k :=
  (sequence_decode widthsBody hk).eqTrans (widthsBody_at L U k)

theorem widths_positive (N L U : PTm n) (h : Γ ⊢[PRAAx] sides N L U) :
    Γ ⊢[PRAAx] MinkowskiMixedRadix.positive N (widths N L U) := by
  refine .allI (.impI ?_)
  have guards : Γ.map Fm.shift ⊢[PRAAx] sides (Syn.shift N) (Syn.shift L) (Syn.shift U) := by
    simpa only [Fm.shift, subst_sides, Syn.shift] using h.shift
  have hp := width_positive _ _ _ (side_at _ _ _ _ guards.wk
    (Prf.hyp0 : lt (var 0) (Syn.shift N) :: Γ.map Fm.shift ⊢[PRAAx] _))
  simpa only [Syn.shift, subst_widths] using
    le_congr (.eqRefl _) (widths_lookup _ _ _ _ Prf.hyp0).eqSymm hp

/-- Actual finite point count, the product of the computed positive widths. -/
def count (N L U : PTm n) : PTm n := MinkowskiMixedRadix.count N (widths N L U)
@[simp] theorem subst_count {l : ℕ} (σ : Fin n → PTm l) (N L U : PTm n) :
    Syn.subst σ (count N L U) = count (Syn.subst σ N) (Syn.subst σ L) (Syn.subst σ U) := by
  simp only [count, MinkowskiMixedRadix.subst_count, subst_widths]

theorem count_positive (N L U : PTm n) (h : Γ ⊢[PRAAx] sides N L U) : Γ ⊢[PRAAx] le one (count N L U) :=
  MinkowskiMixedRadix.count_positive _ _ (widths_positive N L U h)

/-- Coordinates are signed lower endpoints plus actual mixed-radix digits. -/
def coordinate (L W i k : PTm n) : ZT n := lower L k+ZT.ofNat (MinkowskiMixedRadix.digit W i k)
def pointData (L W i : PTm n) : PTm n := pairT L (pairT W i)
def pointBody : PTm 2 := pack (coordinate (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0))
def point (N L U i : PTm n) : PTm n := sequence pointBody N (pointData L (widths N L U) i)

@[simp] theorem subst_coordinate {l : ℕ} (σ : Fin n → PTm l) (L W i k : PTm n) :
    (coordinate L W i k).subst σ = coordinate (Syn.subst σ L) (Syn.subst σ W) (Syn.subst σ i) (Syn.subst σ k) := by
  simp only [coordinate, lower, ZT.subst_add, ZT.subst_ofNat, SignedEuclidean.subst_decode, subst_entry,
    MinkowskiMixedRadix.subst_digit]
@[simp] theorem subst_pointData {l : ℕ} (σ : Fin n → PTm l) (L W i : PTm n) :
    Syn.subst σ (pointData L W i) = pointData (Syn.subst σ L) (Syn.subst σ W) (Syn.subst σ i) := by
  simp only [pointData, subst_pairT]
@[simp] theorem subst_point {l : ℕ} (σ : Fin n → PTm l) (N L U i : PTm n) :
    Syn.subst σ (point N L U i) = point (Syn.subst σ N) (Syn.subst σ L) (Syn.subst σ U) (Syn.subst σ i) := by
  simp only [point, subst_sequence, subst_pointData, subst_widths]

theorem point_length (N L U i : PTm n) : Γ ⊢[PRAAx] length (point N L U i) ≐ N := sequence_length _ _ _

theorem pointBody_at (L W i k : PTm n) :
    Γ ⊢[PRAAx] inst2 pointBody k (pointData L W i) ≐ pack (coordinate L W i k) := by
  have h := Prf.eqCongr (Γ := Γ) (pack (coordinate (var 0) (var 1) (var 2) (var 3)) : PTm 4)
    (σ := ![fstT (pointData L W i),fstT (sndT (pointData L W i)),sndT (sndT (pointData L W i)),k])
    (σ' := ![L,W,i,k]) (fun a => by
      fin_cases a
      · exact fst_pair _ _
      · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
      · exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
      · exact .eqRefl _)
  simpa only [pointBody, inst2, SignedEuclidean.subst_pack, subst_coordinate, subst_fstT, subst_sndT,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using h

theorem point_lookup (N L U i k : PTm n) (hk : Γ ⊢[PRAAx] lt k N) :
    Γ ⊢[PRAAx] entry (point N L U i) k ≐ pack (coordinate L (widths N L U) i k) :=
  (sequence_decode pointBody hk).eqTrans (pointBody_at _ _ _ _)

theorem point_value (N L U i k : PTm n) (hk : Γ ⊢[PRAAx] lt k N) :
    Γ ⊢[PRAAx] ZT.eq (decode (entry (point N L U i) k)) (coordinate L (widths N L U) i k) := by
  have e := point_lookup N L U i k hk
  apply ZT.derive
  simp only [decode, ZT.toZ]
  rw [natEq ((congrFst e).eqTrans (fst_pair _ _)),natEq ((congrSnd e).eqTrans (snd_pair _ _))]

/-- Literal signed half-open coordinate inequalities. -/
def insideAt (L U a k : PTm n) : Fm PTm n :=
  le ((lower L k).pos+(decode (entry a k)).neg) ((decode (entry a k)).pos+(lower L k).neg) ⋏
  lt ((decode (entry a k)).pos+(upper U k).neg) ((upper U k).pos+(decode (entry a k)).neg)
def inside (N L U a : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ insideAt (Syn.shift L) (Syn.shift U) (Syn.shift a) (var 0))

@[simp] theorem subst_insideAt {l : ℕ} (σ : Fin n → PTm l) (L U a k : PTm n) :
    (insideAt L U a k).subst σ = insideAt (Syn.subst σ L) (Syn.subst σ U) (Syn.subst σ a) (Syn.subst σ k) := by
  simp only [insideAt, lower, upper, decode, Fm.subst_and, subst_le, subst_lt, PTm.subst_add,
    subst_fstT, subst_sndT, subst_entry]
@[simp] theorem subst_inside {l : ℕ} (σ : Fin n → PTm l) (N L U a : PTm n) :
    (inside N L U a).subst σ = inside (Syn.subst σ N) (Syn.subst σ L) (Syn.subst σ U) (Syn.subst σ a) := by
  simp only [inside, Fm.subst_all, Fm.subst_imp, subst_lt, subst_insideAt, Syn.subst_var,
    Syn.up_zero, Syn.up_succ, Syn.subst_shift, Syn.shift_subst]

theorem point_inside_at (N L U i k : PTm n) (h : Γ ⊢[PRAAx] sides N L U)
    (hk : Γ ⊢[PRAAx] lt k N) : Γ ⊢[PRAAx] insideAt L U (point N L U i) k := by
  have e := point_lookup N L U i k hk
  have p := (congrFst e).eqTrans (fst_pair _ _)
  have q := (congrSnd e).eqTrans (snd_pair _ _)
  have hs := side_at N L U k h hk
  have digitbound := MinkowskiMixedRadix.digit_bound N (widths N L U) i k (widths_positive N L U h) hk
  have small : Γ ⊢[PRAAx] lt (MinkowskiMixedRadix.digit (widths N L U) i k) (width L U k) :=
    lt_congr (.eqRefl _) (widths_lookup N L U k hk) digitbound
  have reconstruct := eq_add_of_le (le_of_lt hs)
  have lo : Γ ⊢[PRAAx] le ((lower L k).pos+(lower L k).neg)
      ((lower L k).pos+MinkowskiMixedRadix.digit (widths N L U) i k+(lower L k).neg) :=
    le_of_eq_add (d := MinkowskiMixedRadix.digit (widths N L U) i k) (by ipra_ring)
  have hi : Γ ⊢[PRAAx] lt ((lower L k).pos+MinkowskiMixedRadix.digit (widths N L U) i k+(upper U k).neg)
      ((upper U k).pos+(lower L k).neg) :=
    lt_congr (by ipra_ring) reconstruct.eqSymm
      (Foundations.SequenceComposition.add_lt_left ((lower L k).pos+(upper U k).neg) small)
  have p' : Γ ⊢[PRAAx] fstT (entry (point N L U i) k) ≐
      (lower L k).pos+MinkowskiMixedRadix.digit (widths N L U) i k := p
  have q' : Γ ⊢[PRAAx] sndT (entry (point N L U i) k) ≐ (lower L k).neg := q.eqTrans (add_zero _)
  exact .andI (le_congr (congrAdd (.eqRefl _) q'.eqSymm)
    (congrAdd p'.eqSymm (.eqRefl _)) lo)
    (lt_congr (congrAdd p'.eqSymm (.eqRefl _)) (congrAdd (.eqRefl _) q'.eqSymm) hi)

theorem point_inside (N L U i : PTm n) (h : Γ ⊢[PRAAx] sides N L U) :
    Γ ⊢[PRAAx] inside N L U (point N L U i) := by
  refine .allI (.impI ?_)
  have guards : Γ.map Fm.shift ⊢[PRAAx] sides (Syn.shift N) (Syn.shift L) (Syn.shift U) := by
    simpa only [Fm.shift, subst_sides, Syn.shift] using h.shift
  simpa only [Syn.shift, subst_point] using
    point_inside_at (Syn.shift N) (Syn.shift L) (Syn.shift U) (Syn.shift i) (var 0) guards.wk Prf.hyp0

/-- Equality of decoded points forces equality of their actual natural digits;
the common signed lower endpoint cancels in the object-theory ring. -/
theorem digit_equal_of_coordinate_equal (N L U i j k : PTm n)
    (hk : Γ ⊢[PRAAx] lt k N)
    (he : Γ ⊢[PRAAx] ZT.eq (decode (entry (point N L U i) k)) (decode (entry (point N L U j) k))) :
    Γ ⊢[PRAAx] MinkowskiMixedRadix.digit (widths N L U) i k ≐ MinkowskiMixedRadix.digit (widths N L U) j k := by
  ipra_lc [coordinate] -ZT.toZ_eq (point_value N L U i k hk)+ZT.toZ_eq (point_value N L U j k hk)+ZT.toZ_eq he

/-- Different valid mixed-radix indices give an explicit coordinate witnessing
difference of the decoded signed points. The witness is the actual finite
mixed-radix comparison search, not an assumed inequality of point codes. -/
theorem point_distinct (N L U i j : PTm n) (h : Γ ⊢[PRAAx] sides N L U)
    (hi : Γ ⊢[PRAAx] lt i (count N L U)) (hj : Γ ⊢[PRAAx] lt j (count N L U))
    (hij : Γ ⊢[PRAAx] lt i j) :
    Γ ⊢[PRAAx] MinkowskiMesh.differentCoordinate N (point N L U i) (point N L U j) := by
  have ne : Γ ⊢[PRAAx] neg (i ≐ j) :=
    .impI (lt_irrefl i _ (lt_congr (.eqRefl _) Prf.hyp0.eqSymm hij.wk))
  have found := MinkowskiMixedRadix.differentIndex_spec N (widths N L U) i j (widths_positive N L U h) hi hj ne
  let k := MinkowskiMixedRadix.differentIndex N (widths N L U) i j
  have different : Γ ⊢[PRAAx] neg (ZT.eq (decode (entry (point N L U i) k)) (decode (entry (point N L U j) k))) :=
    .impI (.impE (Prf.andE₂ found).wk (digit_equal_of_coordinate_equal N L U i j k (Prf.andE₁ found).wk Prf.hyp0))
  refine .exI k ?_
  simpa only [MinkowskiMesh.differentCoordinate, Fm.subst_and, subst_lt, subst_neg, ZT.subst_eq,
    SignedEuclidean.subst_decode, subst_entry, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using
    (Prf.andI (Prf.andE₁ found) different)

/-- Actual outer list of all mixed-radix indices below the computed count. -/
def pointsData (N L U : PTm n) : PTm n := pairT N (pairT L U)
def pointsBody : PTm 2 := point (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def points (N L U : PTm n) : PTm n := sequence pointsBody (count N L U) (pointsData N L U)
def pointsF : PR 3 := PTm.toPR (points (var 0) (var 1) (var 2))

@[simp] theorem subst_pointsData {l : ℕ} (σ : Fin n → PTm l) (N L U : PTm n) :
    Syn.subst σ (pointsData N L U) = pointsData (Syn.subst σ N) (Syn.subst σ L) (Syn.subst σ U) := by
  simp only [pointsData, subst_pairT]
@[simp] theorem subst_points {l : ℕ} (σ : Fin n → PTm l) (N L U : PTm n) :
    Syn.subst σ (points N L U) = points (Syn.subst σ N) (Syn.subst σ L) (Syn.subst σ U) := by
  simp only [points, subst_sequence, subst_count, subst_pointsData]

theorem points_at (N L U : PTm n) : Γ ⊢[PRAAx] ap3 pointsF N L U ≐ points N L U := by
  have h := toPR_eq (Γ := Γ) (points (var 0) (var 1) (var 2) : PTm 3) ![N,L,U]
  simpa only [pointsF, ap3, subst_points, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h

theorem points_length (N L U : PTm n) : Γ ⊢[PRAAx] length (points N L U) ≐ count N L U := sequence_length _ _ _

theorem pointsBody_at (N L U i : PTm n) :
    Γ ⊢[PRAAx] inst2 pointsBody i (pointsData N L U) ≐ point N L U i := by
  have h := Prf.eqCongr (Γ := Γ) (point (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![fstT (pointsData N L U),fstT (sndT (pointsData N L U)),sndT (sndT (pointsData N L U)),i])
    (σ' := ![N,L,U,i]) (fun a => by
      fin_cases a
      · exact fst_pair _ _
      · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
      · exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
      · exact .eqRefl _)
  simpa only [pointsBody, inst2, subst_point, subst_fstT, subst_sndT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using h

theorem points_lookup (N L U i : PTm n) (hi : Γ ⊢[PRAAx] lt i (count N L U)) :
    Γ ⊢[PRAAx] entry (points N L U) i ≐ point N L U i :=
  (sequence_decode pointsBody hi).eqTrans (pointsBody_at N L U i)

theorem inside_congr (N L U a b : PTm n) (he : Γ ⊢[PRAAx] a ≐ b)
    (h : Γ ⊢[PRAAx] inside N L U a) : Γ ⊢[PRAAx] inside N L U b := by
  have input : Γ ⊢[PRAAx] (inside (var 0) (var 1) (var 2) (var 3)).subst ![N,L,U,a] := by
    simpa only [subst_inside, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using h
  have out := Prf.eqSubst (inside (var 0) (var 1) (var 2) (var 3)) ![N,L,U,a] ![N,L,U,b]
    (fun k => by fin_cases k <;> first | exact he | exact .eqRefl _) input
  simpa only [subst_inside, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using out

theorem differentCoordinate_congr (N a b a' b' : PTm n) (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b')
    (h : Γ ⊢[PRAAx] MinkowskiMesh.differentCoordinate N a b) : Γ ⊢[PRAAx] MinkowskiMesh.differentCoordinate N a' b' := by
  have input : Γ ⊢[PRAAx] (MinkowskiMesh.differentCoordinate (var 0) (var 1) (var 2)).subst ![N,a,b] := by
    simpa only [MinkowskiMesh.subst_differentCoordinate, Syn.subst_var, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h
  have out := Prf.eqSubst (MinkowskiMesh.differentCoordinate (var 0) (var 1) (var 2)) ![N,a,b] ![N,a',b']
    (fun k => by fin_cases k <;> first | exact ha | exact hb | exact .eqRefl _) input
  simpa only [MinkowskiMesh.subst_differentCoordinate, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using out

/-- Each in-range entry is a genuine runtime-dimensional point in the box. -/
theorem points_inside (N L U i : PTm n) (h : Γ ⊢[PRAAx] sides N L U)
    (hi : Γ ⊢[PRAAx] lt i (count N L U)) :
    Γ ⊢[PRAAx] (length (entry (points N L U) i) ≐ N) ⋏ inside N L U (entry (points N L U) i) :=
  .andI ((congrFst (points_lookup N L U i hi)).eqTrans (point_length N L U i))
    (inside_congr N L U _ _ (points_lookup N L U i hi).eqSymm (point_inside N L U i h))

/-- Decoded-vector distinctness of the actual enumerated list follows from
mixed-radix injectivity and the endpoint offset cancellation. -/
theorem points_distinct (N L U i j : PTm n) (h : Γ ⊢[PRAAx] sides N L U)
    (hi : Γ ⊢[PRAAx] lt i (count N L U)) (hj : Γ ⊢[PRAAx] lt j (count N L U))
    (hij : Γ ⊢[PRAAx] lt i j) :
    Γ ⊢[PRAAx] MinkowskiMesh.differentCoordinate N (entry (points N L U) i) (entry (points N L U) j) :=
  differentCoordinate_congr N _ _ _ _ (points_lookup N L U i hi).eqSymm
    (points_lookup N L U j hj).eqSymm (point_distinct N L U i j h hi hj hij)

/-- Restrict the proved decoded distinctness to the actual pigeonhole prefix. -/
theorem points_prefixDistinct (N m L U : PTm n) (h : Γ ⊢[PRAAx] sides N L U)
    (hsize : Γ ⊢[PRAAx] le (succ (MinkowskiMesh.horizon N m)) (count N L U)) :
    Γ ⊢[PRAAx] MinkowskiMesh.prefixDistinct N m (points N L U) := by
  refine .allI (.impI (.allI (.impI ?_)))
  let Δ := lt (var 0) (var 1) ::
    le (var 1) (MinkowskiMesh.horizon (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift m))) ::
      (Γ.map Fm.shift).map Fm.shift
  have guards : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      sides (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift L)) (Syn.shift (Syn.shift U)) := by
    simpa only [Fm.shift, subst_sides, Syn.shift] using h.shift.shift
  have enough : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      le (succ (MinkowskiMesh.horizon (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift m))))
        (count (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift L)) (Syn.shift (Syn.shift U))) := by
    simpa only [Fm.shift, subst_le, ConciseIPRA.PTm.subst_succ,
      MinkowskiMesh.subst_horizon, subst_count, Syn.shift] using hsize.shift.shift
  have jbound : Δ ⊢[PRAAx] lt (var 1)
      (count (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift L)) (Syn.shift (Syn.shift U))) :=
    le_trans ((succ_monus_succ _ _).eqTrans Prf.hyp1) enough.wk.wk
  have ibound := lt_of_lt_of_le (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (var 1)) (le_of_lt jbound)
  have out := points_distinct _ _ _ _ _ guards.wk.wk ibound jbound Prf.hyp0
  simpa only [List.map_cons, Fm.shift, subst_le, MinkowskiMesh.subst_horizon, Syn.shift,
    Syn.subst_var, Fin.succ_zero_eq_one, subst_points] using out

/-- One actual integer box already supplies the full mesh extractor input when
its computed product count is large enough. No distinctness premise remains. -/
theorem box_mesh (N m L U : PTm n) (h : Γ ⊢[PRAAx] sides N L U)
    (hm : Γ ⊢[PRAAx] le one m)
    (hsize : Γ ⊢[PRAAx] le (succ (MinkowskiMesh.horizon N m)) (count N L U)) :
    Γ ⊢[PRAAx] MinkowskiMesh.correct N m (points N L U) (ap3 MinkowskiMesh.meshF N m (points N L U)) :=
  MinkowskiMesh.mesh_correct _ _ _ hm
    (le_congr (.eqRefl _) (points_length N L U).eqSymm hsize)
    (points_prefixDistinct N m L U h hsize)

/-! ## Actual finite concatenation with cumulative product counts -/

/-- A box record is the pair of its lower- and upper-coordinate sequence codes. -/
def boxF : PR 2 := PTm.toPR (points (var 1) (fstT (var 0)) (sndT (var 0)))

theorem box_at (N b : PTm n) :
    Γ ⊢[PRAAx] ap2 boxF b N ≐ points N (fstT b) (sndT b) := by
  have h := toPR_eq (Γ := Γ) (points (var 1) (fstT (var 0)) (sndT (var 0)) : PTm 2) ![b,N]
  simpa only [boxF, ap2, subst_points, subst_fstT, subst_sndT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one] using h

def prefixCount (N B j : PTm n) : PTm n := Foundations.SequenceComposition.prefixSum boxF B N j
def boxes (N B : PTm n) : PTm n := Foundations.SequenceComposition.flatMap boxF B N

def boxesF : PR 2 := PTm.toPR (boxes (var 0) (var 1))

@[simp] theorem subst_prefixCount {l : ℕ} (σ : Fin n → PTm l) (N B j : PTm n) :
    Syn.subst σ (prefixCount N B j) = prefixCount (Syn.subst σ N) (Syn.subst σ B) (Syn.subst σ j) :=
  Foundations.SequenceComposition.subst_prefix _ _ _ _ _
@[simp] theorem subst_boxes {l : ℕ} (σ : Fin n → PTm l) (N B : PTm n) :
    Syn.subst σ (boxes N B) = boxes (Syn.subst σ N) (Syn.subst σ B) :=
  Foundations.SequenceComposition.subst_flatMap _ _ _ _

theorem boxes_at (N B : PTm n) : Γ ⊢[PRAAx] ap2 boxesF N B ≐ boxes N B := by
  have h := toPR_eq (Γ := Γ) (boxes (var 0) (var 1) : PTm 2) ![N,B]
  simpa only [boxesF, ap2, subst_boxes, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem prefixCount_zero (N B : PTm n) : Γ ⊢[PRAAx] prefixCount N B zero ≐ zero :=
  Foundations.SequenceComposition.prefix_zero _ _ _

/-- The actual cumulative count adds the next computed product of widths. -/
theorem prefixCount_succ (N B j : PTm n) :
    Γ ⊢[PRAAx] prefixCount N B (succ j) ≐
      prefixCount N B j+count N (fstT (entry B j)) (sndT (entry B j)) :=
  (Foundations.SequenceComposition.prefix_succ boxF B N j).eqTrans
    (congrAdd (.eqRefl _) ((congrFst (box_at N (entry B j))).eqTrans (points_length _ _ _)))

/-- Thus the true concatenated stored length is the sum of the box products. -/
theorem boxes_length (N B : PTm n) :
    Γ ⊢[PRAAx] length (boxes N B) ≐ prefixCount N B (length B) :=
  Foundations.SequenceComposition.flatMap_length _ _ _

/-- Lookup at an actual cumulative-count offset gives the actual random-access
mixed-radix point of that box. Empty outer lists are covered by the guard. -/
theorem boxes_lookup (N B j i : PTm n) (hj : Γ ⊢[PRAAx] lt j (length B))
    (hi : Γ ⊢[PRAAx] lt i (count N (fstT (entry B j)) (sndT (entry B j)))) :
    Γ ⊢[PRAAx] entry (boxes N B) (prefixCount N B j+i) ≐
      point N (fstT (entry B j)) (sndT (entry B j)) i := by
  have blockLength : Γ ⊢[PRAAx] length (Foundations.SequenceComposition.block boxF B N j) ≐
      count N (fstT (entry B j)) (sndT (entry B j)) :=
    (congrFst (box_at N (entry B j))).eqTrans (points_length _ _ _)
  have out := Foundations.SequenceComposition.flatMap_lookup boxF B N j i hj
    (lt_congr (.eqRefl _) blockLength.eqSymm hi)
  exact out.eqTrans ((entry_congr (box_at N (entry B j)) (.eqRefl _)).eqTrans
    (points_lookup _ _ _ _ hi))

/-- A point at a computed block offset has stored dimension N and lies in that
box, using only that box's genuine endpoint guards. -/
theorem boxes_inside (N B j i : PTm n) (hj : Γ ⊢[PRAAx] lt j (length B))
    (hi : Γ ⊢[PRAAx] lt i (count N (fstT (entry B j)) (sndT (entry B j))))
    (h : Γ ⊢[PRAAx] sides N (fstT (entry B j)) (sndT (entry B j))) :
    Γ ⊢[PRAAx] (length (entry (boxes N B) (prefixCount N B j+i)) ≐ N) ⋏
      inside N (fstT (entry B j)) (sndT (entry B j)) (entry (boxes N B) (prefixCount N B j+i)) :=
  .andI ((congrFst (boxes_lookup N B j i hj hi)).eqTrans (point_length _ _ _ _))
    (inside_congr _ _ _ _ _ (boxes_lookup N B j i hj hi).eqSymm (point_inside _ _ _ _ h))

theorem points_length_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (length (points (var 0) (var 1) (var 2)) ≐ count (var 0) (var 1) (var 2)) :=
  closeUniv 3 (points_length _ _ _)

theorem point_enumeration_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (sides (var 0) (var 1) (var 2) ⟶ lt (var 3) (count (var 0) (var 1) (var 2)) ⟶
        ((length (entry (points (var 0) (var 1) (var 2)) (var 3)) ≐ var 0) ⋏
          inside (var 0) (var 1) (var 2) (entry (points (var 0) (var 1) (var 2)) (var 3)))) :=
  closeUniv 4 (.impI (.impI (points_inside _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem points_distinct_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (sides (var 0) (var 1) (var 2) ⟶ lt (var 3) (count (var 0) (var 1) (var 2)) ⟶
        lt (var 4) (count (var 0) (var 1) (var 2)) ⟶ lt (var 3) (var 4) ⟶
          MinkowskiMesh.differentCoordinate (var 0)
            (entry (points (var 0) (var 1) (var 2)) (var 3))
            (entry (points (var 0) (var 1) (var 2)) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (points_distinct _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

theorem box_mesh_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (sides (var 0) (var 2) (var 3) ⟶ le one (var 1) ⟶
        le (succ (MinkowskiMesh.horizon (var 0) (var 1))) (count (var 0) (var 2) (var 3)) ⟶
          MinkowskiMesh.correct (var 0) (var 1) (points (var 0) (var 2) (var 3))
            (ap3 MinkowskiMesh.meshF (var 0) (var 1) (points (var 0) (var 2) (var 3)))) :=
  closeUniv 4 (.impI (.impI (.impI (box_mesh _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem boxes_count_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (length (boxes (var 0) (var 1)) ≐ prefixCount (var 0) (var 1) (length (var 1))) :=
  closeUniv 2 (boxes_length _ _)

theorem boxes_lookup_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (lt (var 2) (length (var 1)) ⟶
        lt (var 3) (count (var 0) (fstT (entry (var 1) (var 2))) (sndT (entry (var 1) (var 2)))) ⟶
          (entry (boxes (var 0) (var 1)) (prefixCount (var 0) (var 1) (var 2)+var 3) ≐
            point (var 0) (fstT (entry (var 1) (var 2))) (sndT (entry (var 1) (var 2))) (var 3))) :=
  closeUniv 4 (.impI (.impI (boxes_lookup _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiBoxes
