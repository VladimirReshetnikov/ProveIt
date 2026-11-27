import IPRADerivations.DiophantineNumberTheory.MinkowskiRationalScaling
import IPRADerivations.DiophantineNumberTheory.MinkowskiBoxUnion

/-!
# Actual common-denominator conversion of rational box endpoints

The original box record is a pair of rational endpoint-vector codes. Their
coordinate denominators are independently positive (predecessor storage).
The actual pool appends every lower vector to every upper vector. The
existing checked product/quotient normalizer computes its positive common
mesh and each integer endpoint, uniformly in box count and dimension.

The endpoint values and positive/separating comparisons are derived from
that actual pool and its actual quotient cofactors. In particular the width
clearing identity concerns the computed integer boxes and the original
rational endpoint difference, not a supplied integer-box correctness field.
Rational content folding, its volume/count threshold and geometric body
membership are distinct subsequent adapters.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiRationalBoxes

open_ipra exports
open LeanProofs.IPRA.Foundations.MasterCertificate
  (entry sequence sequence_length sequence_decode subst_entry subst_sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.Analysis.RationalSupMetric
  (numeratorOf denominatorOf rationalDenominator rationalNumerator normalizedVector normalizedCoordinateCode
    commonDenominator cofactor subst_numeratorOf subst_denominatorOf subst_normalizedVector
    subst_commonDenominator subst_cofactor)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE subst_rationalLE)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiRationalScaling
  (rationalLT gap scaledLeft scaledGap subst_rationalLT subst_gap)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def lowerRow (B j : PTm n) : PTm n := fstT (entry B j)
def upperRow (B j : PTm n) : PTm n := sndT (entry B j)
def lowerRowsBody : PTm 2 := lowerRow (var 1) (var 0)
def upperRowsBody : PTm 2 := upperRow (var 1) (var 0)
def lowerRows (B : PTm n) : PTm n := sequence lowerRowsBody (length B) B
def upperRows (B : PTm n) : PTm n := sequence upperRowsBody (length B) B
def pool (B : PTm n) : PTm n := Foundations.SequenceComposition.append (lowerRows B) (upperRows B)
def upperIndex (B j : PTm n) : PTm n := length B+j
def mesh (N B : PTm n) : PTm n := commonDenominator (pool B) N

@[simp] theorem subst_lowerRow {l : ℕ} (σ : Fin n → PTm l) (B j : PTm n) :
    Syn.subst σ (lowerRow B j) = lowerRow (Syn.subst σ B) (Syn.subst σ j) := by simp only [lowerRow, subst_fstT, subst_entry]
@[simp] theorem subst_upperRow {l : ℕ} (σ : Fin n → PTm l) (B j : PTm n) :
    Syn.subst σ (upperRow B j) = upperRow (Syn.subst σ B) (Syn.subst σ j) := by simp only [upperRow, subst_sndT, subst_entry]
@[simp] theorem subst_lowerRows {l : ℕ} (σ : Fin n → PTm l) (B : PTm n) :
    Syn.subst σ (lowerRows B) = lowerRows (Syn.subst σ B) := by simp only [lowerRows, subst_sequence, subst_length]
@[simp] theorem subst_upperRows {l : ℕ} (σ : Fin n → PTm l) (B : PTm n) :
    Syn.subst σ (upperRows B) = upperRows (Syn.subst σ B) := by simp only [upperRows, subst_sequence, subst_length]
@[simp] theorem subst_pool {l : ℕ} (σ : Fin n → PTm l) (B : PTm n) :
    Syn.subst σ (pool B) = pool (Syn.subst σ B) := by
  simp only [pool, Foundations.SequenceComposition.subst_append, subst_lowerRows, subst_upperRows]
@[simp] theorem subst_upperIndex {l : ℕ} (σ : Fin n → PTm l) (B j : PTm n) :
    Syn.subst σ (upperIndex B j) = upperIndex (Syn.subst σ B) (Syn.subst σ j) := by simp only [upperIndex, PTm.subst_add, subst_length]
@[simp] theorem subst_mesh {l : ℕ} (σ : Fin n → PTm l) (N B : PTm n) :
    Syn.subst σ (mesh N B) = mesh (Syn.subst σ N) (Syn.subst σ B) := by simp only [mesh, subst_commonDenominator, subst_pool]

theorem lowerRows_length (B : PTm n) : Γ ⊢[PRAAx] length (lowerRows B) ≐ length B := sequence_length _ _ _
theorem upperRows_length (B : PTm n) : Γ ⊢[PRAAx] length (upperRows B) ≐ length B := sequence_length _ _ _
theorem pool_length (B : PTm n) : Γ ⊢[PRAAx] length (pool B) ≐ length B+length B :=
  (Foundations.SequenceComposition.append_length _ _).eqTrans (congrAdd (lowerRows_length B) (upperRows_length B))

theorem lower_row_bound (B j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length B)) :
    Γ ⊢[PRAAx] lt j (length (pool B)) :=
  lt_congr (.eqRefl _) (pool_length B).eqSymm (lt_of_lt_of_le hj (le_add_right _ _))
theorem upper_row_bound (B j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length B)) :
    Γ ⊢[PRAAx] lt (upperIndex B j) (length (pool B)) :=
  lt_congr (.eqRefl _) (pool_length B).eqSymm (Foundations.SequenceComposition.add_lt_left _ hj)

theorem pool_lower (B j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length B)) :
    Γ ⊢[PRAAx] entry (pool B) j ≐ lowerRow B j := by
  have first := Foundations.SequenceComposition.append_left (b := upperRows B)
    (lt_congr (.eqRefl _) (lowerRows_length B).eqSymm hj)
  have row : Γ ⊢[PRAAx] entry (lowerRows B) j ≐ lowerRow B j := by
    simpa only [lowerRows, lowerRowsBody, inst2, subst_lowerRow, Syn.subst_var,
      Matrix.cons_val_zero, Matrix.cons_val_one] using sequence_decode (Γ := Γ) lowerRowsBody (x := B) hj
  exact first.eqTrans row

theorem pool_upper (B j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length B)) :
    Γ ⊢[PRAAx] entry (pool B) (upperIndex B j) ≐ upperRow B j := by
  have first := Foundations.SequenceComposition.append_right (a := lowerRows B)
    (lt_congr (.eqRefl _) (upperRows_length B).eqSymm hj)
  have row : Γ ⊢[PRAAx] entry (upperRows B) j ≐ upperRow B j := by
    simpa only [upperRows, upperRowsBody, inst2, subst_upperRow, Syn.subst_var,
      Matrix.cons_val_zero, Matrix.cons_val_one] using sequence_decode (Γ := Γ) upperRowsBody (x := B) hj
  exact (entry_congr (.eqRefl _) (congrAdd (lowerRows_length B).eqSymm (.eqRefl j))).eqTrans (first.eqTrans row)

theorem mesh_positive (N B : PTm n) : Γ ⊢[PRAAx] le one (mesh N B) :=
  Analysis.RationalSupMetric.commonDenominator_one_le _ _

/-- This actual PR conversion returns signed integer endpoint vectors. -/
def integerBox (N B j : PTm n) : PTm n :=
  pairT (normalizedVector (pool B) N j) (normalizedVector (pool B) N (upperIndex B j))
def integerBoxF : PR 3 := PTm.toPR (integerBox (var 0) (var 1) (var 2))
def integerBoxesBody : PTm 2 := ap3 integerBoxF (fstT (var 1)) (sndT (var 1)) (var 0)
def integerBoxes (N B : PTm n) : PTm n := sequence integerBoxesBody (length B) (pairT N B)
def integerBoxesF : PR 2 := PTm.toPR (integerBoxes (var 0) (var 1))
def meshF : PR 2 := PTm.toPR (mesh (var 0) (var 1))

@[simp] theorem subst_integerBox {l : ℕ} (σ : Fin n → PTm l) (N B j : PTm n) :
    Syn.subst σ (integerBox N B j) = integerBox (Syn.subst σ N) (Syn.subst σ B) (Syn.subst σ j) := by
  simp only [integerBox, subst_pairT, subst_normalizedVector, subst_pool, subst_upperIndex]
@[simp] theorem subst_integerBoxes {l : ℕ} (σ : Fin n → PTm l) (N B : PTm n) :
    Syn.subst σ (integerBoxes N B) = integerBoxes (Syn.subst σ N) (Syn.subst σ B) := by
  simp only [integerBoxes, subst_sequence, subst_length, subst_pairT]

theorem integerBox_at (N B j : PTm n) : Γ ⊢[PRAAx] ap3 integerBoxF N B j ≐ integerBox N B j := by
  have h := toPR_eq (Γ := Γ) (integerBox (var 0) (var 1) (var 2) : PTm 3) ![N,B,j]
  simpa only [integerBoxF, ap3, subst_integerBox, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h

theorem integerBoxes_at (N B : PTm n) : Γ ⊢[PRAAx] ap2 integerBoxesF N B ≐ integerBoxes N B := by
  have h := toPR_eq (Γ := Γ) (integerBoxes (var 0) (var 1) : PTm 2) ![N,B]
  simpa only [integerBoxesF, ap2, subst_integerBoxes, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem mesh_at (N B : PTm n) : Γ ⊢[PRAAx] ap2 meshF N B ≐ mesh N B := by
  have h := toPR_eq (Γ := Γ) (mesh (var 0) (var 1) : PTm 2) ![N,B]
  simpa only [meshF, ap2, subst_mesh, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem integerBoxes_length (N B : PTm n) : Γ ⊢[PRAAx] length (integerBoxes N B) ≐ length B := sequence_length _ _ _

theorem integerBoxes_lookup (N B j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length B)) :
    Γ ⊢[PRAAx] entry (integerBoxes N B) j ≐ integerBox N B j := by
  have h := sequence_decode (Γ := Γ) integerBoxesBody (x := pairT N B) hj
  have body : Γ ⊢[PRAAx] inst2 integerBoxesBody j (pairT N B) ≐ ap3 integerBoxF N B j := by
    simp only [integerBoxesBody, inst2, subst_ap3, subst_fstT, subst_sndT, Syn.subst_var,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    exact congrAp3 integerBoxF (fst_pair _ _) (snd_pair _ _) (.eqRefl _)
  exact h.eqTrans (body.eqTrans (integerBox_at N B j))

theorem integer_lower (N B j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length B)) :
    Γ ⊢[PRAAx] fstT (entry (integerBoxes N B) j) ≐ normalizedVector (pool B) N j :=
  (congrFst (integerBoxes_lookup N B j hj)).eqTrans (fst_pair _ _)
theorem integer_upper (N B j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length B)) :
    Γ ⊢[PRAAx] sndT (entry (integerBoxes N B) j) ≐ normalizedVector (pool B) N (upperIndex B j) :=
  (congrSnd (integerBoxes_lookup N B j hj)).eqTrans (snd_pair _ _)

/-- Actual coordinate fields and exact denominator/cofactor clearing at one
pool row. The original row equality is supplied by pool_lower/pool_upper. -/
theorem normalized_parts (N B r v k : PTm n) (hr : Γ ⊢[PRAAx] lt r (length (pool B)))
    (hk : Γ ⊢[PRAAx] lt k N) (hrow : Γ ⊢[PRAAx] entry (pool B) r ≐ v) :
    Γ ⊢[PRAAx] (fstT (entry (normalizedVector (pool B) N r) k) ≐ (numeratorOf (entry v k)).pos*cofactor (pool B) N r k) ⋏
      ((sndT (entry (normalizedVector (pool B) N r) k) ≐ (numeratorOf (entry v k)).neg*cofactor (pool B) N r k) ⋏
        (denominatorOf (entry v k)*cofactor (pool B) N r k ≐ mesh N B)) := by
  have e := Analysis.RationalSupMetric.normalizedVector_lookup (pool B) N r k hk
  have coord := entry_congr hrow (.eqRefl k)
  have p := ((congrFst e).eqTrans (fst_pair _ _)).eqTrans
    (congrMul (congrFst (congrFst coord)) (.eqRefl _))
  have q := ((congrSnd e).eqTrans (snd_pair _ _)).eqTrans
    (congrMul (congrSnd (congrFst coord)) (.eqRefl _))
  have den := congrSucc (congrSnd coord)
  have clear := (congrMul den.eqSymm (.eqRefl _)).eqTrans
    (Analysis.RationalSupMetric.cofactor_clears (pool B) N r k hr hk)
  exact .andI p (.andI q clear)

theorem endpoint_strict (N B r s v w k : PTm n)
    (hr : Γ ⊢[PRAAx] lt r (length (pool B))) (hs : Γ ⊢[PRAAx] lt s (length (pool B))) (hk : Γ ⊢[PRAAx] lt k N)
    (hv : Γ ⊢[PRAAx] entry (pool B) r ≐ v) (hw : Γ ⊢[PRAAx] entry (pool B) s ≐ w)
    (h : Γ ⊢[PRAAx] rationalLT (entry v k) (entry w k)) :
    Γ ⊢[PRAAx] lt
      (fstT (entry (normalizedVector (pool B) N r) k)+sndT (entry (normalizedVector (pool B) N s) k))
      (fstT (entry (normalizedVector (pool B) N s) k)+sndT (entry (normalizedVector (pool B) N r) k)) := by
  have a := normalized_parts N B r v k hr hk hv
  have b := normalized_parts N B s w k hs hk hw
  exact lt_congr (congrAdd (Prf.andE₁ a).eqSymm (Prf.andE₁ (Prf.andE₂ b)).eqSymm)
    (congrAdd (Prf.andE₁ b).eqSymm (Prf.andE₁ (Prf.andE₂ a)).eqSymm)
    (MinkowskiRationalScaling.strict_clear _ _ _ _ _ (mesh_positive N B)
      (Prf.andE₂ (Prf.andE₂ a)) (Prf.andE₂ (Prf.andE₂ b)) h)

theorem endpoint_weak (N B r s v w k : PTm n)
    (hr : Γ ⊢[PRAAx] lt r (length (pool B))) (hs : Γ ⊢[PRAAx] lt s (length (pool B))) (hk : Γ ⊢[PRAAx] lt k N)
    (hv : Γ ⊢[PRAAx] entry (pool B) r ≐ v) (hw : Γ ⊢[PRAAx] entry (pool B) s ≐ w)
    (h : Γ ⊢[PRAAx] rationalLE (entry v k) (entry w k)) :
    Γ ⊢[PRAAx] le
      (fstT (entry (normalizedVector (pool B) N r) k)+sndT (entry (normalizedVector (pool B) N s) k))
      (fstT (entry (normalizedVector (pool B) N s) k)+sndT (entry (normalizedVector (pool B) N r) k)) := by
  have a := normalized_parts N B r v k hr hk hv
  have b := normalized_parts N B s w k hs hk hw
  exact le_congr (congrAdd (Prf.andE₁ a).eqSymm (Prf.andE₁ (Prf.andE₂ b)).eqSymm)
    (congrAdd (Prf.andE₁ b).eqSymm (Prf.andE₁ (Prf.andE₂ a)).eqSymm)
    (MinkowskiRationalScaling.weak_clear _ _ _ _ _ (mesh_positive N B)
      (Prf.andE₂ (Prf.andE₂ a)) (Prf.andE₂ (Prf.andE₂ b)) h)


/-- Original rational width, as a computed positive cross numerator over its
computed product denominator. Neither depends on any mesh construction. -/
def widthNumerator (B j k : PTm n) : PTm n := gap (entry (lowerRow B j) k) (entry (upperRow B j) k)
def widthDenominator (B j k : PTm n) : PTm n := denominatorOf (entry (lowerRow B j) k)*denominatorOf (entry (upperRow B j) k)
def rationalSide (B j k : PTm n) : Fm PTm n := rationalLT (entry (lowerRow B j) k) (entry (upperRow B j) k)
def rationalSides (N B : PTm n) : Fm PTm n :=
  .all (lt (var 0) (length (Syn.shift B)) ⟶ .all (lt (var 0) (Syn.shift (Syn.shift N)) ⟶
    rationalSide (Syn.shift (Syn.shift B)) (var 1) (var 0)))

@[simp] theorem subst_widthNumerator {l : ℕ} (σ : Fin n → PTm l) (B j k : PTm n) :
    Syn.subst σ (widthNumerator B j k) = widthNumerator (Syn.subst σ B) (Syn.subst σ j) (Syn.subst σ k) := by
  simp only [widthNumerator, subst_gap, subst_entry, subst_lowerRow, subst_upperRow]
@[simp] theorem subst_widthDenominator {l : ℕ} (σ : Fin n → PTm l) (B j k : PTm n) :
    Syn.subst σ (widthDenominator B j k) = widthDenominator (Syn.subst σ B) (Syn.subst σ j) (Syn.subst σ k) := by
  simp only [widthDenominator, PTm.subst_mul, subst_denominatorOf, subst_entry, subst_lowerRow, subst_upperRow]
@[simp] theorem subst_rationalSide {l : ℕ} (σ : Fin n → PTm l) (B j k : PTm n) :
    (rationalSide B j k).subst σ = rationalSide (Syn.subst σ B) (Syn.subst σ j) (Syn.subst σ k) := by
  simp only [rationalSide, subst_rationalLT, subst_entry, subst_lowerRow, subst_upperRow]
@[simp] theorem subst_rationalSides {l : ℕ} (σ : Fin n → PTm l) (N B : PTm n) :
    (rationalSides N B).subst σ = rationalSides (Syn.subst σ N) (Syn.subst σ B) := by
  simp only [rationalSides, Fm.subst_all, Fm.subst_imp, subst_lt, subst_length, subst_rationalSide,
    Syn.subst_var, Syn.up_zero, Syn.up_one, Syn.up_succ, Syn.subst_shift, Syn.shift_subst,
    Syn.shift_var, Fin.succ_zero_eq_one]

theorem rationalSides_at (N B j k : PTm n) (h : Γ ⊢[PRAAx] rationalSides N B)
    (hj : Γ ⊢[PRAAx] lt j (length B)) (hk : Γ ⊢[PRAAx] lt k N) : Γ ⊢[PRAAx] rationalSide B j k := by
  have first : Γ ⊢[PRAAx] lt j (length B) ⟶ .all (lt (var 0) (Syn.shift N) ⟶
      rationalSide (Syn.shift B) (Syn.shift j) (var 0)) := by
    simpa only [rationalSides, Fm.subst_all, Fm.subst_imp, subst_lt, subst_length, subst_rationalSide,
      Syn.subst_var, Syn.inst_zero, Syn.up_zero, Syn.up_one, Syn.up_succ, Syn.subst_inst_shift,
      LeanProofs.IPRA.AnalyticNumberTheory.Fermat.subst_up_shift'] using Prf.allE j h
  have last : Γ ⊢[PRAAx] lt k N ⟶ rationalSide B j k := by
    simpa only [Fm.subst_imp, subst_lt, subst_rationalSide, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using
      Prf.allE k (Prf.impE first hj)
  exact .impE last hk

theorem widthNumerator_positive (B j k : PTm n) (h : Γ ⊢[PRAAx] rationalSide B j k) :
    Γ ⊢[PRAAx] le one (widthNumerator B j k) := by
  have e := eq_add_of_le (le_of_lt h)
  exact le_of_add_le_add_right (le_congr (by ipra_ring) (e.eqTrans (add_comm _ _)) h)

theorem widthDenominator_positive (B j k : PTm n) : Γ ⊢[PRAAx] le one (widthDenominator B j k) :=
  le_congr (one_mul one) (.eqRefl _)
    (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono
      (Analysis.RationalArgmin.denominator_positive _) (Analysis.RationalArgmin.denominator_positive _))

/-- The actual integer-box side is derived from the original rational side. -/
theorem integer_side (N B j k : PTm n) (hj : Γ ⊢[PRAAx] lt j (length B)) (hk : Γ ⊢[PRAAx] lt k N)
    (h : Γ ⊢[PRAAx] rationalSide B j k) :
    Γ ⊢[PRAAx] MinkowskiBoxes.side (fstT (entry (integerBoxes N B) j)) (sndT (entry (integerBoxes N B) j)) k := by
  have low := entry_congr (integer_lower N B j hj) (.eqRefl k)
  have up := entry_congr (integer_upper N B j hj) (.eqRefl k)
  have original := endpoint_strict N B j (upperIndex B j) (lowerRow B j) (upperRow B j) k
    (lower_row_bound B j hj) (upper_row_bound B j hj) hk (pool_lower B j hj) (pool_upper B j hj) h
  exact lt_congr (congrAdd (congrFst low).eqSymm (congrSnd up).eqSymm)
    (congrAdd (congrFst up).eqSymm (congrSnd low).eqSymm) original

/-- Exact source cell-width clearing for the actual converted box. -/
theorem integer_width_clears (N B j k : PTm n)
    (hj : Γ ⊢[PRAAx] lt j (length B)) (hk : Γ ⊢[PRAAx] lt k N)
    (h : Γ ⊢[PRAAx] rationalSide B j k) :
    Γ ⊢[PRAAx] widthDenominator B j k*
      MinkowskiBoxes.width (fstT (entry (integerBoxes N B) j)) (sndT (entry (integerBoxes N B) j)) k ≐
        mesh N B*widthNumerator B j k := by
  have a := normalized_parts N B j (lowerRow B j) k (lower_row_bound B j hj) hk (pool_lower B j hj)
  have b := normalized_parts N B (upperIndex B j) (upperRow B j) k (upper_row_bound B j hj) hk (pool_upper B j hj)
  have low := entry_congr (integer_lower N B j hj) (.eqRefl k)
  have up := entry_congr (integer_upper N B j hj) (.eqRefl k)
  have pl := (congrFst low).eqTrans (Prf.andE₁ a)
  have nl := (congrSnd low).eqTrans (Prf.andE₁ (Prf.andE₂ a))
  have pu := (congrFst up).eqTrans (Prf.andE₁ b)
  have nu := (congrSnd up).eqTrans (Prf.andE₁ (Prf.andE₂ b))
  have gapEq := congrMonus (congrAdd pu nl) (congrAdd pl nu)
  exact (congrMul (.eqRefl _) gapEq).eqTrans
    (MinkowskiRationalScaling.width_clears _ _ _ _ _ (mesh_positive N B)
      (Prf.andE₂ (Prf.andE₂ a)) (Prf.andE₂ (Prf.andE₂ b)) h)

theorem integer_sides_at (N B j : PTm n) (h : Γ ⊢[PRAAx] rationalSides N B)
    (hj : Γ ⊢[PRAAx] lt j (length B)) :
    Γ ⊢[PRAAx] MinkowskiBoxes.sides N (fstT (entry (integerBoxes N B) j)) (sndT (entry (integerBoxes N B) j)) := by
  refine .allI (.impI ?_)
  have guards : Γ.map Fm.shift ⊢[PRAAx] rationalSides (Syn.shift N) (Syn.shift B) := by
    simpa only [Fm.shift, subst_rationalSides, Syn.shift] using h.shift
  have bound : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (length (Syn.shift B)) := by
    simpa only [Fm.shift, subst_lt, subst_length, Syn.shift] using hj.shift
  have out := integer_side (Syn.shift N) (Syn.shift B) (Syn.shift j) (var 0) bound.wk
    (Prf.hyp0 : lt (var 0) (Syn.shift N) :: Γ.map Fm.shift ⊢[PRAAx] _)
    (rationalSides_at _ _ _ _ guards.wk bound.wk Prf.hyp0)
  simpa only [Syn.shift, subst_fstT, subst_sndT, subst_entry, subst_integerBoxes] using out

theorem integer_allSides (N B : PTm n) (h : Γ ⊢[PRAAx] rationalSides N B) :
    Γ ⊢[PRAAx] MinkowskiBoxUnion.allSides N (integerBoxes N B) := by
  refine .allI (.impI ?_)
  have guards : Γ.map Fm.shift ⊢[PRAAx] rationalSides (Syn.shift N) (Syn.shift B) := by
    simpa only [Fm.shift, subst_rationalSides, Syn.shift] using h.shift
  have bound : lt (var 0) (length (Syn.shift (integerBoxes N B))) :: Γ.map Fm.shift ⊢[PRAAx]
      lt (var 0) (length (Syn.shift B)) :=
    lt_congr (.eqRefl _) (integerBoxes_length (Syn.shift N) (Syn.shift B))
      (by simpa only [Syn.shift, subst_integerBoxes] using (Prf.hyp0 : lt (var 0) (length (Syn.shift (integerBoxes N B))) :: Γ.map Fm.shift ⊢[PRAAx] _))
  simpa only [Syn.shift, subst_integerBoxes] using integer_sides_at (Syn.shift N) (Syn.shift B) (var 0) guards.wk bound


/-- The original rational endpoint form of source eq:box-disjoint. -/
def rationalSeparationAt (B i j k : PTm n) : Fm PTm n :=
  rationalLE (entry (upperRow B i) k) (entry (lowerRow B j) k) ⋎
    rationalLE (entry (upperRow B j) k) (entry (lowerRow B i) k)
def rationalSeparated (N B i j : PTm n) : Fm PTm n :=
  .ex (lt (var 0) (Syn.shift N) ⋏ rationalSeparationAt (Syn.shift B) (Syn.shift i) (Syn.shift j) (var 0))
def rationalDisjoint (N B : PTm n) : Fm PTm n :=
  .all (lt (var 0) (length (Syn.shift B)) ⟶ .all (lt (var 0) (var 1) ⟶
    rationalSeparated (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift B)) (var 0) (var 1)))

@[simp] theorem subst_rationalSeparationAt {l : ℕ} (σ : Fin n → PTm l) (B i j k : PTm n) :
    (rationalSeparationAt B i j k).subst σ = rationalSeparationAt (Syn.subst σ B) (Syn.subst σ i) (Syn.subst σ j) (Syn.subst σ k) := by
  simp only [rationalSeparationAt, Fm.subst_or, subst_rationalLE, subst_entry, subst_lowerRow, subst_upperRow]
@[simp] theorem subst_rationalSeparated {l : ℕ} (σ : Fin n → PTm l) (N B i j : PTm n) :
    (rationalSeparated N B i j).subst σ = rationalSeparated (Syn.subst σ N) (Syn.subst σ B) (Syn.subst σ i) (Syn.subst σ j) := by
  simp only [rationalSeparated, Fm.subst_ex, Fm.subst_and, subst_lt, subst_rationalSeparationAt,
    Syn.subst_var, Syn.up_zero, Syn.up_succ, Syn.subst_shift, Syn.shift_subst]
@[simp] theorem subst_rationalDisjoint {l : ℕ} (σ : Fin n → PTm l) (N B : PTm n) :
    (rationalDisjoint N B).subst σ = rationalDisjoint (Syn.subst σ N) (Syn.subst σ B) := by
  simp only [rationalDisjoint, Fm.subst_all, Fm.subst_imp, subst_lt, subst_length, subst_rationalSeparated,
    Syn.subst_var, Syn.up_zero, Syn.up_one, Syn.up_succ, Syn.subst_shift, Syn.shift_subst,
    Syn.shift_var, Fin.succ_zero_eq_one]

theorem rationalDisjoint_at (N B i j : PTm n) (h : Γ ⊢[PRAAx] rationalDisjoint N B)
    (hj : Γ ⊢[PRAAx] lt j (length B)) (hij : Γ ⊢[PRAAx] lt i j) :
    Γ ⊢[PRAAx] rationalSeparated N B i j := by
  have first : Γ ⊢[PRAAx] lt j (length B) ⟶ .all (lt (var 0) (Syn.shift j) ⟶
      rationalSeparated (Syn.shift N) (Syn.shift B) (var 0) (Syn.shift j)) := by
    simpa only [rationalDisjoint, Fm.subst_all, Fm.subst_imp, subst_lt, subst_length, subst_rationalSeparated,
      Syn.subst_var, Syn.inst_zero, Syn.up_zero, Syn.up_one, Syn.up_succ, Syn.subst_inst_shift,
      LeanProofs.IPRA.AnalyticNumberTheory.Fermat.subst_up_shift'] using Prf.allE j h
  have last : Γ ⊢[PRAAx] lt i j ⟶ rationalSeparated N B i j := by
    simpa only [Fm.subst_imp, subst_lt, subst_rationalSeparated, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using
      Prf.allE i (Prf.impE first hj)
  exact .impE last hij

/-- A genuine rational separating axis remains a separating axis after the
actual common-denominator conversion, including touching endpoints. -/
theorem integer_separation_at (N B i j k : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length B)) (hj : Γ ⊢[PRAAx] lt j (length B)) (hk : Γ ⊢[PRAAx] lt k N)
    (h : Γ ⊢[PRAAx] rationalSeparationAt B i j k) :
    Γ ⊢[PRAAx] MinkowskiBoxUnion.separationAt
      (fstT (entry (integerBoxes N B) i)) (sndT (entry (integerBoxes N B) i))
      (fstT (entry (integerBoxes N B) j)) (sndT (entry (integerBoxes N B) j)) k := by
  have li := entry_congr (integer_lower N B i hi) (.eqRefl k)
  have ui := entry_congr (integer_upper N B i hi) (.eqRefl k)
  have lj := entry_congr (integer_lower N B j hj) (.eqRefl k)
  have uj := entry_congr (integer_upper N B j hj) (.eqRefl k)
  refine .orE h (.orI₁ ?_) (.orI₂ ?_)
  · have original := endpoint_weak N B (upperIndex B i) j (upperRow B i) (lowerRow B j) k
      (upper_row_bound B i hi.wk) (lower_row_bound B j hj.wk) hk.wk (pool_upper B i hi.wk) (pool_lower B j hj.wk) Prf.hyp0
    exact le_congr (congrAdd (congrFst ui.wk).eqSymm (congrSnd lj.wk).eqSymm)
      (congrAdd (congrFst lj.wk).eqSymm (congrSnd ui.wk).eqSymm) original
  · have original := endpoint_weak N B (upperIndex B j) i (upperRow B j) (lowerRow B i) k
      (upper_row_bound B j hj.wk) (lower_row_bound B i hi.wk) hk.wk (pool_upper B j hj.wk) (pool_lower B i hi.wk) Prf.hyp0
    exact le_congr (congrAdd (congrFst uj.wk).eqSymm (congrSnd li.wk).eqSymm)
      (congrAdd (congrFst li.wk).eqSymm (congrSnd uj.wk).eqSymm) original

theorem integer_separated (N B i j : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length B)) (hj : Γ ⊢[PRAAx] lt j (length B))
    (h : Γ ⊢[PRAAx] rationalSeparated N B i j) :
    Γ ⊢[PRAAx] MinkowskiBoxUnion.separated N
      (fstT (entry (integerBoxes N B) i)) (sndT (entry (integerBoxes N B) i))
      (fstT (entry (integerBoxes N B) j)) (sndT (entry (integerBoxes N B) j)) := by
  refine .exE h ?_
  let E : Fm PTm (n+1) := lt (var 0) (Syn.shift N) ⋏
    rationalSeparationAt (Syn.shift B) (Syn.shift i) (Syn.shift j) (var 0)
  have ibound : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift i) (length (Syn.shift B)) := by
    simpa only [Fm.shift, subst_lt, subst_length, Syn.shift] using hi.shift
  have jbound : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (length (Syn.shift B)) := by
    simpa only [Fm.shift, subst_lt, subst_length, Syn.shift] using hj.shift
  have separated := integer_separation_at (Syn.shift N) (Syn.shift B) (Syn.shift i) (Syn.shift j) (var 0)
    ibound.wk jbound.wk (Prf.andE₁ (Prf.hyp0 : E :: Γ.map Fm.shift ⊢[PRAAx] E)) (Prf.andE₂ Prf.hyp0)
  have out : E :: Γ.map Fm.shift ⊢[PRAAx] MinkowskiBoxUnion.separated (Syn.shift N)
      (fstT (entry (integerBoxes (Syn.shift N) (Syn.shift B)) (Syn.shift i)))
      (sndT (entry (integerBoxes (Syn.shift N) (Syn.shift B)) (Syn.shift i)))
      (fstT (entry (integerBoxes (Syn.shift N) (Syn.shift B)) (Syn.shift j)))
      (sndT (entry (integerBoxes (Syn.shift N) (Syn.shift B)) (Syn.shift j))) := by
    refine .exI (var 0) ?_
    simpa only [MinkowskiBoxUnion.separated, Fm.subst_and, subst_lt, MinkowskiBoxUnion.subst_separationAt,
      Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using
      (Prf.andI (Prf.andE₁ (Prf.hyp0 : E :: Γ.map Fm.shift ⊢[PRAAx] E)) separated)
  simpa only [E, Fm.shift, MinkowskiBoxUnion.subst_separated, subst_fstT, subst_sndT,
    subst_entry, subst_integerBoxes, Syn.shift] using out

theorem integer_disjoint (N B : PTm n) (h : Γ ⊢[PRAAx] rationalDisjoint N B) :
    Γ ⊢[PRAAx] MinkowskiBoxUnion.disjoint N (integerBoxes N B) := by
  refine .allI (.impI (.allI (.impI ?_)))
  let Δ := lt (var 0) (var 1) ::
    lt (var 1) (length (integerBoxes (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift B)))) ::
      (Γ.map Fm.shift).map Fm.shift
  have guards : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      rationalDisjoint (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift B)) := by
    simpa only [Fm.shift, subst_rationalDisjoint, Syn.shift] using h.shift.shift
  have jbound : Δ ⊢[PRAAx] lt (var 1) (length (Syn.shift (Syn.shift B))) :=
    lt_congr (.eqRefl _) (integerBoxes_length _ _) Prf.hyp1
  have ibound := lt_of_lt_of_le (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (var 1)) (le_of_lt jbound)
  have original := rationalDisjoint_at _ _ _ _ guards.wk.wk jbound (Prf.hyp0 : Δ ⊢[PRAAx] _)
  have out := integer_separated _ _ _ _ ibound jbound original
  simpa only [List.map_cons, Fm.shift, subst_lt, subst_length, Syn.shift, Syn.subst_var,
    Fin.succ_zero_eq_one, subst_integerBoxes] using out

/-- The source rational endpoint guards produce the actual integer mesh input
guards. The volume/count inequality is not assumed or claimed here. -/
theorem conversion_guards_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (rationalSides (var 0) (var 1) ⟶ rationalDisjoint (var 0) (var 1) ⟶
        (le one (mesh (var 0) (var 1)) ⋏
          ((length (integerBoxes (var 0) (var 1)) ≐ length (var 1)) ⋏
            (MinkowskiBoxUnion.allSides (var 0) (integerBoxes (var 0) (var 1)) ⋏
              MinkowskiBoxUnion.disjoint (var 0) (integerBoxes (var 0) (var 1)))))) :=
  closeUniv 2 (.impI (.impI (.andI (mesh_positive _ _)
    (.andI (integerBoxes_length _ _) (.andI (integer_allSides _ _ Prf.hyp1) (integer_disjoint _ _ Prf.hyp0))))))

theorem integer_width_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (lt (var 2) (length (var 1)) ⟶ lt (var 3) (var 0) ⟶ rationalSide (var 1) (var 2) (var 3) ⟶
        (widthDenominator (var 1) (var 2) (var 3)*MinkowskiBoxes.width
          (fstT (entry (integerBoxes (var 0) (var 1)) (var 2)))
          (sndT (entry (integerBoxes (var 0) (var 1)) (var 2))) (var 3) ≐
            mesh (var 0) (var 1)*widthNumerator (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (integer_width_clears (var 0) (var 1) (var 2) (var 3)
    Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem endpoint_programs_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((ap2 meshF (var 0) (var 1) ≐ mesh (var 0) (var 1)) ⋏
        ((ap2 integerBoxesF (var 0) (var 1) ≐ integerBoxes (var 0) (var 1)) ⋏
          (ap3 integerBoxF (var 0) (var 1) (var 2) ≐ integerBox (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.andI (mesh_at _ _) (.andI (integerBoxes_at _ _) (integerBox_at _ _ _)))

end LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiRationalBoxes
