import IPRADerivations.DiophantineNumberTheory.MinkowskiRationalBoxes
import IPRADerivations.DiophantineNumberTheory.MinkowskiContentSum

/-!
# Original rational box content and the actual integer cell count

Each original rational side is computed as a natural cross-difference
numerator over the product of its independent endpoint denominators. Its
box content is the product of these numerators over the product of these
denominators, computed without reference to the integer mesh enumeration.
Quantifier-free prefix induction derives the exact per-box identity
`boxDenominator * integerCount = mesh^N * boxNumerator` from the actual
endpoint conversion. All dimensions, box lists, and indices are internal.
The sum-facing fixed bodies and actual concatenated-count linkage expose
the inputs needed for a separate rational-content accumulator theorem.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiRationalContent

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiRationalBoxes
  (integerBoxes mesh widthNumerator widthDenominator rationalSides subst_integerBoxes subst_mesh
    subst_widthNumerator subst_widthDenominator subst_rationalSides)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def numeratorBody : PTm 2 := widthNumerator (fstT (var 1)) (sndT (var 1)) (var 0)
def denominatorBody : PTm 2 := widthDenominator (fstT (var 1)) (sndT (var 1)) (var 0)
def boxNumerator (N B j : PTm n) : PTm n := ap2 (prodF numeratorBody) N (pairT B j)
def boxDenominator (N B j : PTm n) : PTm n := ap2 (prodF denominatorBody) N (pairT B j)
def integerCount (N B j : PTm n) : PTm n :=
  MinkowskiBoxes.count N (fstT (entry (integerBoxes N B) j)) (sndT (entry (integerBoxes N B) j))
def partialCount (N B j k : PTm n) : PTm n :=
  MinkowskiMixedRadix.count k (MinkowskiBoxes.widths N
    (fstT (entry (integerBoxes N B) j)) (sndT (entry (integerBoxes N B) j)))

@[simp] theorem subst_boxNumerator {l : ℕ} (σ : Fin n → PTm l) (N B j : PTm n) :
    Syn.subst σ (boxNumerator N B j) = boxNumerator (Syn.subst σ N) (Syn.subst σ B) (Syn.subst σ j) := by
  simp only [boxNumerator, subst_ap2, subst_pairT]
@[simp] theorem subst_boxDenominator {l : ℕ} (σ : Fin n → PTm l) (N B j : PTm n) :
    Syn.subst σ (boxDenominator N B j) = boxDenominator (Syn.subst σ N) (Syn.subst σ B) (Syn.subst σ j) := by
  simp only [boxDenominator, subst_ap2, subst_pairT]
@[simp] theorem subst_integerCount {l : ℕ} (σ : Fin n → PTm l) (N B j : PTm n) :
    Syn.subst σ (integerCount N B j) = integerCount (Syn.subst σ N) (Syn.subst σ B) (Syn.subst σ j) := by
  simp only [integerCount, MinkowskiBoxes.subst_count, subst_fstT, subst_sndT, subst_entry, subst_integerBoxes]
@[simp] theorem subst_partialCount {l : ℕ} (σ : Fin n → PTm l) (N B j k : PTm n) :
    Syn.subst σ (partialCount N B j k) = partialCount (Syn.subst σ N) (Syn.subst σ B) (Syn.subst σ j) (Syn.subst σ k) := by
  simp only [partialCount, MinkowskiMixedRadix.subst_count, MinkowskiBoxes.subst_widths,
    subst_fstT, subst_sndT, subst_entry, subst_integerBoxes]

theorem numeratorBody_at (B j k : PTm n) :
    Γ ⊢[PRAAx] inst2 numeratorBody k (pairT B j) ≐ widthNumerator B j k := by
  have h := Prf.eqCongr (Γ := Γ) (widthNumerator (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![fstT (pairT B j),sndT (pairT B j),k]) (σ' := ![B,j,k])
    (fun i => by fin_cases i; exact fst_pair _ _; exact snd_pair _ _; exact .eqRefl _)
  simpa only [numeratorBody, inst2, subst_widthNumerator, subst_fstT, subst_sndT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h

theorem denominatorBody_at (B j k : PTm n) :
    Γ ⊢[PRAAx] inst2 denominatorBody k (pairT B j) ≐ widthDenominator B j k := by
  have h := Prf.eqCongr (Γ := Γ) (widthDenominator (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![fstT (pairT B j),sndT (pairT B j),k]) (σ' := ![B,j,k])
    (fun i => by fin_cases i; exact fst_pair _ _; exact snd_pair _ _; exact .eqRefl _)
  simpa only [denominatorBody, inst2, subst_widthDenominator, subst_fstT, subst_sndT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h

theorem boxNumerator_zero (B j : PTm n) : Γ ⊢[PRAAx] boxNumerator zero B j ≐ one := prod_zero _ _
theorem boxDenominator_zero (B j : PTm n) : Γ ⊢[PRAAx] boxDenominator zero B j ≐ one := prod_zero _ _
theorem partialCount_zero (N B j : PTm n) : Γ ⊢[PRAAx] partialCount N B j zero ≐ one := MinkowskiMixedRadix.count_zero _

theorem boxNumerator_succ (k B j : PTm n) :
    Γ ⊢[PRAAx] boxNumerator (succ k) B j ≐ boxNumerator k B j*widthNumerator B j k :=
  (prod_succ numeratorBody k (pairT B j)).eqTrans (congrMul (.eqRefl _) (numeratorBody_at B j k))
theorem boxDenominator_succ (k B j : PTm n) :
    Γ ⊢[PRAAx] boxDenominator (succ k) B j ≐ boxDenominator k B j*widthDenominator B j k :=
  (prod_succ denominatorBody k (pairT B j)).eqTrans (congrMul (.eqRefl _) (denominatorBody_at B j k))

theorem partialCount_succ (N B j k : PTm n) (hk : Γ ⊢[PRAAx] lt k N) :
    Γ ⊢[PRAAx] partialCount N B j (succ k) ≐ partialCount N B j k*
      MinkowskiBoxes.width (fstT (entry (integerBoxes N B) j)) (sndT (entry (integerBoxes N B) j)) k :=
  (MinkowskiMixedRadix.count_succ k _).eqTrans (congrMul (.eqRefl _) (MinkowskiBoxes.widths_lookup _ _ _ _ hk))

/-- Positivity uses the original rational endpoint denominators only. -/
theorem box_denominator_positive (N B j : PTm n) : Γ ⊢[PRAAx] le one (boxDenominator N B j) := by
  have positive : Γ ⊢[PRAAx] boxDenominator N B j ≐ succ (PTm.pred (boxDenominator N B j)) := by
    apply prod_pos_bounded denominatorBody (pairT B j) N
    refine .allI (.impI ?_)
    have hp : Γ.map Fm.shift ⊢[PRAAx] le one (widthDenominator (Syn.shift B) (Syn.shift j) (var 0)) :=
      MinkowskiRationalBoxes.widthDenominator_positive _ _ _
    have ep : lt (var 0) (Syn.shift N) :: Γ.map Fm.shift ⊢[PRAAx]
        inst2 denominatorBody (var 0) (Syn.shift (pairT B j)) ≐ widthDenominator (Syn.shift B) (Syn.shift j) (var 0) := by
      simpa only [Syn.shift, subst_pairT] using denominatorBody_at (Syn.shift B) (Syn.shift j) (var 0)
    exact pos_of_eq_succ (ep.eqTrans (SignedEuclidean.positive_form _ hp.wk))
  exact le_congr (.eqRefl _) positive.eqSymm (zero_lt_succ _)

/-- The induction invariant contains only natural order and one equation of
actual PR products. No induction on a quantified box correctness predicate. -/
theorem box_content_clears (N B j : PTm n) (h : Γ ⊢[PRAAx] rationalSides N B)
    (hj : Γ ⊢[PRAAx] lt j (length B)) :
    Γ ⊢[PRAAx] boxDenominator N B j*integerCount N B j ≐ pw (mesh N B) N*boxNumerator N B j := by
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift N) ⟶
      (boxDenominator (var 0) (Syn.shift B) (Syn.shift j)*
        partialCount (Syn.shift N) (Syn.shift B) (Syn.shift j) (var 0) ≐
          pw (mesh (Syn.shift N) (Syn.shift B)) (var 0)*boxNumerator (var 0) (Syn.shift B) (Syn.shift j))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, PTm.subst_mul, subst_boxDenominator,
        subst_partialCount, subst_boxNumerator, subst_ap2, subst_mesh, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      exact .impI ((congrMul (boxDenominator_zero _ _) (partialCount_zero _ _ _)).eqTrans
        (congrMul (pw_zero _) (boxNumerator_zero _ _)).eqSymm)
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, PTm.subst_mul, subst_boxDenominator,
        subst_partialCount, subst_boxNumerator, subst_ap2, subst_mesh, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_succ]
      refine .impI ?_
      let I : Fm PTm (n+1) := le (var 0) (Syn.shift N) ⟶
        (boxDenominator (var 0) (Syn.shift B) (Syn.shift j)*partialCount (Syn.shift N) (Syn.shift B) (Syn.shift j) (var 0) ≐
          pw (mesh (Syn.shift N) (Syn.shift B)) (var 0)*boxNumerator (var 0) (Syn.shift B) (Syn.shift j))
      let Δ := le (succ (var 0)) (Syn.shift N) :: I :: Γ.map Fm.shift
      have guards : Γ.map Fm.shift ⊢[PRAAx] rationalSides (Syn.shift N) (Syn.shift B) := by
        simpa only [Fm.shift, subst_rationalSides, Syn.shift] using h.shift
      have bound : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (length (Syn.shift B)) := by
        simpa only [Fm.shift, subst_lt, subst_length, Syn.shift] using hj.shift
      have hk : Δ ⊢[PRAAx] lt (var 0) (Syn.shift N) := Prf.hyp0
      have ih : Δ ⊢[PRAAx] boxDenominator (var 0) (Syn.shift B) (Syn.shift j)*
          partialCount (Syn.shift N) (Syn.shift B) (Syn.shift j) (var 0) ≐
            pw (mesh (Syn.shift N) (Syn.shift B)) (var 0)*boxNumerator (var 0) (Syn.shift B) (Syn.shift j) :=
        .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      have width := MinkowskiRationalBoxes.integer_width_clears (Syn.shift N) (Syn.shift B) (Syn.shift j) (var 0)
        bound.wk.wk hk (MinkowskiRationalBoxes.rationalSides_at _ _ _ _ guards.wk.wk bound.wk.wk hk)
      refine (congrMul (boxDenominator_succ _ _ _) (partialCount_succ _ _ _ _ hk)).eqTrans ?_
      refine .eqTrans (show Δ ⊢[PRAAx]
        (boxDenominator (var 0) (Syn.shift B) (Syn.shift j)*widthDenominator (Syn.shift B) (Syn.shift j) (var 0))*
          (partialCount (Syn.shift N) (Syn.shift B) (Syn.shift j) (var 0)*
            MinkowskiBoxes.width (fstT (entry (integerBoxes (Syn.shift N) (Syn.shift B)) (Syn.shift j)))
              (sndT (entry (integerBoxes (Syn.shift N) (Syn.shift B)) (Syn.shift j))) (var 0)) ≐
        (boxDenominator (var 0) (Syn.shift B) (Syn.shift j)*partialCount (Syn.shift N) (Syn.shift B) (Syn.shift j) (var 0))*
          (widthDenominator (Syn.shift B) (Syn.shift j) (var 0)*
            MinkowskiBoxes.width (fstT (entry (integerBoxes (Syn.shift N) (Syn.shift B)) (Syn.shift j)))
              (sndT (entry (integerBoxes (Syn.shift N) (Syn.shift B)) (Syn.shift j))) (var 0)) from by ipra_ring) ?_
      refine (congrMul ih width).eqTrans ?_
      refine .eqTrans (show Δ ⊢[PRAAx]
        (pw (mesh (Syn.shift N) (Syn.shift B)) (var 0)*boxNumerator (var 0) (Syn.shift B) (Syn.shift j))*
          (mesh (Syn.shift N) (Syn.shift B)*widthNumerator (Syn.shift B) (Syn.shift j) (var 0)) ≐
        (pw (mesh (Syn.shift N) (Syn.shift B)) (var 0)*mesh (Syn.shift N) (Syn.shift B))*
          (boxNumerator (var 0) (Syn.shift B) (Syn.shift j)*widthNumerator (Syn.shift B) (Syn.shift j) (var 0)) from by ipra_ring) ?_
      exact congrMul (pw_succ _ _).eqSymm (boxNumerator_succ _ _ _).eqSymm
  have final := Prf.allE N all
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, PTm.subst_mul, subst_boxDenominator,
    subst_partialCount, subst_boxNumerator, subst_ap2, subst_mesh, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift] at final
  exact .impE final (le_refl N)

/-- Count body is compiled as a fixed PR symbol so its pair-parameter identity
does not unfold the whole endpoint-conversion program. -/
def integerCountF : PR 3 := PTm.toPR (integerCount (var 0) (var 1) (var 2))

theorem integerCount_at (N B j : PTm n) : Γ ⊢[PRAAx] ap3 integerCountF N B j ≐ integerCount N B j := by
  have h := toPR_eq (Γ := Γ) (integerCount (var 0) (var 1) (var 2) : PTm 3) ![N,B,j]
  simpa only [integerCountF, ap3, subst_integerCount, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h


/-- Fixed sum-facing bodies: index j, persistent data pair(N,B). -/
def numeratorAt : PTm 2 := boxNumerator (fstT (var 1)) (sndT (var 1)) (var 0)
def denominatorAt : PTm 2 := boxDenominator (fstT (var 1)) (sndT (var 1)) (var 0)
def countAt : PTm 2 := ap3 integerCountF (fstT (var 1)) (sndT (var 1)) (var 0)

theorem numeratorAt_at (N B j : PTm n) : Γ ⊢[PRAAx] inst2 numeratorAt j (pairT N B) ≐ boxNumerator N B j := by
  simp only [numeratorAt, inst2, subst_boxNumerator, subst_fstT, subst_sndT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  exact congrAp2 (prodF numeratorBody) (fst_pair _ _) (congrPairT (snd_pair _ _) (.eqRefl j))

theorem denominatorAt_at (N B j : PTm n) : Γ ⊢[PRAAx] inst2 denominatorAt j (pairT N B) ≐ boxDenominator N B j := by
  simp only [denominatorAt, inst2, subst_boxDenominator, subst_fstT, subst_sndT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  exact congrAp2 (prodF denominatorBody) (fst_pair _ _) (congrPairT (snd_pair _ _) (.eqRefl j))



theorem countAt_at (N B j : PTm n) : Γ ⊢[PRAAx] inst2 countAt j (pairT N B) ≐ integerCount N B j := by
  simp only [countAt, inst2, subst_ap3, subst_fstT, subst_sndT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  exact (congrAp3 integerCountF (fst_pair _ _) (snd_pair _ _) (.eqRefl _)).eqTrans (integerCount_at N B j)

def integerCountSum (N B r : PTm n) : PTm n := ap2 (sumF countAt) r (pairT N B)
@[simp] theorem subst_integerCountSum {l : ℕ} (σ : Fin n → PTm l) (N B r : PTm n) :
    Syn.subst σ (integerCountSum N B r) = integerCountSum (Syn.subst σ N) (Syn.subst σ B) (Syn.subst σ r) := by
  simp only [integerCountSum, subst_ap2, subst_pairT]

theorem integerCountSum_zero (N B : PTm n) : Γ ⊢[PRAAx] integerCountSum N B zero ≐ zero := sum_zero _ _
theorem integerCountSum_succ (N B r : PTm n) :
    Γ ⊢[PRAAx] integerCountSum N B (succ r) ≐ integerCountSum N B r+integerCount N B r :=
  (sum_succ' countAt r (pairT N B)).eqTrans (congrAdd (.eqRefl _) (countAt_at N B r))

theorem prefix_integer_count_sum (N B r : PTm n) :
    Γ ⊢[PRAAx] MinkowskiBoxes.prefixCount N (integerBoxes N B) r ≐ integerCountSum N B r := by
  have all : Γ ⊢[PRAAx] .all
      (MinkowskiBoxes.prefixCount (Syn.shift N) (integerBoxes (Syn.shift N) (Syn.shift B)) (var 0) ≐
        integerCountSum (Syn.shift N) (Syn.shift B) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, MinkowskiBoxes.subst_prefixCount, subst_integerBoxes,
        subst_integerCountSum, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact (MinkowskiBoxes.prefixCount_zero _ _).eqTrans (integerCountSum_zero N B).eqSymm
    · simp only [Fm.subst_eq, MinkowskiBoxes.subst_prefixCount, subst_integerBoxes,
        subst_integerCountSum, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      exact (MinkowskiBoxes.prefixCount_succ _ _ _).eqTrans
        ((congrAdd Prf.hyp0 (.eqRefl _)).eqTrans (integerCountSum_succ _ _ _).eqSymm)
  simpa only [Fm.subst_eq, MinkowskiBoxes.subst_prefixCount, subst_integerBoxes,
    subst_integerCountSum, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE r all

/-- The sum-facing count is the actual concatenated integer point-list count,
not a separate cardinality quantity assumed equal to it. -/
theorem integer_count_sum (N B : PTm n) :
    Γ ⊢[PRAAx] integerCountSum N B (length B) ≐ MinkowskiBoxUnion.total N (integerBoxes N B) :=
  (prefix_integer_count_sum N B (length B)).eqSymm.eqTrans
    (congrAp3 (sum2F (Foundations.SequenceComposition.lengthBody MinkowskiBoxes.boxF))
      (MinkowskiRationalBoxes.integerBoxes_length N B).eqSymm (.eqRefl (integerBoxes N B)) (.eqRefl N))

theorem box_content_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (rationalSides (var 0) (var 1) ⟶ lt (var 2) (length (var 1)) ⟶
        (boxDenominator (var 0) (var 1) (var 2)*integerCount (var 0) (var 1) (var 2) ≐
          pw (mesh (var 0) (var 1)) (var 0)*boxNumerator (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (box_content_clears (var 0) (var 1) (var 2) Prf.hyp1 Prf.hyp0)))

theorem box_denominator_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (le one (boxDenominator (var 0) (var 1) (var 2))) :=
  closeUniv 3 (box_denominator_positive _ _ _)

theorem integer_count_sum_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (integerCountSum (var 0) (var 1) (length (var 1)) ≐ MinkowskiBoxUnion.total (var 0) (integerBoxes (var 0) (var 1))) :=
  closeUniv 2 (integer_count_sum _ _)


/-- Original rational sum-of-products content, computed before any count or
mesh claim. The denominator product and numerator accumulator are actual PR
programs on the original endpoint width fractions. -/
def contentNumerator (N B : PTm n) : PTm n :=
  MinkowskiContentSum.numerator numeratorAt denominatorAt (length B) (pairT N B)
def contentDenominator (N B : PTm n) : PTm n :=
  MinkowskiContentSum.denominator denominatorAt (length B) (pairT N B)

@[simp] theorem subst_contentNumerator {l : ℕ} (σ : Fin n → PTm l) (N B : PTm n) :
    Syn.subst σ (contentNumerator N B) = contentNumerator (Syn.subst σ N) (Syn.subst σ B) := by
  simp only [contentNumerator, MinkowskiContentSum.subst_numerator, subst_length, subst_pairT]
@[simp] theorem subst_contentDenominator {l : ℕ} (σ : Fin n → PTm l) (N B : PTm n) :
    Syn.subst σ (contentDenominator N B) = contentDenominator (Syn.subst σ N) (Syn.subst σ B) := by
  simp only [contentDenominator, MinkowskiContentSum.subst_denominator, subst_length, subst_pairT]

/-- The pointwise premise of the generic rational-sum theorem is here derived
from original endpoint positivity and the actual per-box product identity. -/
theorem content_clearing (N B : PTm n) (h : Γ ⊢[PRAAx] rationalSides N B) :
    Γ ⊢[PRAAx] MinkowskiContentSum.clearing countAt numeratorAt denominatorAt (length B)
      (pw (mesh N B) N) (pairT N B) := by
  refine .allI (.impI ?_)
  have guards : Γ.map Fm.shift ⊢[PRAAx] rationalSides (Syn.shift N) (Syn.shift B) := by
    simpa only [Fm.shift, subst_rationalSides, Syn.shift] using h.shift
  have identity := box_content_clears (Syn.shift N) (Syn.shift B) (var 0) guards.wk
    (Prf.hyp0 : lt (var 0) (length (Syn.shift B)) :: Γ.map Fm.shift ⊢[PRAAx] _)
  have out := (congrMul (denominatorAt_at (Syn.shift N) (Syn.shift B) (var 0))
    (countAt_at (Syn.shift N) (Syn.shift B) (var 0))).eqTrans
    (identity.eqTrans (congrMul (.eqRefl _) (numeratorAt_at (Syn.shift N) (Syn.shift B) (var 0)).eqSymm))
  simpa only [Syn.shift, subst_pairT, subst_ap2, subst_mesh, subst_length] using out

theorem content_denominators_positive (N B : PTm n) :
    Γ ⊢[PRAAx] MinkowskiContentSum.positiveDenominators denominatorAt (length B) (pairT N B) := by
  refine .allI (.impI ?_)
  have pos : Γ.map Fm.shift ⊢[PRAAx] le one (boxDenominator (Syn.shift N) (Syn.shift B) (var 0)) :=
    box_denominator_positive _ _ _
  have out := le_congr (.eqRefl _) (denominatorAt_at (Syn.shift N) (Syn.shift B) (var 0)).eqSymm pos
  simpa only [Syn.shift, subst_pairT, subst_length] using out.wk

theorem content_denominator_positive (N B : PTm n) : Γ ⊢[PRAAx] le one (contentDenominator N B) :=
  MinkowskiContentSum.denominator_positive denominatorAt (length B) (pairT N B) (content_denominators_positive N B)

/-- Exact source eq:cell-count, with original rational content and the actual
concatenated integer point-list count. No global identity is a premise. -/
theorem content_count_identity (N B : PTm n) (h : Γ ⊢[PRAAx] rationalSides N B) :
    Γ ⊢[PRAAx] contentDenominator N B*MinkowskiBoxUnion.total N (integerBoxes N B) ≐
      pw (mesh N B) N*contentNumerator N B :=
  (congrMul (.eqRefl _) (integer_count_sum N B).eqSymm).eqTrans
    (MinkowskiContentSum.sum_clearing countAt numeratorAt denominatorAt (length B)
      (pw (mesh N B) N) (pairT N B) (content_clearing N B h))

/-- The original rational content inequality W>1 yields the required actual
integer threshold. No integer-count inequality is supplied. -/
theorem rational_count_threshold (N B : PTm n) (h : Γ ⊢[PRAAx] rationalSides N B)
    (hW : Γ ⊢[PRAAx] lt (contentDenominator N B) (contentNumerator N B)) :
    Γ ⊢[PRAAx] lt (pw (mesh N B) N) (MinkowskiBoxUnion.total N (integerBoxes N B)) :=
  lt_congr (.eqRefl _) (integer_count_sum N B)
    (MinkowskiContentSum.strict_count countAt numeratorAt denominatorAt (length B)
      (pw (mesh N B) N) (pairT N B) (content_clearing N B h)
      (MinkowskiMesh.horizon_positive N (mesh N B) (MinkowskiRationalBoxes.mesh_positive N B)) hW)

def extractor (N B : PTm n) : PTm n :=
  ap3 MinkowskiMesh.meshF N (mesh N B) (MinkowskiBoxes.boxes N (integerBoxes N B))

@[simp] theorem subst_extractor {l : ℕ} (σ : Fin n → PTm l) (N B : PTm n) :
    Syn.subst σ (extractor N B) = extractor (Syn.subst σ N) (Syn.subst σ B) := by
  simp only [extractor, subst_ap3, subst_mesh, MinkowskiBoxes.subst_boxes, subst_integerBoxes]

/-- Actual original rational endpoint/content guards now feed the complete
integer mesh extractor. Geometric InsidePhi and the numerical Boolean BoxOK
reflection are subsequent adapters, not hidden premises of this theorem. -/
theorem rational_mesh (N B : PTm n) (h : Γ ⊢[PRAAx] rationalSides N B)
    (hd : Γ ⊢[PRAAx] MinkowskiRationalBoxes.rationalDisjoint N B)
    (hW : Γ ⊢[PRAAx] lt (contentDenominator N B) (contentNumerator N B)) :
    Γ ⊢[PRAAx] MinkowskiMesh.correct N (mesh N B) (MinkowskiBoxes.boxes N (integerBoxes N B)) (extractor N B) :=
  MinkowskiBoxUnion.union_mesh N (mesh N B) (integerBoxes N B)
    (MinkowskiRationalBoxes.integer_allSides N B h) (MinkowskiRationalBoxes.integer_disjoint N B hd)
    (MinkowskiRationalBoxes.mesh_positive N B) (rational_count_threshold N B h hW)

def contentNumeratorF : PR 2 := PTm.toPR (contentNumerator (var 0) (var 1))
def contentDenominatorF : PR 2 := PTm.toPR (contentDenominator (var 0) (var 1))
def extractorF : PR 2 := PTm.toPR (extractor (var 0) (var 1))

theorem contentNumerator_at (N B : PTm n) : Γ ⊢[PRAAx] ap2 contentNumeratorF N B ≐ contentNumerator N B := by
  have h := toPR_eq (Γ := Γ) (contentNumerator (var 0) (var 1) : PTm 2) ![N,B]
  simpa only [contentNumeratorF, ap2, subst_contentNumerator, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem contentDenominator_at (N B : PTm n) : Γ ⊢[PRAAx] ap2 contentDenominatorF N B ≐ contentDenominator N B := by
  have h := toPR_eq (Γ := Γ) (contentDenominator (var 0) (var 1) : PTm 2) ![N,B]
  simpa only [contentDenominatorF, ap2, subst_contentDenominator, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem extractor_at (N B : PTm n) : Γ ⊢[PRAAx] ap2 extractorF N B ≐ extractor N B := by
  have h := toPR_eq (Γ := Γ) (extractor (var 0) (var 1) : PTm 2) ![N,B]
  simpa only [extractorF, ap2, subst_extractor, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using h

/-- Correctness also names the actual fixed PR2 output program. -/
theorem rational_program_correct (N B : PTm n) (h : Γ ⊢[PRAAx] rationalSides N B)
    (hd : Γ ⊢[PRAAx] MinkowskiRationalBoxes.rationalDisjoint N B)
    (hW : Γ ⊢[PRAAx] lt (contentDenominator N B) (contentNumerator N B)) :
    Γ ⊢[PRAAx] MinkowskiMesh.correct N (mesh N B) (MinkowskiBoxes.boxes N (integerBoxes N B)) (ap2 extractorF N B) := by
  have e := (extractor_at (Γ := Γ) N B).eqSymm
  exact MinkowskiMesh.good_congr N (mesh N B) (MinkowskiBoxes.boxes N (integerBoxes N B))
    (fstT (fstT (extractor N B))) (sndT (fstT (extractor N B)))
    (fstT (sndT (extractor N B))) (sndT (sndT (extractor N B)))
    (fstT (fstT (ap2 extractorF N B))) (sndT (fstT (ap2 extractorF N B)))
    (fstT (sndT (ap2 extractorF N B))) (sndT (sndT (ap2 extractorF N B)))
    (congrFst (congrFst e)) (congrSnd (congrFst e)) (congrFst (congrSnd e)) (congrSnd (congrSnd e))
    (rational_mesh N B h hd hW)

theorem content_count_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (rationalSides (var 0) (var 1) ⟶
        (contentDenominator (var 0) (var 1)*MinkowskiBoxUnion.total (var 0) (integerBoxes (var 0) (var 1)) ≐
          pw (mesh (var 0) (var 1)) (var 0)*contentNumerator (var 0) (var 1))) :=
  closeUniv 2 (.impI (content_count_identity (var 0) (var 1) Prf.hyp0))

theorem rational_count_threshold_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (rationalSides (var 0) (var 1) ⟶ lt (contentDenominator (var 0) (var 1)) (contentNumerator (var 0) (var 1)) ⟶
        lt (pw (mesh (var 0) (var 1)) (var 0)) (MinkowskiBoxUnion.total (var 0) (integerBoxes (var 0) (var 1)))) :=
  closeUniv 2 (.impI (.impI (rational_count_threshold (var 0) (var 1) Prf.hyp1 Prf.hyp0)))

theorem rational_mesh_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (rationalSides (var 0) (var 1) ⟶ MinkowskiRationalBoxes.rationalDisjoint (var 0) (var 1) ⟶
        lt (contentDenominator (var 0) (var 1)) (contentNumerator (var 0) (var 1)) ⟶
          MinkowskiMesh.correct (var 0) (mesh (var 0) (var 1)) (MinkowskiBoxes.boxes (var 0) (integerBoxes (var 0) (var 1)))
            (ap2 extractorF (var 0) (var 1))) :=
  closeUniv 2 (.impI (.impI (.impI (rational_program_correct (var 0) (var 1) Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem content_programs_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      ((ap2 contentNumeratorF (var 0) (var 1) ≐ contentNumerator (var 0) (var 1)) ⋏
        ((ap2 contentDenominatorF (var 0) (var 1) ≐ contentDenominator (var 0) (var 1)) ⋏
          (ap2 extractorF (var 0) (var 1) ≐ extractor (var 0) (var 1)))) :=
  closeUniv 2 (.andI (contentNumerator_at _ _) (.andI (contentDenominator_at _ _) (extractor_at _ _)))

end LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiRationalContent
