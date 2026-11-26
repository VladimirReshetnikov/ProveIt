import IPRADerivations.Foundations.BoundedSyntax
import IPRADerivations.Foundations.FiniteQueryDemand
import IPRADerivations.Foundations.GapDecision
import IPRADerivations.Foundations.SequenceComposition
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.SubstCommand
import IPRADerivations.Core.Header

/-!
# Integer-facet enlargement preserves the integer lattice points

Source: `diophantine-number-theory/minkowski_ipra/paper/03_polytopes.tex`,
`thm:equality`, equation `eq:same-lattice`.

The dimension, facet count, signed integer coefficient rows, positive facet
bounds and signed integer point are runtime data. A facet entry is the actual
pair `(rowCode,bound)`; rows and points use `MasterCertificate.sequence`.
Each signed entry is a natural pair representing positive minus negative.
The dot product is a genuine pair of primitive-recursive finite sums.

The actual maximum `M` of the bounds determines the rational enlargement
`lambda=(M+2)/(M+1)`. Integer discreteness proves, rather than assumes,
that `(M+1)*abs(dot) <= (M+2)*bound` implies `abs(dot) <= bound`.
Both original and enlarged membership have generated bounded PR checkers.

This is the full lattice-preserving arithmetic step, including zero-valued
bounds as a stronger auxiliary case. The public source endpoint retains
positive dimension, positive facet count, positive bounds and the row/vector
shape checks. It does not supply volume computation, the strict Minkowski
extractor or the finite box certificate; those are further dependencies of
the complete theorem `thm:equality`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiEnlargement

open_ipra
open LeanProofs.IPRA.Foundations
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open LeanProofs.IPRA.Foundations.FiniteQueryDemand
  (finiteMaximum finiteMaximum_at finiteMaximum_zero finiteMaximum_succ subst_finiteMaximum)
open LeanProofs.IPRA.Foundations.GapDecision (zabs subst_zabs)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Actual signed integer decoded from one finite-list entry. -/
def integerAt (code i : PTm n) : ZT n := ⟨fstT (entry code i), sndT (entry code i)⟩

@[simp] theorem subst_integerAt {m : ℕ} (σ : Fin n → PTm m) (code i : PTm n) :
    (integerAt code i).subst σ = integerAt (Syn.subst σ code) (Syn.subst σ i) := by
  simp only [integerAt, ZT.subst, subst_fstT, subst_sndT, subst_entry]

def dotBody : ZT 2 := integerAt (fstT (var 1)) (var 0) * integerAt (sndT (var 1)) (var 0)

/-- The actual signed dot product of the first `dimension` coordinates. -/
def dot (dimension row point : PTm n) : ZT n :=
  ⟨ap2 (sumF dotBody.pos) dimension (pairT row point),
    ap2 (sumF dotBody.neg) dimension (pairT row point)⟩

@[simp] theorem subst_dot {m : ℕ} (σ : Fin n → PTm m) (dimension row point : PTm n) :
    (dot dimension row point).subst σ =
      dot (Syn.subst σ dimension) (Syn.subst σ row) (Syn.subst σ point) := by
  simp only [dot, ZT.subst, subst_ap2, subst_pairT]

theorem dot_zero (row point : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (dot zero row point) (ZT.natLit 0) := by
  apply ZT.derive
  rw [ZT.toZ_natLit]
  simp only [dot, ZT.toZ]
  rw [natEq (sum_zero (Γ := Γ) dotBody.pos (pairT row point)),
    natEq (sum_zero (Γ := Γ) dotBody.neg (pairT row point))]
  ipra_simps
  ring

theorem dotBody_at (i row point : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (dotBody.subst ![i, pairT row point]) (integerAt row i * integerAt point i) := by
  have er : Γ ⊢[PRAAx] entry (fstT (pairT row point)) i ≐ entry row i :=
    SequenceComposition.entry_congr (fst_pair _ _) (.eqRefl _)
  have ep : Γ ⊢[PRAAx] entry (sndT (pairT row point)) i ≐ entry point i :=
    SequenceComposition.entry_congr (snd_pair _ _) (.eqRefl _)
  apply ZT.derive
  simp only [dotBody, ZT.subst_mul, subst_integerAt, subst_fstT, subst_sndT,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, ZT.toZ_mul]
  simp only [integerAt, ZT.toZ]
  rw [natEq (congrFst er), natEq (congrSnd er), natEq (congrFst ep), natEq (congrSnd ep)]

theorem dot_succ (dimension row point : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (dot (succ dimension) row point)
      (dot dimension row point + integerAt row dimension * integerAt point dimension) := by
  apply ZT.derive
  have hp := natEq (sum_succ (Γ := Γ) dotBody.pos dimension (pairT row point))
  have hn := natEq (sum_succ (Γ := Γ) dotBody.neg dimension (pairT row point))
  have product := ZT.toZ_eq (dotBody_at (Γ := Γ) dimension row point)
  simp only [Q.mk_add, map_add] at hp hn
  simp only [ZT.toZ, ZT.subst, inst2] at product
  calc
    _ = ZT.toZ Γ (dot dimension row point) + ZT.toZ Γ (integerAt row dimension * integerAt point dimension) := by
      change (Groth.ι (Q.mk Γ (ap2 (sumF dotBody.pos) (succ dimension) (pairT row point))) -
          Groth.ι (Q.mk Γ (ap2 (sumF dotBody.neg) (succ dimension) (pairT row point)))) =
        (Groth.ι (Q.mk Γ (ap2 (sumF dotBody.pos) dimension (pairT row point))) -
          Groth.ι (Q.mk Γ (ap2 (sumF dotBody.neg) dimension (pairT row point)))) +
        (Groth.ι (Q.mk Γ (integerAt row dimension * integerAt point dimension).pos) -
          Groth.ι (Q.mk Γ (integerAt row dimension * integerAt point dimension).neg))
      linear_combination hp - hn + product
    _ = _ := (ZT.toZ_add (dot dimension row point) (integerAt row dimension * integerAt point dimension)).symm

/-- The dot-product pair itself is one fixed primitive-recursive program. -/
def dotF : PR 3 := PTm.toPR (pairT (dot (var 0) (var 1) (var 2)).pos (dot (var 0) (var 1) (var 2)).neg)

theorem dot_program_at (dimension row point : PTm n) :
    Γ ⊢[PRAAx] ap3 dotF dimension row point ≐ pairT (dot dimension row point).pos (dot dimension row point).neg := by
  have h := toPR_eq (Γ := Γ) (pairT (dot (var 0) (var 1) (var 2)).pos (dot (var 0) (var 1) (var 2)).neg)
    ![dimension, row, point]
  simpa [dotF, ap3, dot, ZT.subst] using h

def row (facets i : PTm n) : PTm n := fstT (entry facets i)
def bound (facets i : PTm n) : PTm n := sndT (entry facets i)
def absolute (dimension facets point i : PTm n) : PTm n := zabs (dot dimension (row facets i) point)

@[simp] theorem subst_row {m : ℕ} (σ : Fin n → PTm m) (facets i : PTm n) :
    Syn.subst σ (row facets i) = row (Syn.subst σ facets) (Syn.subst σ i) := by simp [row]
ipra_subst bound
@[simp] theorem subst_absolute {m : ℕ} (σ : Fin n → PTm m) (dimension facets point i : PTm n) :
    Syn.subst σ (absolute dimension facets point i) =
      absolute (Syn.subst σ dimension) (Syn.subst σ facets) (Syn.subst σ point) (Syn.subst σ i) := by
  unfold absolute
  rw [subst_zabs, subst_dot, subst_row]

def boundBody : PTm 2 := bound (var 1) (var 0)
def maximumBound (facets : PTm n) : PTm n := finiteMaximum boundBody (length facets) facets
def lambdaDenominator (facets : PTm n) : PTm n := succ (maximumBound facets)
def lambdaNumerator (facets : PTm n) : PTm n := succ (succ (maximumBound facets))

@[simp] theorem subst_maximumBound {m : ℕ} (σ : Fin n → PTm m) (facets : PTm n) :
    Syn.subst σ (maximumBound facets) = maximumBound (Syn.subst σ facets) := by simp [maximumBound]
ipra_subst lambdaDenominator
ipra_subst lambdaNumerator

theorem bound_le_maximum {facets i : PTm n} (hi : Γ ⊢[PRAAx] lt i (length facets)) :
    Γ ⊢[PRAAx] le (bound facets i) (maximumBound facets) := by
  simpa [boundBody, inst2, maximumBound] using finiteMaximum_at boundBody hi

/-- Integer discreteness is the essential arithmetic step, valid also at `b=0`. -/
theorem integer_rounding {v b M : PTm n} (hb : Γ ⊢[PRAAx] le b M)
    (h : Γ ⊢[PRAAx] le (succ M * v) (succ (succ M) * b)) : Γ ⊢[PRAAx] le v b := by
  refine .orE (lt_or_le b v) ?_ Prf.hyp0
  have enlarged : (lt b v :: Γ) ⊢[PRAAx] le (succ M * succ b) (succ (succ M) * b) :=
    le_trans (le_mul_mono (le_refl _) Prf.hyp0) h.wk
  have impossible : (lt b v :: Γ) ⊢[PRAAx] le (succ M) b :=
    le_of_add_le_add_right (le_congr
      (by ipra_ring : (lt b v :: Γ) ⊢[PRAAx] succ M * succ b ≐ succ M + succ M * b)
      (by ipra_ring : (lt b v :: Γ) ⊢[PRAAx] succ (succ M) * b ≐ b + succ M * b) enlarged)
  exact le_lt_absurd _ hb.wk impossible

theorem original_to_enlarged (v b M : PTm n) (h : Γ ⊢[PRAAx] le v b) :
    Γ ⊢[PRAAx] le (succ M * v) (succ (succ M) * b) :=
  le_mul_mono (le_succ_self (succ M)) h

def member (dimension facets point : PTm n) : Fm PTm n :=
  .all (lt (var 0) (length (Syn.shift facets)) ⟶
    le (absolute (Syn.shift dimension) (Syn.shift facets) (Syn.shift point) (var 0))
      (bound (Syn.shift facets) (var 0)))

def enlargedMember (dimension facets point : PTm n) : Fm PTm n :=
  .all (lt (var 0) (length (Syn.shift facets)) ⟶
    le (lambdaDenominator (Syn.shift facets) * absolute (Syn.shift dimension) (Syn.shift facets) (Syn.shift point) (var 0))
      (lambdaNumerator (Syn.shift facets) * bound (Syn.shift facets) (var 0)))

ipra_subst member [Syn.up, Syn.subst_shift, ← Syn.shift_subst]
ipra_subst enlargedMember [Syn.up, Syn.subst_shift, ← Syn.shift_subst]

theorem member_at {dimension facets point i : PTm n} (h : Γ ⊢[PRAAx] member dimension facets point)
    (hi : Γ ⊢[PRAAx] lt i (length facets)) :
    Γ ⊢[PRAAx] le (absolute dimension facets point i) (bound facets i) := by
  have e := Prf.allE i h
  simp [member] at e
  exact .impE e hi

theorem enlarged_at {dimension facets point i : PTm n} (h : Γ ⊢[PRAAx] enlargedMember dimension facets point)
    (hi : Γ ⊢[PRAAx] lt i (length facets)) :
    Γ ⊢[PRAAx] le (lambdaDenominator facets * absolute dimension facets point i)
      (lambdaNumerator facets * bound facets i) := by
  have e := Prf.allE i h
  simp [enlargedMember] at e
  exact .impE e hi

theorem enlargement_subset (dimension facets point : PTm n)
    (h : Γ ⊢[PRAAx] enlargedMember dimension facets point) : Γ ⊢[PRAAx] member dimension facets point := by
  refine .allI (.impI ?_)
  have shifted : Γ.map Fm.shift ⊢[PRAAx]
      enlargedMember (Syn.shift dimension) (Syn.shift facets) (Syn.shift point) := by
    simpa only [Fm.shift, subst_enlargedMember, Syn.shift] using h.shift
  exact integer_rounding (bound_le_maximum Prf.hyp0) (enlarged_at shifted.wk Prf.hyp0)

theorem original_subset (dimension facets point : PTm n)
    (h : Γ ⊢[PRAAx] member dimension facets point) : Γ ⊢[PRAAx] enlargedMember dimension facets point := by
  refine .allI (.impI ?_)
  have shifted : Γ.map Fm.shift ⊢[PRAAx] member (Syn.shift dimension) (Syn.shift facets) (Syn.shift point) := by
    simpa only [Fm.shift, subst_member, Syn.shift] using h.shift
  exact original_to_enlarged _ _ _ (member_at shifted.wk Prf.hyp0)

/-- `eq:same-lattice`: equality of the two predicates on actual integer codes. -/
theorem same_lattice (dimension facets point : PTm n) :
    Γ ⊢[PRAAx] Fm.iff (enlargedMember dimension facets point) (member dimension facets point) :=
  .iffI (.impI (enlargement_subset _ _ _ Prf.hyp0)) (.impI (original_subset _ _ _ Prf.hyp0))

/-! ## Source shape guards and actual bounded verifier programs -/

def bodyGuard (dimension facets : PTm n) : Fm PTm n :=
  le one dimension ⋏ (le one (length facets) ⋏
    .all (lt (var 0) (length (Syn.shift facets)) ⟶
      (le one (bound (Syn.shift facets) (var 0)) ⋏
        (length (row (Syn.shift facets) (var 0)) ≐ Syn.shift dimension))))

def memberSyntax : BoundedSyntax.BFm 3 :=
  .all (length (var 1))
    (.le (absolute (var 1) (var 2) (var 3) (var 0)) (bound (var 2) (var 0)))

def enlargedSyntax : BoundedSyntax.BFm 3 :=
  .all (length (var 1))
    (.le (lambdaDenominator (var 2) * absolute (var 1) (var 2) (var 3) (var 0))
      (lambdaNumerator (var 2) * bound (var 2) (var 0)))

def bodyGuardSyntax : BoundedSyntax.BFm 2 :=
  .and (.le one (var 0)) (.and (.le one (length (var 1)))
    (.all (length (var 1)) (.and (.le one (bound (var 2) (var 0)))
      (.eq (length (row (var 2) (var 0))) (var 1)))))

def memberF : PR 3 := BoundedSyntax.bitF memberSyntax
def enlargedF : PR 3 := BoundedSyntax.bitF enlargedSyntax
def bodyGuardF : PR 2 := BoundedSyntax.bitF bodyGuardSyntax

theorem memberSyntax_at (dimension facets point : PTm n) :
    (BoundedSyntax.formula memberSyntax).subst ![dimension, facets, point] = member dimension facets point := by
  simp [memberSyntax, BoundedSyntax.formula, BoundedSyntax.BFm.le, member,
    Syn.up, Syn.subst_shift, ← Syn.shift_subst, le]

theorem enlargedSyntax_at (dimension facets point : PTm n) :
    (BoundedSyntax.formula enlargedSyntax).subst ![dimension, facets, point] = enlargedMember dimension facets point := by
  simp [enlargedSyntax, BoundedSyntax.formula, BoundedSyntax.BFm.le, enlargedMember,
    Syn.up, Syn.subst_shift, ← Syn.shift_subst, le]

theorem bodyGuardSyntax_at (dimension facets : PTm n) :
    (BoundedSyntax.formula bodyGuardSyntax).subst ![dimension, facets] = bodyGuard dimension facets := by
  simp [bodyGuardSyntax, BoundedSyntax.formula, BoundedSyntax.BFm.le, bodyGuard,
    Syn.up, Syn.subst_shift, ← Syn.shift_subst, le]

theorem member_reflection (dimension facets point : PTm n) :
    Γ ⊢[PRAAx] Fm.iff (ap3 memberF dimension facets point ≐ one) (member dimension facets point) := by
  have prog := BoundedSyntax.program_correct (Γ := Γ) memberSyntax ![dimension, facets, point]
  have reflect := BoundedSyntax.bounded_reflection (Γ := Γ) memberSyntax ![dimension, facets, point]
  rw [memberSyntax_at] at reflect
  exact (Prf.iffI (.impI (prog.eqSymm.wk.eqTrans Prf.hyp0))
    (.impI (prog.wk.eqTrans Prf.hyp0))).iffTrans reflect

theorem enlarged_reflection (dimension facets point : PTm n) :
    Γ ⊢[PRAAx] Fm.iff (ap3 enlargedF dimension facets point ≐ one) (enlargedMember dimension facets point) := by
  have prog := BoundedSyntax.program_correct (Γ := Γ) enlargedSyntax ![dimension, facets, point]
  have reflect := BoundedSyntax.bounded_reflection (Γ := Γ) enlargedSyntax ![dimension, facets, point]
  rw [enlargedSyntax_at] at reflect
  exact (Prf.iffI (.impI (prog.eqSymm.wk.eqTrans Prf.hyp0))
    (.impI (prog.wk.eqTrans Prf.hyp0))).iffTrans reflect

theorem bodyGuard_reflection (dimension facets : PTm n) :
    Γ ⊢[PRAAx] Fm.iff (ap2 bodyGuardF dimension facets ≐ one) (bodyGuard dimension facets) := by
  have prog := BoundedSyntax.program_correct (Γ := Γ) bodyGuardSyntax ![dimension, facets]
  have reflect := BoundedSyntax.bounded_reflection (Γ := Γ) bodyGuardSyntax ![dimension, facets]
  rw [bodyGuardSyntax_at] at reflect
  exact (Prf.iffI (.impI (prog.eqSymm.wk.eqTrans Prf.hyp0))
    (.impI (prog.wk.eqTrans Prf.hyp0))).iffTrans reflect

/-- The actual two membership programs accept exactly the same integer points. -/
theorem checker_equivalence (dimension facets point : PTm n) :
    Γ ⊢[PRAAx] Fm.iff (ap3 enlargedF dimension facets point ≐ one) (ap3 memberF dimension facets point ≐ one) :=
  ((enlarged_reflection dimension facets point).iffTrans (same_lattice dimension facets point)).iffTrans
    (member_reflection dimension facets point).iffSymm

/-- Actual unreduced rational enlargement, numerator first and denominator second. -/
def enlargementF : PR 1 := PTm.toPR (pairT (lambdaNumerator (var 0)) (lambdaDenominator (var 0)))

theorem enlargement_program_at (facets : PTm n) :
    Γ ⊢[PRAAx] app enlargementF ![facets] ≐ pairT (lambdaNumerator facets) (lambdaDenominator facets) := by
  have h := toPR_eq (Γ := Γ) (pairT (lambdaNumerator (var 0)) (lambdaDenominator (var 0))) ![facets]
  simpa [enlargementF] using h

theorem enlargement_denominator_positive (facets : PTm n) :
    Γ ⊢[PRAAx] le one (lambdaDenominator facets) :=
  le_of_eq_add (d := maximumBound facets) (by unfold lambdaDenominator; ipra_ring)

theorem enlargement_strict (facets : PTm n) :
    Γ ⊢[PRAAx] lt (lambdaDenominator facets) (lambdaNumerator facets) := le_refl _

/-- Every expanded bound lies strictly below the next integer threshold. -/
theorem expanded_bound_gap {facets i : PTm n} (hi : Γ ⊢[PRAAx] lt i (length facets)) :
    Γ ⊢[PRAAx] lt (lambdaNumerator facets * bound facets i)
      (lambdaDenominator facets * succ (bound facets i)) := by
  apply le_of_eq_add (d := PTm.monus (maximumBound facets) (bound facets i))
  ipra_lc [lambdaNumerator, lambdaDenominator] natEq (eq_add_of_le (bound_le_maximum hi))

/-- Source guards are retained explicitly even though the lattice identity
itself holds for every finite slab code and for zero right sides. -/
theorem same_lattice_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (bodyGuard (var 0) (var 1) ⟶ (length (var 2) ≐ var 0) ⟶
        Fm.iff (enlargedMember (var 0) (var 1) (var 2)) (member (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (same_lattice (var 0) (var 1) (var 2))))

theorem same_lattice_program_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((ap2 bodyGuardF (var 0) (var 1) ≐ one) ⟶ (length (var 2) ≐ var 0) ⟶
        Fm.iff (ap3 enlargedF (var 0) (var 1) (var 2) ≐ one)
          (ap3 memberF (var 0) (var 1) (var 2) ≐ one)) :=
  closeUniv 3 (.impI (.impI (checker_equivalence (var 0) (var 1) (var 2))))

theorem enlargement_metadata_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      ((app enlargementF ![var 0] ≐ pairT (lambdaNumerator (var 0)) (lambdaDenominator (var 0))) ⋏
        (le one (lambdaDenominator (var 0)) ⋏ lt (lambdaDenominator (var 0)) (lambdaNumerator (var 0)))) :=
  closeUniv 1 (.andI (enlargement_program_at _) (.andI (enlargement_denominator_positive _) (enlargement_strict _)))

#print axioms dot_zero
#print axioms dot_succ
#print axioms dot_program_at
#print axioms bound_le_maximum
#print axioms integer_rounding
#print axioms same_lattice
#print axioms member_reflection
#print axioms enlarged_reflection
#print axioms bodyGuard_reflection
#print axioms expanded_bound_gap
#print axioms same_lattice_closed
#print axioms same_lattice_program_closed
#print axioms enlargement_metadata_closed

end LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiEnlargement
