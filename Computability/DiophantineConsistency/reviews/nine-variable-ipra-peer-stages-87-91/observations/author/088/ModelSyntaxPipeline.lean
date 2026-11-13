import DiophantineConsistency.CompactedJonesSyntax
import DiophantineConsistency.AdaptiveEquationSyntax2011

/-! # The simplified and compacted source syntax over commutative semirings

`SimplifiedJones` folds constants and deletes zero/unit gates of the split
natural source equation (`NatExpr.simplify`), and `CompactedJones` then
renumbers the witnesses that actually occur (`WitnessCompaction`). Both
steps are proved correct over `ℕ` in their own modules. Here the same
arguments are repeated over an arbitrary commutative semiring `R`, with the
semiring evaluator `NatExpr.evalSemiring`:

* `evalSemiring_simplify`: simplification preserves every semiring value;
* `exists_closed_evalSemiring_eq_iff`: compaction preserves solvability;
* `compacted_iff_internalZero`: for a closed representation `r`, the
  compacted equation is solvable in `R` iff `r.expression` has an
  `InternalZero` in `R` (with the literal empty input block).

No order structure is used, so this file deliberately does not open
`LO.FirstOrder.Arithmetic` (whose scoped `LE` instance captures every ring). -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelSyntaxPipeline

/-! ### Simplification -/

section Simplify
variable {σ R : Type*} [CommSemiring R]

theorem evalSemiring_smartAdd (p q : NatExpr σ) (v : σ → R) :
    (NatExpr.smartAdd p q).evalSemiring v = p.evalSemiring v + q.evalSemiring v := by
  unfold NatExpr.smartAdd
  split <;> simp [NatExpr.evalSemiring]

theorem evalSemiring_smartMul (p q : NatExpr σ) (v : σ → R) :
    (NatExpr.smartMul p q).evalSemiring v = p.evalSemiring v * q.evalSemiring v := by
  unfold NatExpr.smartMul
  split <;> simp [NatExpr.evalSemiring]

/-- Constant folding preserves values in every commutative semiring. -/
theorem evalSemiring_simplify (e : NatExpr σ) (v : σ → R) :
    e.simplify.evalSemiring v = e.evalSemiring v := by
  induction e with
  | constant a => rfl
  | var i => rfl
  | add p q hp hq =>
    simp only [NatExpr.simplify, NatExpr.evalSemiring, evalSemiring_smartAdd, hp, hq]
  | mul p q hp hq =>
    simp only [NatExpr.simplify, NatExpr.evalSemiring, evalSemiring_smartMul, hp, hq]

end Simplify

/-! ### Witness compaction -/

section Compaction
variable {σ R : Type*} [CommSemiring R]

theorem evalSemiring_rename {τ : Type*} (f : σ → τ) (e : NatExpr σ) (v : τ → R) :
    (e.rename f).evalSemiring v = e.evalSemiring (v ∘ f) := by
  induction e with
  | constant a => rfl
  | var i => rfl
  | add p q hp hq => simp only [NatExpr.rename, NatExpr.evalSemiring, hp, hq]
  | mul p q hp hq => simp only [NatExpr.rename, NatExpr.evalSemiring, hp, hq]

/-- Values depend only on syntactically occurring coordinates. -/
theorem evalSemiring_congr (e : NatExpr σ) {v w : σ → R}
    (h : ∀ i ∈ e.occurrences, v i = w i) : e.evalSemiring v = e.evalSemiring w := by
  induction e with
  | constant a => rfl
  | var i => exact h i (by simp [NatExpr.occurrences])
  | add p q hp hq | mul p q hp hq =>
      simp only [NatExpr.evalSemiring]
      rw [hp (fun i hi => h i (by simp [NatExpr.occurrences, hi])),
        hq (fun i hi => h i (by simp [NatExpr.occurrences, hi]))]

variable [DecidableEq σ]

/-- Read packed coordinates in `R`; unused source coordinates are zero. -/
def unpackR (indices : List σ) (v : Fin indices.length → R) (i : σ) : R :=
  if h : i ∈ indices then v ⟨indices.idxOf i, List.idxOf_lt_length_of_mem h⟩ else 0

/-- Pack an `R`-assignment along the literal variable list. -/
def packR (indices : List σ) (v : σ → R) (i : Fin indices.length) : R :=
  v (indices.get i)

theorem evalSemiring_translate (indices : List σ) (e : NatExpr σ)
    (v : Fin indices.length → R) :
    (WitnessCompaction.translate indices e).evalSemiring v =
      e.evalSemiring (unpackR indices v) := by
  induction e with
  | constant a => rfl
  | var i =>
    by_cases h : i ∈ indices
    · simp [WitnessCompaction.translate, NatExpr.evalSemiring, unpackR, h]
    · simp [WitnessCompaction.translate, NatExpr.evalSemiring, unpackR, h]
  | add p q hp hq => simp only [WitnessCompaction.translate, NatExpr.evalSemiring, hp, hq]
  | mul p q hp hq => simp only [WitnessCompaction.translate, NatExpr.evalSemiring, hp, hq]

theorem unpackR_packR_of_mem (indices : List σ) (v : σ → R) {i : σ} (h : i ∈ indices) :
    unpackR indices (packR indices v) i = v i := by
  simp only [unpackR, dif_pos h, packR]
  rw [List.idxOf_get]

/-- Witness compaction preserves solvability in every commutative semiring. -/
theorem exists_evalSemiring_eq_iff (p q : NatExpr σ) :
    (∃ v : σ → R, p.evalSemiring v = q.evalSemiring v) ↔
      ∃ v : Fin (WitnessCompaction.count p q) → R,
        (WitnessCompaction.left p q).evalSemiring v =
          (WitnessCompaction.right p q).evalSemiring v := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨packR (WitnessCompaction.used p q) v, ?_⟩
    change (WitnessCompaction.translate (WitnessCompaction.used p q) p).evalSemiring _ =
      (WitnessCompaction.translate (WitnessCompaction.used p q) q).evalSemiring _
    rw [evalSemiring_translate (WitnessCompaction.used p q) p,
      evalSemiring_translate (WitnessCompaction.used p q) q]
    have hp := evalSemiring_congr p (fun i hi =>
      unpackR_packR_of_mem (WitnessCompaction.used p q) v (WitnessCompaction.mem_used_left p q hi))
    have hq := evalSemiring_congr q (fun i hi =>
      unpackR_packR_of_mem (WitnessCompaction.used p q) v (WitnessCompaction.mem_used_right p q hi))
    exact hp.trans (hv.trans hq.symm)
  · rintro ⟨v, hv⟩
    refine ⟨unpackR (WitnessCompaction.used p q) v, ?_⟩
    exact (evalSemiring_translate (WitnessCompaction.used p q) p v).symm.trans
      (hv.trans (evalSemiring_translate (WitnessCompaction.used p q) q v))

/-- The version with the literal empty input block. -/
theorem exists_closed_evalSemiring_eq_iff {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    (∃ w : Fin m → R,
      p.evalSemiring (Sum.elim Empty.elim w) = q.evalSemiring (Sum.elim Empty.elim w)) ↔
      ∃ w : Fin (WitnessCompaction.count p q) → R,
        (WitnessCompaction.leftClosed p q).evalSemiring (Sum.elim Empty.elim w) =
          (WitnessCompaction.rightClosed p q).evalSemiring (Sum.elim Empty.elim w) := by
  have compact := exists_evalSemiring_eq_iff (R := R) p q
  have original :
      (∃ w : Fin m → R,
        p.evalSemiring (Sum.elim Empty.elim w) = q.evalSemiring (Sum.elim Empty.elim w)) ↔
        ∃ v : Empty ⊕ Fin m → R, p.evalSemiring v = q.evalSemiring v := by
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨Sum.elim Empty.elim w, hw⟩
    · rintro ⟨v, hv⟩
      refine ⟨fun i => v (Sum.inr i), ?_⟩
      have he : (Sum.elim Empty.elim (fun i => v (Sum.inr i)) : Empty ⊕ Fin m → R) = v := by
        funext i
        cases i with
        | inl e => cases e
        | inr _ => rfl
      rw [he]
      exact hv
  apply original.trans
  apply compact.trans
  apply exists_congr
  intro w
  simp only [WitnessCompaction.leftClosed, WitnessCompaction.rightClosed, evalSemiring_rename]
  rfl

end Compaction

/-! ### The compacted source equation -/

/-- For a closed representation, the compacted simplified equation is
solvable in `R` iff the representation's expression has an internal zero. -/
theorem compacted_iff_internalZero {A : Prop} (r : Rep Empty (fun _ => A))
    {R : Type*} [CommSemiring R] :
    (∃ w : Fin (WitnessCompaction.count (SimplifiedJones.left r) (SimplifiedJones.right r)) → R,
      (CompactedJones.left r).evalSemiring (Sum.elim Empty.elim w) =
        (CompactedJones.right r).evalSemiring (Sum.elim Empty.elim w)) ↔
      ∃ w : Fin r.witnessCount → R,
        AdaptiveEquationSyntax2011.InternalZero r.expression (Sum.elim Empty.elim w) := by
  refine (exists_closed_evalSemiring_eq_iff (R := R) (SimplifiedJones.left r)
    (SimplifiedJones.right r)).symm.trans (exists_congr fun w => ?_)
  show (SimplifiedJones.left r).evalSemiring (Sum.elim Empty.elim w) =
      (SimplifiedJones.right r).evalSemiring (Sum.elim Empty.elim w) ↔
    r.expression.splitNatural.1.evalSemiring (Sum.elim Empty.elim w) =
      r.expression.splitNatural.2.evalSemiring (Sum.elim Empty.elim w)
  rw [SimplifiedJones.left, SimplifiedJones.right, evalSemiring_simplify, evalSemiring_simplify]

end DiophantineConsistency.ModelSyntaxPipeline
