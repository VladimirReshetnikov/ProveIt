import DiophantineConsistency.NaturalSimplifier
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Fintype.Card

/-!
# Executable removal of unused natural witnesses

A deduplicated list records exactly the occurrences appearing in two supplied
natural expressions. Their translation uses only that list's finite index
range. Both directions of the existential correspondence supply assignments
explicitly, including the case when the list is empty.
-/

namespace DiophantineConsistency.NatExpr

variable {σ : Type*}

/-- Variable occurrences, computed in syntax order. -/
def occurrences : NatExpr σ → List σ
  | .constant _ => []
  | .var i => [i]
  | .add p q | .mul p q => p.occurrences ++ q.occurrences

/-- A computable variable renaming for natural syntax. -/
def rename {τ : Type*} (f : σ → τ) : NatExpr σ → NatExpr τ
  | .constant a => .constant a
  | .var i => .var (f i)
  | .add p q => .add (p.rename f) (q.rename f)
  | .mul p q => .mul (p.rename f) (q.rename f)

@[simp] theorem eval_rename {τ : Type*} (f : σ → τ) (e : NatExpr σ) (v : τ → ℕ) :
    (e.rename f).eval v = e.eval (v ∘ f) := by
  induction e <;> simp_all [rename, eval, Function.comp_def]

@[simp] theorem count_rename {τ : Type*} (f : σ → τ) (e : NatExpr σ) :
    QuarticCompiler.Gates.count (e.rename f) = QuarticCompiler.Gates.count e := by
  induction e <;> simp_all [rename, QuarticCompiler.Gates.count]

end DiophantineConsistency.NatExpr

namespace DiophantineConsistency.WitnessCompaction

open NatExpr

variable {σ : Type*} [DecidableEq σ]

/-- Retain one occurrence of each used variable. -/
def used (p q : NatExpr σ) : List σ := (p.occurrences ++ q.occurrences).dedup

def count (p q : NatExpr σ) : ℕ := (used p q).length

/-- Read packed coordinates; unused source coordinates are assigned zero. -/
def unpack (indices : List σ) (v : Fin indices.length → ℕ) (i : σ) : ℕ :=
  if h : i ∈ indices then v ⟨indices.idxOf i, List.idxOf_lt_length_of_mem h⟩ else 0

/-- Pack an old assignment by the literal variable list. -/
def pack (indices : List σ) (v : σ → ℕ) (i : Fin indices.length) : ℕ :=
  v (indices.get i)

/-- Replace each listed source variable by its finite position. A variable not
on the list is replaced by zero, so this definition also handles an empty list. -/
def translate (indices : List σ) : NatExpr σ → NatExpr (Fin indices.length)
  | .constant a => .constant a
  | .var i =>
      if h : i ∈ indices then .var ⟨indices.idxOf i, List.idxOf_lt_length_of_mem h⟩
      else .constant 0
  | .add p q => .add (translate indices p) (translate indices q)
  | .mul p q => .mul (translate indices p) (translate indices q)

@[simp] theorem eval_translate (indices : List σ) (e : NatExpr σ)
    (v : Fin indices.length → ℕ) :
    (translate indices e).eval v = e.eval (unpack indices v) := by
  induction e with
  | constant a => rfl
  | var i => simp [translate, eval, unpack]; split <;> rfl
  | add p q hp hq | mul p q hp hq => simp_all [translate, eval]

@[simp] theorem count_translate (indices : List σ) (e : NatExpr σ) :
    QuarticCompiler.Gates.count (translate indices e) = QuarticCompiler.Gates.count e := by
  induction e with
  | constant a => rfl
  | var i => unfold translate; split <;> rfl
  | add p q hp hq | mul p q hp hq => simp_all [translate, QuarticCompiler.Gates.count]

@[simp] theorem unpack_pack_of_mem (indices : List σ) (v : σ → ℕ) {i : σ}
    (h : i ∈ indices) : unpack indices (pack indices v) i = v i := by
  simp only [unpack, dif_pos h, pack]
  rw [List.idxOf_get]

omit [DecidableEq σ] in
/-- Expression values depend only on coordinates that occur syntactically. -/
theorem eval_congr (e : NatExpr σ) {v w : σ → ℕ}
    (h : ∀ i ∈ e.occurrences, v i = w i) : e.eval v = e.eval w := by
  induction e with
  | constant a => rfl
  | var i => exact h i (by simp [occurrences])
  | add p q hp hq | mul p q hp hq =>
      simp only [eval]
      rw [hp (fun i hi => h i (by simp [occurrences, hi])),
        hq (fun i hi => h i (by simp [occurrences, hi]))]

/-- Both expressions contain only occurrences recorded by `used`. -/
theorem mem_used_left (p q : NatExpr σ) {i : σ} (h : i ∈ p.occurrences) : i ∈ used p q := by
  simp [used, h]

theorem mem_used_right (p q : NatExpr σ) {i : σ} (h : i ∈ q.occurrences) : i ∈ used p q := by
  simp [used, h]

def left (p q : NatExpr σ) : NatExpr (Fin (count p q)) := translate (used p q) p
def right (p q : NatExpr σ) : NatExpr (Fin (count p q)) := translate (used p q) q

/-- Witness compaction preserves solvability over the natural numbers. -/
theorem exists_eval_eq_iff (p q : NatExpr σ) :
    (∃ v : σ → ℕ, p.eval v = q.eval v) ↔
      ∃ v : Fin (count p q) → ℕ, (left p q).eval v = (right p q).eval v := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨pack (used p q) v, ?_⟩
    change (translate (used p q) p).eval _ = (translate (used p q) q).eval _
    rw [eval_translate (used p q) p, eval_translate (used p q) q]
    have hp := eval_congr p (fun i hi => unpack_pack_of_mem (used p q) v (mem_used_left p q hi))
    have hq := eval_congr q (fun i hi => unpack_pack_of_mem (used p q) v (mem_used_right p q hi))
    exact hp.trans (hv.trans hq.symm)
  · rintro ⟨v, hv⟩
    refine ⟨unpack (used p q) v, ?_⟩
    exact (eval_translate (used p q) p v).symm.trans
      (hv.trans (eval_translate (used p q) q v))

/-- The deduplicated coordinate list never exceeds the original finite domain. -/
theorem count_le_card [Fintype σ] (p q : NatExpr σ) : count p q ≤ Fintype.card σ := by
  exact (List.nodup_dedup (p.occurrences ++ q.occurrences)).length_le_card

theorem count_le {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) : count p q ≤ m := by
  simpa using count_le_card p q

/-- Restore the empty input block expected by the quartic compiler. -/
def leftClosed (p q : NatExpr σ) : NatExpr (Empty ⊕ Fin (count p q)) :=
  (left p q).rename Sum.inr

def rightClosed (p q : NatExpr σ) : NatExpr (Empty ⊕ Fin (count p q)) :=
  (right p q).rename Sum.inr

@[simp] theorem count_leftClosed (p q : NatExpr σ) :
    QuarticCompiler.Gates.count (leftClosed p q) = QuarticCompiler.Gates.count p := by
  exact (NatExpr.count_rename _ _).trans (count_translate _ _)

@[simp] theorem count_rightClosed (p q : NatExpr σ) :
    QuarticCompiler.Gates.count (rightClosed p q) = QuarticCompiler.Gates.count q := by
  exact (NatExpr.count_rename _ _).trans (count_translate _ _)

/-- The version with the literal empty input block used by `QuarticCompiler`. -/
theorem exists_closed_eval_eq_iff {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    (∃ w : Fin m → ℕ, p.eval (Sum.elim Empty.elim w) = q.eval (Sum.elim Empty.elim w)) ↔
      ∃ w : Fin (count p q) → ℕ,
        (leftClosed p q).eval (Sum.elim Empty.elim w) =
          (rightClosed p q).eval (Sum.elim Empty.elim w) := by
  have compact := exists_eval_eq_iff p q
  have original :
      (∃ w : Fin m → ℕ, p.eval (Sum.elim Empty.elim w) = q.eval (Sum.elim Empty.elim w)) ↔
        ∃ v : Empty ⊕ Fin m → ℕ, p.eval v = q.eval v := by
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨Sum.elim Empty.elim w, hw⟩
    · rintro ⟨v, hv⟩
      refine ⟨fun i => v (Sum.inr i), ?_⟩
      have he : Sum.elim Empty.elim (fun i => v (Sum.inr i)) = v := by
        funext i
        cases i with
        | inl e => cases e
        | inr _ => rfl
      simpa only [he] using hv
  apply original.trans
  apply compact.trans
  apply exists_congr
  intro w
  simp only [leftClosed, rightClosed, NatExpr.eval_rename]
  rfl

end DiophantineConsistency.WitnessCompaction
