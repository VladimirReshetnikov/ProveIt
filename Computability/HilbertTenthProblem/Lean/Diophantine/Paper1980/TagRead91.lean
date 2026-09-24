import Diophantine.Paper1980.TagSystem

/-!
# Reading a queue chunk by chunk

A tag system with deletion number `d` and productions `P` reads the letters of its queue at
the positions `0, d, 2d, …`.  When the queue is a concatenation of chunks, the reads within a
chunk depend only on the chunk and on the *phase*, the offset of the next read from the chunk's
start.  `reads d φ X` lists the letters read in `X` from phase `φ`, and `nph d φ X` is the
phase carried into whatever follows `X`.  Both are compositional (`reads_append`,
`nph_append`), and `run_chunk` identifies the actual run: as long as at least `d` letters
follow the chunk, reading it appends the productions of its reads and leaves the queue at the
carried phase, every intermediate queue being long with the expected head.

The binary systems of `TagSystem` are the case `P b = if b then u else [0]` (`step_eq`).
-/

namespace Jones1980

namespace GTag

variable {α : Type*}

/-- One step with deletion number `d` and productions `P`: a queue shorter than `d` is halted. -/
def step (d : ℕ) (P : α → List α) (W : List α) : List α :=
  match W with
  | [] => []
  | x :: W' => if (x :: W').length < d then x :: W' else (x :: W').drop d ++ P x

/-- The letters read in a chunk from phase `φ`. -/
def reads (d : ℕ) : ℕ → List α → List α
  | _, [] => []
  | 0, x :: X => x :: reads d (d - 1) X
  | φ + 1, _ :: X => reads d φ X

/-- The phase carried past a chunk. -/
def nph (d : ℕ) : ℕ → List α → ℕ
  | φ, [] => φ
  | 0, _ :: X => nph d (d - 1) X
  | φ + 1, _ :: X => nph d φ X

variable (d : ℕ)

@[simp] theorem reads_nil (φ : ℕ) : reads d φ ([] : List α) = [] := by cases φ <;> rfl
@[simp] theorem nph_nil (φ : ℕ) : nph d φ ([] : List α) = φ := by cases φ <;> rfl
@[simp] theorem reads_zero_cons (x : α) (X : List α) : reads d 0 (x :: X) = x :: reads d (d - 1) X :=
  rfl
@[simp] theorem nph_zero_cons (x : α) (X : List α) : nph d 0 (x :: X) = nph d (d - 1) X := rfl
@[simp] theorem reads_succ_cons (φ : ℕ) (x : α) (X : List α) :
    reads d (φ + 1) (x :: X) = reads d φ X := rfl
@[simp] theorem nph_succ_cons (φ : ℕ) (x : α) (X : List α) : nph d (φ + 1) (x :: X) = nph d φ X :=
  rfl

theorem reads_append (X Y : List α) : ∀ φ, reads d φ (X ++ Y) = reads d φ X ++ reads d (nph d φ X) Y := by
  induction X with
  | nil => intro φ; simp
  | cons x X ih =>
    intro φ
    cases φ with
    | zero => simp [ih]
    | succ φ => simp [ih]

theorem nph_append (X Y : List α) : ∀ φ, nph d φ (X ++ Y) = nph d (nph d φ X) Y := by
  induction X with
  | nil => intro φ; simp
  | cons x X ih =>
    intro φ
    cases φ with
    | zero => simp [ih]
    | succ φ => simp [ih]

theorem nph_lt (hd : 1 ≤ d) (X : List α) : ∀ φ, φ < d → nph d φ X < d := by
  induction X with
  | nil => intro φ h; simpa using h
  | cons x X ih =>
    intro φ h
    cases φ with
    | zero => simpa using ih (d - 1) (by omega)
    | succ φ => simpa using ih φ (by omega)

/-- A chunk too short to contain the phase is skipped. -/
theorem reads_of_le (X : List α) : ∀ φ, X.length ≤ φ → reads d φ X = [] ∧ nph d φ X = φ - X.length := by
  induction X with
  | nil => intro φ _; simp
  | cons x X ih =>
    intro φ h
    cases φ with
    | zero => simp at h
    | succ φ =>
      simp only [List.length_cons] at h
      simpa [List.length_cons] using ih φ (by omega)

/-- A read inside the chunk. -/
theorem reads_of_lt (X : List α) : ∀ φ (h : φ < X.length),
    reads d φ X = X[φ] :: reads d (d - 1) (X.drop (φ + 1)) ∧
      nph d φ X = nph d (d - 1) (X.drop (φ + 1)) := by
  induction X with
  | nil => intro φ h; simp at h
  | cons x X ih =>
    intro φ h
    cases φ with
    | zero => simp
    | succ φ =>
      simp only [List.length_cons] at h
      simpa using ih φ (by omega)

/-- A chunk of exactly `d` letters is read once, at the phase, and the phase is kept. -/
theorem reads_row (hd : 1 ≤ d) (X : List α) (hX : X.length = d) (φ : ℕ) (hφ : φ < d) :
    reads d φ X = [X[φ]'(by omega)] ∧ nph d φ X = φ := by
  obtain ⟨h1, h2⟩ := reads_of_lt d X φ (by omega)
  obtain ⟨h3, h4⟩ := reads_of_le d (X.drop (φ + 1)) (d - 1) (by simp; omega)
  refine ⟨by rw [h1, h3], by rw [h2, h4]; simp; omega⟩

theorem step_cons (P : α → List α) {x : α} {W : List α} (h : d ≤ (x :: W).length) :
    step d P (x :: W) = (x :: W).drop d ++ P x := by
  show (if (x :: W).length < d then x :: W else _) = _
  rw [if_neg (by omega)]

/-- **Reading a chunk.** -/
theorem run_chunk (P : α → List α) (hd : 1 ≤ d) (X : List α) :
    ∀ (φ : ℕ) (Y : List α), φ < d → d ≤ Y.length →
      (step d P)^[(reads d φ X).length] ((X ++ Y).drop φ) =
          (Y ++ (reads d φ X).flatMap P).drop (nph d φ X) ∧
        ∀ i (hi : i < (reads d φ X).length),
          d ≤ ((step d P)^[i] ((X ++ Y).drop φ)).length ∧
            ((step d P)^[i] ((X ++ Y).drop φ)).head? = some ((reads d φ X)[i]) := by
  induction X with
  | nil =>
    intro φ Y hφ hY
    simp
  | cons x X ih =>
    intro φ Y hφ hY
    cases φ with
    | zero =>
      have hlong : d ≤ (x :: (X ++ Y)).length := by simp; omega
      have hs : step d P (x :: (X ++ Y)) = (X ++ (Y ++ P x)).drop (d - 1) := by
        rw [step_cons d P hlong]
        obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
        have h' : d' ≤ (X ++ Y).length := by simp at hlong ⊢; omega
        rw [List.drop_succ_cons, Nat.add_sub_cancel, ← List.append_assoc,
          List.drop_append_of_le_length (l₁ := X ++ Y) (l₂ := P x) h']
      obtain ⟨ih1, ih2⟩ := ih (d - 1) (Y ++ P x) (by omega) (by simp; omega)
      simp only [reads_zero_cons, nph_zero_cons, List.length_cons, List.drop_zero,
        List.cons_append]
      refine ⟨?_, ?_⟩
      · rw [Function.iterate_succ_apply, hs, ih1, List.flatMap_cons, List.append_assoc]
      · intro i hi
        cases i with
        | zero => exact ⟨by simpa using hlong, rfl⟩
        | succ i =>
          rw [Function.iterate_succ_apply, hs]
          simpa using ih2 i (by simpa using hi)
    | succ φ =>
      simp only [reads_succ_cons, nph_succ_cons, List.cons_append, List.drop_succ_cons]
      exact ih φ Y (by omega) hY

end GTag

theorem TagSys.step_eq (TS : TagSys) :
    TS.step = GTag.step TS.β (fun b => if b then TS.u else [false]) := by
  funext W
  cases W <;> rfl

end Jones1980
