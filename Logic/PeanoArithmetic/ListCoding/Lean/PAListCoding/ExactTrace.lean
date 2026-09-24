import PAListCoding.BoundedDioph

/-!
# Exact iteration and Goedel-beta trace coding

Exact iteration of a binary relation on `ℕ`, its extensional semantics as a
finite sequence of states, and the coding of such a sequence by Gödel's beta
function (`BetaTrace`).  These generic facts are used by the Diophantine
closure of exact iteration (`IterationDioph`) and by the tetration
certificate (`TetrationDiophantine`).  They are kept apart from
`TetrationDiophantine` so that users of exact iteration do not import its
arithmetic-foundation dependencies.
-/

namespace PAListCoding

/-- Exact iteration of a binary relation.  The successor clause exposes the
last transition; this orientation makes induction on a completed trace
especially convenient. -/
def ExactIter (R : ℕ → ℕ → Prop) : ℕ → ℕ → ℕ → Prop
  | 0, x, y => x = y
  | h + 1, x, z => ∃ y, ExactIter R h x y ∧ R y z

@[simp] theorem exactIter_zero (R : ℕ → ℕ → Prop) (x y : ℕ) :
    ExactIter R 0 x y ↔ x = y := Iff.rfl

@[simp] theorem exactIter_succ (R : ℕ → ℕ → Prop) (h x z : ℕ) :
    ExactIter R (h + 1) x z ↔ ∃ y, ExactIter R h x y ∧ R y z := Iff.rfl

/-- Extensional semantics for exact iteration: a run of length `h` is a
function containing its `h+1` states and satisfying every adjacent step. -/
theorem exactIter_iff_exists_sequence (R : ℕ → ℕ → Prop) (h x y : ℕ) :
    ExactIter R h x y ↔
      ∃ f : ℕ → ℕ,
        f 0 = x ∧ f h = y ∧ ∀ i, i < h → R (f i) (f (i + 1)) := by
  induction h generalizing x y with
  | zero =>
      constructor
      · intro hxy
        exact ⟨fun _ => x, rfl, hxy, by omega⟩
      · rintro ⟨f, hf0, hfy, _hstep⟩
        exact hf0.symm.trans hfy
  | succ h ih =>
      rw [exactIter_succ]
      constructor
      · rintro ⟨middle, hprefix, hlast⟩
        obtain ⟨f, hf0, hfh, hfstep⟩ := (ih x middle).mp hprefix
        let g : ℕ → ℕ := fun i => if i = h + 1 then y else f i
        refine ⟨g, ?_, ?_, ?_⟩
        · simp [g, hf0]
        · simp [g]
        · intro i hi
          have hile : i ≤ h := by omega
          rcases Nat.lt_or_eq_of_le hile with hil | rfl
          · have hi_ne : i ≠ h + 1 := by omega
            have his_ne : i + 1 ≠ h + 1 := by omega
            have hi_h : i ≠ h := Nat.ne_of_lt hil
            simpa [g, hi_ne, his_ne, hi_h] using hfstep i hil
          · simpa [g, hfh] using hlast
      · rintro ⟨f, hf0, hfend, hfstep⟩
        refine ⟨f h, ?_, ?_⟩
        · apply (ih x (f h)).mpr
          exact ⟨f, hf0, rfl, fun i hi => hfstep i (by omega)⟩
        · simpa [hfend] using hfstep h (Nat.lt_succ_self h)

/-! ## Arithmetic coding of finite traces

`BoundedDioph.BetaEntry` uses Goedel's beta moduli.  Unlike a dependent
vector, the pair `(code,step)` is a fixed finite tuple of natural numbers and
can therefore become part of one Diophantine certificate.  The bound still
occurs in the universal adjacency clause; eliminating precisely that clause
is the substantive bounded-universal theorem developed in `BoundedDioph`.
-/

/-- A beta-coded exact trace for a binary relation. -/
def BetaTrace (R : ℕ → ℕ → Prop)
    (code step height start finish : ℕ) : Prop :=
  BoundedDioph.BetaEntry code step 0 start ∧
  BoundedDioph.BetaEntry code step height finish ∧
  ∀ i, i < height →
    ∃ current next,
      BoundedDioph.BetaEntry code step i current ∧
      BoundedDioph.BetaEntry code step (i + 1) next ∧
      R current next

/-- Goedel-beta codes are semantically complete for finite exact traces.  The
forward direction applies finite CRT to the sequence supplied above; the
reverse direction decodes each position by remainder and uses lookup
functionality to recover every transition. -/
theorem exactIter_iff_exists_betaTrace (R : ℕ → ℕ → Prop) (height start finish : ℕ) :
    ExactIter R height start finish ↔
      ∃ code step, BetaTrace R code step height start finish := by
  constructor
  · intro hiter
    obtain ⟨f, hf0, hfh, hfstep⟩ :=
      (exactIter_iff_exists_sequence R height start finish).mp hiter
    obtain ⟨code, step, hentry⟩ :=
      BoundedDioph.exists_beta_prefix f (height + 1)
    refine ⟨code, step, ?_, ?_, ?_⟩
    · simpa [hf0] using hentry 0 (by omega)
    · simpa [hfh] using hentry height (by omega)
    · intro i hi
      exact ⟨f i, f (i + 1), hentry i (by omega),
        hentry (i + 1) (by omega), hfstep i hi⟩
  · rintro ⟨code, step, hstart, hfinish, hsteps⟩
    apply (exactIter_iff_exists_sequence R height start finish).mpr
    let f : ℕ → ℕ := fun i => code % BoundedDioph.BetaModulus step i
    refine ⟨f, ?_, ?_, ?_⟩
    · simpa [f] using hstart.1
    · simpa [f] using hfinish.1
    · intro i hi
      obtain ⟨current, next, hcurrent, hnext, hrel⟩ := hsteps i hi
      have hc : f i = current := by simpa [f] using hcurrent.1
      have hn : f (i + 1) = next := by simpa [f] using hnext.1
      simpa [hc, hn] using hrel

end PAListCoding
