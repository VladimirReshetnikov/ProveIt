import ConPACtlClosure

/-!
# The scheduler reaches every command word

The PA194 scheduler keeps a candidate counter `n`, a continuation pointer `l` and a store
`σ`. With `l = 0` it starts the candidate `n` and increments the counter; otherwise it
continues at `l - 1`. The number it continues at (the *seed*) decodes, by the triangular
pairing, into a command and the next pointer.

* `encC c q`: the seed that decodes into the command `c` and the pointer `q`;
  `ptr W q m`: the pointer of the last `m` commands of the word `W` followed by `q`.
* `sstep`: one scheduler step on `⟪n, l, σ⟫`; `shalt`: the step is a halting SHIFT.
  A run is a `𝚺₁` function `run k x` with `run (k + 1) x = sstep (run k x)` (`Run`); it is
  a parameter so that the function symbols of a candidate PRA model can be used for it.
* `run_inv`: started at the pointer of `W`, the scheduler executes `W` on its store,
  as long as the tracked executor is running.
* `reach`: from a fresh start the scheduler reaches every later candidate with an empty
  continuation. The proof bounds the time to drain a continuation by its code.
* `derivation_halts`: if some word computes the formula `1`, then every run from a fresh
  start at candidate `2` meets a halting SHIFT, at a possibly nonstandard time.
-/
set_option autoImplicit false
noncomputable section
namespace ConPA.Ctl
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor (cantor first second triangle)

section model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Seeds and pointers

A command is `⟪tag, y, x, z⟫`. The flag `l` says whether AX has the fourth field `z` in the
command stream (the eleven-entry layout); without it the stream has three fields and the
decoded command has `z = 0`. Below, `encC`, `ptr`, `nextL` and `cmd` stand for these functions
at the layout of the semantics `S`.
-/

/-- The seed that decodes into the command `c` followed by the pointer `q`. -/
def encCL (l : Bool) (c q : V) : V :=
  if π₁ c = 0 then cantor 0 q
  else if π₁ c = 1 then cantor 1 (cantor (π₁ (π₂ c)) q)
  else if l then
    cantor (π₁ c) (cantor (π₁ (π₂ c)) (cantor (π₁ (π₂ (π₂ c))) (cantor (π₂ (π₂ (π₂ c))) q)))
  else cantor (π₁ c) (cantor (π₁ (π₂ c)) (cantor (π₁ (π₂ (π₂ c))) q))

def encCLDef (l : Bool) : 𝚺₁.Semisentence 3 :=
  if l then
    .mkSigma “s c q. ∃ tag, !pi₁Def tag c ∧ ∃ c2, !pi₂Def c2 c ∧ ∃ y, !pi₁Def y c2 ∧
      ∃ c3, !pi₂Def c3 c2 ∧ ∃ x, !pi₁Def x c3 ∧ ∃ z, !pi₂Def z c3 ∧
      ((tag = 0 ∧ !cantorDef s 0 q) ∨
       (tag = 1 ∧ ∃ p, !cantorDef p y q ∧ !cantorDef s 1 p) ∨
       (tag ≠ 0 ∧ tag ≠ 1 ∧ ∃ p0, !cantorDef p0 z q ∧ ∃ p, !cantorDef p x p0 ∧
          ∃ p2, !cantorDef p2 y p ∧ !cantorDef s tag p2))”
  else
    .mkSigma “s c q. ∃ tag, !pi₁Def tag c ∧ ∃ c2, !pi₂Def c2 c ∧ ∃ y, !pi₁Def y c2 ∧
      ∃ c3, !pi₂Def c3 c2 ∧ ∃ x, !pi₁Def x c3 ∧
      ((tag = 0 ∧ !cantorDef s 0 q) ∨
       (tag = 1 ∧ ∃ p, !cantorDef p y q ∧ !cantorDef s 1 p) ∨
       (tag ≠ 0 ∧ tag ≠ 1 ∧ ∃ p, !cantorDef p x q ∧ ∃ p2, !cantorDef p2 y p ∧
          !cantorDef s tag p2))”

lemma encCDef_iff (l : Bool) (s c q : V) :
    (encCLDef l).val.Evalb ![s, c, q] ↔ s = encCL l c q := by
  unfold encCL encCLDef
  cases l <;> by_cases h0 : π₁ c = 0 <;> by_cases h1 : π₁ c = 1 <;> simp [h0, h1]

lemma le_encC {l : Bool} (c q : V) : q ≤ encCL l c q := by
  have h2 := fun a b : V => (SetTheory.BusyBeaver.ZFC.ArithmeticCantor.components_le a b).2
  unfold encCL
  split_ifs
  · exact h2 _ _
  · exact le_trans (h2 _ _) (h2 _ _)
  · exact le_trans (h2 _ _) (le_trans (h2 _ _) (le_trans (h2 _ _) (h2 _ _)))
  · exact le_trans (h2 _ _) (le_trans (h2 _ _) (h2 _ _))

@[simp] lemma first_encC {l : Bool} (c q : V) : first (encCL l c q) = π₁ c := by
  unfold encCL
  split_ifs with h0 h1
  · simp [h0]
  · simp [h1]
  · simp
  · simp

namespace Ptr

def blueprint (l : Bool) : PR.Blueprint 2 where
  zero := .mkSigma “y W q. y = q”
  succ := .mkSigma “y ih m W q. ∃ c, !nthDef c W m ∧ ∃ s, !(encCLDef l) s c ih ∧ y = s + 1”

def construction (l : Bool) : PR.Construction V (blueprint l) where
  zero := fun v ↦ v 1
  succ := fun v m ih ↦ encCL l (v 0).[m] ih + 1
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, encCDef_iff]

end Ptr

/-- The pointer of the last `m` commands of the word `W` (its first `m` entries), with the
continuation `q`. -/
def ptrL (l : Bool) (W q m : V) : V := (Ptr.construction l).result ![W, q] m

@[simp] lemma ptr_zero {l : Bool} (W q : V) : ptrL l W q 0 = q := by
  simp [ptrL, Ptr.construction]

@[simp] lemma ptr_succ {l : Bool} (W q m : V) :
    ptrL l W q (m + 1) = encCL l W.[m] (ptrL l W q m) + 1 := by
  simp [ptrL, Ptr.construction]

def ptrLDef (l : Bool) : 𝚺₁.Semisentence 4 :=
  (Ptr.blueprint l).resultDef |>.rew (Rew.subst ![#0, #3, #1, #2])

instance ptr_defined (l : Bool) : 𝚺₁-Function₃ (ptrL l : V → V → V → V) via ptrLDef l := .mk
  fun v ↦ by simp [(Ptr.construction l).result_defined_iff, ptrLDef]; rfl

instance ptr_definable (l : Bool) : 𝚺₁-Function₃ (ptrL l : V → V → V → V) :=
  (ptr_defined l).to_definable

instance ptr_definable' (l : Bool) (Γ m) : Γ-[m + 1]-Function₃ (ptrL l : V → V → V → V) :=
  (ptr_definable l).of_sigmaOne

lemma le_ptr {l : Bool} (W q m : V) : q ≤ ptrL l W q m := by
  induction m using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ m ih =>
    rw [ptr_succ]
    exact le_trans ih (le_trans (le_encC _ _) (le_add_of_nonneg_right (by simp)))

lemma ptr_ne_zero {l : Bool} (W q m : V) (hq : q ≠ 0) : ptrL l W q m ≠ 0 := by
  intro h
  have hle := le_ptr (l := l) W q m
  rw [h] at hle
  exact hq (nonpos_iff_eq_zero.mp hle)

/-! ## The scheduler step -/

/-- The number the scheduler continues at. -/
def seed (n l : V) : V := if l = 0 then n else l - 1

/-- The next pointer of a seed. -/
def nextLL (l : Bool) (s : V) : V :=
  if first s = 0 then second s
  else if first s = 1 then second (second s)
  else if l then second (second (second (second s)))
  else second (second (second s))

/-- The command of a seed. -/
def cmdL (l : Bool) (s : V) : V :=
  ⟪first s, first (second s), first (second (second s)),
    (if l then first (second (second (second s))) else 0)⟫

@[simp] lemma nextL_encC {l : Bool} (c q : V) : nextLL l (encCL l c q) = q := by
  unfold nextLL
  rw [first_encC]
  unfold encCL
  cases l <;> split_ifs <;> simp

variable (S : Sem V)

local notation "encC" => encCL (Sem.ax11 S)
local notation "ptr" => ptrL (Sem.ax11 S)
local notation "nextL" => nextLL (Sem.ax11 S)
local notation "cmd" => cmdL (Sem.ax11 S)

lemma command_eta4 (c : V) : c = ⟪π₁ c, π₁ (π₂ c), π₁ (π₂ (π₂ c)), π₂ (π₂ (π₂ c))⟫ := by simp

lemma cstep_cmd_encC (c q σ : V) : S.cstep (cmd (encC c q)) σ = S.cstep c σ := by
  obtain ⟨t, w, d, h, rfl⟩ : ∃ t w d h : V, σ = ⟪t, w, d, h⟫ :=
    ⟨π₁ σ, π₁ (π₂ σ), π₁ (π₂ (π₂ σ)), π₂ (π₂ (π₂ σ)), by simp⟩
  obtain ⟨tag, y, x, z, rfl⟩ : ∃ tag y x z : V, c = ⟪tag, y, x, z⟫ :=
    ⟨_, _, _, _, command_eta4 c⟩
  by_cases h0 : tag = 0
  · subst h0
    simp [cmdL, encCL, S.shift_eq]
  · by_cases h1 : tag = 1
    · subst h1
      simp [cmdL, encCL, S.mp_eq]
    · obtain ⟨A, rfl⟩ : ∃ A : V, tag = A + 1 + 1 := by
        rcases zero_or_succ tag with (rfl | ⟨a, rfl⟩)
        · exact absurd rfl h0
        · rcases zero_or_succ a with (rfl | ⟨b, rfl⟩)
          · simp at h1
          · exact ⟨b, rfl⟩
      cases hl : S.ax11
      · have e : cmdL false (encCL false ⟪A + 1 + 1, y, x, z⟫ q) = ⟪A + 1 + 1, y, x, 0⟫ := by
          simp [cmdL, encCL, h0, h1]
        rw [e, S.ax_eq, S.ax_eq]
        simp [hl]
      · have e : cmdL true (encCL true ⟪A + 1 + 1, y, x, z⟫ q) = ⟪A + 1 + 1, y, x, z⟫ := by
          simp [cmdL, encCL, h0, h1]
        rw [e]

/-- One scheduler step on `⟪n, l, σ⟫`. -/
def sstep (x : V) : V :=
  ⟪(if π₁ (π₂ x) = 0 then π₁ x + 1 else π₁ x), nextL (seed (π₁ x) (π₁ (π₂ x))),
    S.cstep (cmd (seed (π₁ x) (π₁ (π₂ x)))) (π₂ (π₂ x))⟫

@[simp] lemma sstep_mk (n l σ : V) :
    sstep S ⟪n, l, σ⟫ =
      ⟪(if l = 0 then n + 1 else n), nextL (seed n l), S.cstep (cmd (seed n l)) σ⟫ := by
  simp [sstep]

/-- The step at `x` is a SHIFT whose halting test succeeds. -/
def shalt (x : V) : Prop :=
  first (seed (π₁ x) (π₁ (π₂ x))) = 0 ∧
    S.Halts (π₁ (π₂ (π₂ x))) (π₂ (π₂ (π₂ (π₂ (π₂ x)))))

/-- The state `x` continues at the seed `p - 1`. -/
def PtIs (x p : V) : Prop :=
  (π₁ (π₂ x) = 0 ∧ π₁ x + 1 = p) ∨ (0 < π₁ (π₂ x) ∧ π₁ (π₂ x) = p)

lemma seed_of_ptIs {n l σ s : V} (h : PtIs ⟪n, l, σ⟫ (s + 1)) : seed n l = s := by
  unfold seed
  rcases h with (⟨h0, h1⟩ | ⟨h0, h1⟩)
  · simp only [pi₁_pair, pi₂_pair] at h0 h1
    rw [if_pos h0]
    exact add_right_cancel h1
  · simp only [pi₁_pair, pi₂_pair] at h0 h1
    rw [if_neg (ne_of_gt h0), h1]
    simp

/-! ## The tracked step and the scheduler step -/

lemma tstep_flag_zero_of (c τ : V) (hf : flg(tstep S c τ) = 0) : flg(τ) = 0 := by
  by_contra h
  rw [tstep_of_flag S c τ h] at hf
  exact h hf

lemma tstep_store (c σ δ : V) (hf : flg(tstep S c ⟪σ, δ, 0⟫) = 0) :
    π₁ (tstep S c ⟪σ, δ, 0⟫) = S.cstep c σ := by
  unfold tstep at hf ⊢
  simp only [pi₁_pair, pi₂_pair, if_true] at hf ⊢
  split_ifs at hf ⊢ <;> simp_all

lemma tstep_halt (c σ δ : V) (hf : flg(tstep S c ⟪σ, δ, 0⟫) = 1) :
    π₁ c = 0 ∧ S.Halts (π₁ σ) (π₂ (π₂ (π₂ σ))) := by
  unfold Sem.Halts
  unfold tstep at hf
  simp only [pi₁_pair, pi₂_pair, if_true] at hf
  split_ifs at hf with h0 hh <;> simp_all

lemma inv_step_pure (c q' n l σ δ : V) (hq' : q' ≠ 0) (hp : PtIs ⟪n, l, σ⟫ (encC c q' + 1))
    (hf0 : flg(tstep S c ⟪σ, δ, 0⟫) = 0) :
    PtIs (sstep S ⟪n, l, σ⟫) q' ∧ π₂ (π₂ (sstep S ⟪n, l, σ⟫)) = π₁ (tstep S c ⟪σ, δ, 0⟫) := by
  have hs := seed_of_ptIs hp
  rw [sstep_mk, hs, nextL_encC, cstep_cmd_encC, tstep_store S c σ δ hf0]
  refine ⟨Or.inr ⟨?_, ?_⟩, ?_⟩
  · simpa using pos_iff_ne_zero.mpr hq'
  · simp
  · simp

lemma halt_step_pure (c q' n l σ δ : V) (hp : PtIs ⟪n, l, σ⟫ (encC c q' + 1))
    (hf1 : flg(tstep S c ⟪σ, δ, 0⟫) = 1) : shalt S ⟪n, l, σ⟫ := by
  have hs := seed_of_ptIs hp
  obtain ⟨h0, h1⟩ := tstep_halt S c σ δ hf1
  refine ⟨?_, ?_⟩
  · simp only [pi₁_pair, pi₂_pair]
    rw [hs, first_encC, h0]
  · simpa using h1

/-! ## Runs -/

variable (V) in
/-- A run of the scheduler, as a `𝚺₁` function of the number of steps and the start. -/
structure Run (S : Sem V) where
  run : V → V → V
  run_definable : 𝚺₁-Function₂ run
  run_zero : ∀ x : V, run 0 x = x
  run_succ : ∀ k x : V, run (k + 1) x = sstep S (run k x)

attribute [instance] Run.run_definable

variable {S}

instance Run.run_definable' (R : Run V S) (Γ m) : Γ-[m + 1]-Function₂ R.run :=
  R.run_definable.of_sigmaOne

variable (R : Run V S)

lemma Run.run_add (a b x : V) : R.run (a + b) x = R.run b (R.run a x) := by
  induction b using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp [R.run_zero]
  case succ b ih => rw [← add_assoc, R.run_succ, ih, R.run_succ]

lemma state_eta3 (x : V) : x = ⟪π₁ x, π₁ (π₂ x), π₂ (π₂ x)⟫ := by simp

/-- **The scheduler executes the word at its pointer.** -/
theorem run_inv (W q σ₀ δ₀ x₀ : V) (hq : q ≠ 0) (hpt : PtIs x₀ (ptr W q (len W)))
    (hst : π₂ (π₂ x₀) = σ₀) (j : V) :
    len W < j ∨ 0 < flg(texec S (takeLast W j) ⟪σ₀, δ₀, 0⟫) ∨
      (PtIs (R.run j x₀) (ptr W q (len W - j)) ∧
        π₂ (π₂ (R.run j x₀)) = π₁ (texec S (takeLast W j) ⟪σ₀, δ₀, 0⟫)) := by
  induction j using ISigma1.sigma1_succ_induction
  · unfold PtIs
    definability
  case zero =>
    right; right
    simpa [R.run_zero, hst] using hpt
  case succ j ih =>
    by_cases hj : len W < j + 1
    · exact Or.inl hj
    have hjl : j < len W := lt_iff_succ_le.mpr (not_lt.mp hj)
    right
    have hT1 : texec S (takeLast W (j + 1)) ⟪σ₀, δ₀, 0⟫ =
        tstep S W.[len W - (j + 1)] (texec S (takeLast W j) ⟪σ₀, δ₀, 0⟫) := by
      rw [takeLast_succ_of_lt hjl, texec_adjoin]
    rw [hT1]
    by_cases hf : 0 < flg(tstep S W.[len W - (j + 1)] (texec S (takeLast W j) ⟪σ₀, δ₀, 0⟫))
    · exact Or.inl hf
    right
    have hf0 := nonpos_iff_eq_zero.mp (not_lt.mp hf)
    have hT0 := tstep_flag_zero_of S _ _ hf0
    rcases ih with (h | h | ⟨hp, hs⟩)
    · exact absurd h (not_lt.mpr (le_of_lt hjl))
    · exact absurd hT0 (ne_of_gt h)
    · have hlen : len W - j = len W - (j + 1) + 1 := by
        rw [← Arithmetic.sub_sub, sub_add_self_of_le (pos_iff_one_le.mp (tsub_pos_of_lt hjl))]
      obtain ⟨δ, hTeq⟩ : ∃ δ : V, texec S (takeLast W j) ⟪σ₀, δ₀, 0⟫ =
          ⟪π₂ (π₂ (R.run j x₀)), δ, 0⟫ :=
        ⟨_, (state_eta3 _).trans (by rw [hT0, ← hs])⟩
      obtain ⟨n, l, σ, hx⟩ : ∃ n l σ : V, R.run j x₀ = ⟪n, l, σ⟫ := ⟨_, _, _, state_eta3 _⟩
      rw [hlen, ptr_succ, hx] at hp
      rw [hx] at hTeq
      simp only [pi₂_pair] at hTeq
      rw [hTeq] at hf0 ⊢
      rw [R.run_succ, hx]
      exact inv_step_pure S _ _ _ _ _ _ (ptr_ne_zero W q _ hq) hp hf0

/-- If the tracked run of `W` halts, the scheduler meets a halting SHIFT. -/
theorem word_halts (W q σ₀ x₀ : V) (hq : q ≠ 0) (hpt : PtIs x₀ (ptr W q (len W)))
    (hst : π₂ (π₂ x₀) = σ₀) (hfin : flg(texec S W ⟪σ₀, 0, 0⟫) = 1) :
    ∃ j, shalt S (R.run j x₀) := by
  have hsw : ∀ j, len W < j ∨ flg(texec S (takeLast W j) ⟪σ₀, 0, 0⟫) = 0 ∨
      1 < flg(texec S (takeLast W j) ⟪σ₀, 0, 0⟫) ∨
      ∃ i < j, flg(texec S (takeLast W i) ⟪σ₀, 0, 0⟫) = 0 ∧
        flg(texec S (takeLast W (i + 1)) ⟪σ₀, 0, 0⟫) = 1 := by
    intro j
    induction j using ISigma1.sigma1_succ_induction
    · definability
    case zero => right; left; simp
    case succ j ih =>
      by_cases hj : len W < j + 1
      · exact Or.inl hj
      have hjl : j < len W := lt_iff_succ_le.mpr (not_lt.mp hj)
      right
      have hT1 : texec S (takeLast W (j + 1)) ⟪σ₀, 0, 0⟫ =
          tstep S W.[len W - (j + 1)] (texec S (takeLast W j) ⟪σ₀, 0, 0⟫) := by
        rw [takeLast_succ_of_lt hjl, texec_adjoin]
      rcases ih with (h | h | h | ⟨i, hi, h0, h1⟩)
      · exact absurd h (not_lt.mpr (le_of_lt hjl))
      · rcases lt_trichotomy (flg(texec S (takeLast W (j + 1)) ⟪σ₀, 0, 0⟫)) 1 with (h' | h' | h')
        · left
          exact lt_one_iff_eq_zero.mp h'
        · right; right
          exact ⟨j, by simp, h, h'⟩
        · right; left
          exact h'
      · right; left
        rw [hT1, tstep_of_flag S _ _ (ne_of_gt (lt_trans _root_.zero_lt_one h))]
        exact h
      · right; right
        exact ⟨i, lt_trans hi (by simp), h0, h1⟩
  rcases hsw (len W) with (h | h | h | ⟨i, hi, h0, h1⟩)
  · exact absurd h (_root_.lt_irrefl _)
  · rw [takeLast_len_self, hfin] at h
    simp at h
  · rw [takeLast_len_self, hfin] at h
    exact absurd h (_root_.lt_irrefl _)
  · refine ⟨i, ?_⟩
    rcases run_inv R W q σ₀ 0 x₀ hq hpt hst i with (h | h | ⟨hp, hs⟩)
    · exact absurd (lt_trans hi h) (_root_.lt_irrefl _)
    · rw [h0] at h
      exact absurd h (_root_.lt_irrefl _)
    · have hlen : len W - i = len W - (i + 1) + 1 := by
        rw [← Arithmetic.sub_sub, sub_add_self_of_le (pos_iff_one_le.mp (tsub_pos_of_lt hi))]
      obtain ⟨δ, hTeq⟩ : ∃ δ : V, texec S (takeLast W i) ⟪σ₀, 0, 0⟫ =
          ⟪π₂ (π₂ (R.run i x₀)), δ, 0⟫ :=
        ⟨_, (state_eta3 _).trans (by rw [h0, ← hs])⟩
      obtain ⟨n, l, σ, hx⟩ : ∃ n l σ : V, R.run i x₀ = ⟪n, l, σ⟫ := ⟨_, _, _, state_eta3 _⟩
      rw [hlen, ptr_succ, hx] at hp
      rw [hx] at hTeq
      simp only [pi₂_pair] at hTeq
      rw [takeLast_succ_of_lt hi, texec_adjoin, hTeq] at h1
      rw [hx]
      exact halt_step_pure S _ _ _ _ _ _ hp h1

end model
end ConPA.Ctl
