import Std
import Init.Data.Rat.Lemmas

/-!
# A small kernel for approximation arguments

This file contains ordinary Lean theorems.  It is **not** an object-language
`Prf PRAAx` development.  The accompanying OBJECT_LANGUAGE_PLAN.md specifies
the finite arithmetic statements and the existing ProveIt interfaces needed
for that second step.

No Mathlib dependency, `sorry`, or new axiom is used.  `positive_transfer` is
axiom-free; the standard Rat lemmas used in the arithmetic proofs carry Lean's
standard metatheoretic axioms, including Classical.choice.  See Audit.lean.
The public theorems cover positive-formula transfer, a correct executable
finite-domain evaluator, and the complete perturbed-contraction error schedule.
-/

namespace IPRAAbstractAnalysis

universe u v w

abbrev Env (X : Type u) := Nat → X

def push {X : Type u} (x : X) (ρ : Env X) : Env X
  | 0 => x
  | n + 1 => ρ n

def Related {X : Type u} {Y : Type v} (R : X → Y → Prop)
    (ρ : Env X) (σ : Env Y) : Prop := ∀ n, R (ρ n) (σ n)

theorem related_push {X : Type u} {Y : Type v} {R : X → Y → Prop}
    {ρ : Env X} {σ : Env Y} {x : X} {y : Y}
    (hxy : R x y) (hρσ : Related R ρ σ) :
    Related R (push x ρ) (push y σ) := by
  intro n
  cases n with
  | zero => exact hxy
  | succ n => exact hρσ n

/-- Positive first-order syntax. Atomic expressions include their terms.
The ambient domain is the selected bounded sort. -/
inductive PosFormula (Atom : Type u) : Type u where
  | atom : Atom → PosFormula Atom
  | top : PosFormula Atom
  | bot : PosFormula Atom
  | conj : PosFormula Atom → PosFormula Atom → PosFormula Atom
  | disj : PosFormula Atom → PosFormula Atom → PosFormula Atom
  | all : PosFormula Atom → PosFormula Atom
  | ex : PosFormula Atom → PosFormula Atom

def Holds {Atom : Type u} {X : Type v}
    (atom : Atom → Env X → Prop) : PosFormula Atom → Env X → Prop
  | .atom a, ρ => atom a ρ
  | .top, _ => True
  | .bot, _ => False
  | .conj φ ψ, ρ => Holds atom φ ρ ∧ Holds atom ψ ρ
  | .disj φ ψ, ρ => Holds atom φ ρ ∨ Holds atom ψ ρ
  | .all φ, ρ => ∀ x : X, Holds atom φ (push x ρ)
  | .ex φ, ρ => ∃ x : X, Holds atom φ (push x ρ)

/-- A relation with selected forth and back witnesses preserves every positive
formula whenever its atomic assertions are preserved.  For finite metric nets,
`forth` is a net selector and `back` is inclusion.  Atomic assertions may use
different margins on the two sides; no additional loss is introduced by the
logical connectives or quantifier nesting. -/
theorem positive_transfer {Atom : Type u} {X : Type v} {Y : Type w}
    (R : X → Y → Prop) (forth : X → Y) (back : Y → X)
    (hforth : ∀ x, R x (forth x)) (hback : ∀ y, R (back y) y)
    (source : Atom → Env X → Prop) (target : Atom → Env Y → Prop)
    (atomic : ∀ a ρ σ, Related R ρ σ → source a ρ → target a σ)
    (φ : PosFormula Atom) :
    ∀ ρ σ, Related R ρ σ → Holds source φ ρ → Holds target φ σ := by
  induction φ with
  | atom a =>
      intro ρ σ hρσ h
      exact atomic a ρ σ hρσ h
  | top =>
      intro _ _ _ _
      exact True.intro
  | bot =>
      intro _ _ _ h
      exact False.elim h
  | conj φ ψ ihφ ihψ =>
      intro ρ σ hρσ h
      exact ⟨ihφ ρ σ hρσ h.1, ihψ ρ σ hρσ h.2⟩
  | disj φ ψ ihφ ihψ =>
      intro ρ σ hρσ h
      cases h with
      | inl hφ => exact Or.inl (ihφ ρ σ hρσ hφ)
      | inr hψ => exact Or.inr (ihψ ρ σ hρσ hψ)
  | all φ ih =>
      intro ρ σ hρσ h y
      exact ih (push (back y) ρ) (push y σ)
        (related_push (hback y) hρσ) (h (back y))
  | ex φ ih =>
      intro ρ σ hρσ h
      obtain ⟨x, hx⟩ := h
      exact ⟨forth x, ih (push x ρ) (push (forth x) σ)
        (related_push (hforth x) hρσ) hx⟩

/-- Primitive recursion for finite universal quantification, including n = 0. -/
def allFin : (n : Nat) → (Fin n → Bool) → Bool
  | 0, _ => true
  | n + 1, f => f 0 && allFin n (fun i => f i.succ)

/-- Primitive recursion for finite existential quantification, including n = 0. -/
def anyFin : (n : Nat) → (Fin n → Bool) → Bool
  | 0, _ => false
  | n + 1, f => f 0 || anyFin n (fun i => f i.succ)

theorem allFin_true (n : Nat) : ∀ f : Fin n → Bool,
    allFin n f = true ↔ ∀ i, f i = true := by
  induction n with
  | zero =>
      intro f
      constructor
      · intro _ i
        exact Fin.elim0 i
      · intro _
        rfl
  | succ n ih =>
      intro f
      rw [allFin, Bool.and_eq_true, ih]
      constructor
      · intro h i
        exact Fin.cases h.1 h.2 i
      · intro h
        exact ⟨h 0, fun i => h i.succ⟩

theorem anyFin_true (n : Nat) : ∀ f : Fin n → Bool,
    anyFin n f = true ↔ ∃ i, f i = true := by
  induction n with
  | zero =>
      intro f
      constructor
      · intro h
        cases h
      · intro h
        obtain ⟨i, _⟩ := h
        exact Fin.elim0 i
  | succ n ih =>
      intro f
      rw [anyFin, Bool.or_eq_true, ih]
      constructor
      · intro h
        cases h with
        | inl h => exact ⟨0, h⟩
        | inr h =>
            obtain ⟨i, hi⟩ := h
            exact ⟨i.succ, hi⟩
      · intro h
        obtain ⟨i, hi⟩ := h
        exact Fin.cases (fun h0 => Or.inl h0)
          (fun j hj => Or.inr ⟨j, hj⟩) i hi

/-- Evaluate a fixed formula over a finite domain.  This is a structural
interpreter for this syntax, not a universal evaluator for PR programs. -/
def eval {Atom : Type u} (n : Nat) (atom : Atom → Env (Fin n) → Bool) :
    PosFormula Atom → Env (Fin n) → Bool
  | .atom a, ρ => atom a ρ
  | .top, _ => true
  | .bot, _ => false
  | .conj φ ψ, ρ => eval n atom φ ρ && eval n atom ψ ρ
  | .disj φ ψ, ρ => eval n atom φ ρ || eval n atom ψ ρ
  | .all φ, ρ => allFin n (fun x => eval n atom φ (push x ρ))
  | .ex φ, ρ => anyFin n (fun x => eval n atom φ (push x ρ))

theorem eval_correct {Atom : Type u} (n : Nat)
    (atom : Atom → Env (Fin n) → Bool) (φ : PosFormula Atom) :
    ∀ ρ, eval n atom φ ρ = true ↔
      Holds (fun a σ => atom a σ = true) φ ρ := by
  induction φ with
  | atom a => intro ρ; rfl
  | top => intro ρ; simp [eval, Holds]
  | bot => intro ρ; simp [eval, Holds]
  | conj φ ψ ihφ ihψ =>
      intro ρ
      simp only [eval, Bool.and_eq_true, ihφ, ihψ, Holds]
  | disj φ ψ ihφ ihψ =>
      intro ρ
      simp only [eval, Bool.or_eq_true, ihφ, ihψ, Holds]
  | all φ ih =>
      intro ρ
      simp only [eval, allFin_true, ih, Holds]
  | ex φ ih =>
      intro ρ
      simp only [eval, anyFin_true, ih, Holds]

section RationalError

/-- The algebraic step behind the perturbation invariant. -/
theorem error_step_identity (q R E ε : Rat) (n : Nat) :
    q * (q ^ n * R + E) + ε =
      q ^ (n + 1) * R + (q * E + ε) := by
  rw [Rat.mul_add, Rat.add_assoc, Rat.pow_succ]
  rw [← Rat.mul_assoc, Rat.mul_comm q (q ^ n)]

/-- A stationary error reserve is preserved when each perturbation is at most
the unused fraction of the reserve. -/
theorem stationary_error {q E ε : Rat} (hε : ε ≤ (1 - q) * E) :
    q * E + ε ≤ E := by
  have h : q * E + ε ≤ q * E + (1 - q) * E :=
    Rat.add_le_add_left.mpr hε
  have eq : q * E + (1 - q) * E = E := by
    rw [← Rat.add_mul, Rat.add_comm q (1 - q), Rat.sub_add_cancel, Rat.one_mul]
  rw [eq] at h
  exact h

/-- If x(n+1) ≤ q*x(n)+ε, then x(n) ≤ q^n*R+E when x(0)≤R,
q≥0, E≥0 and q*E+ε≤E.  A genuine contraction additionally has q<1;
that hypothesis is needed for selecting a convergence clock, not for this
finite arithmetic invariant. -/
theorem perturbed_contraction {q R E ε : Rat} (x : Nat → Rat)
    (hq : 0 ≤ q) (hE : 0 ≤ E) (hreserve : q * E + ε ≤ E)
    (hzero : x 0 ≤ R)
    (hstep : ∀ n, x (n + 1) ≤ q * x n + ε) :
    ∀ n, x n ≤ q ^ n * R + E := by
  intro n
  induction n with
  | zero =>
      simp only [Rat.pow_zero, Rat.one_mul]
      have h : R + 0 ≤ R + E := Rat.add_le_add_left.mpr hE
      rw [Rat.add_zero] at h
      exact Rat.le_trans hzero h
  | succ n ih =>
      have hmul : q * x n ≤ q * (q ^ n * R + E) :=
        Rat.mul_le_mul_of_nonneg_left ih hq
      have hadd : q * x n + ε ≤ q * (q ^ n * R + E) + ε :=
        Rat.add_le_add_right.mpr hmul
      have hlast : q ^ (n + 1) * R + (q * E + ε) ≤ q ^ (n + 1) * R + E :=
        Rat.add_le_add_left.mpr hreserve
      exact Rat.le_trans (Rat.le_trans (hstep n) hadd)
        ((error_step_identity q R E ε n).symm ▸ hlast)

/-- The standard noise assumption ε ≤ (1−q)E gives the same bound. -/
theorem perturbed_contraction_of_noise {q R E ε : Rat} (x : Nat → Rat)
    (hq : 0 ≤ q) (hE : 0 ≤ E) (hε : ε ≤ (1 - q) * E)
    (hzero : x 0 ≤ R) (hstep : ∀ n, x (n + 1) ≤ q * x n + ε) :
    ∀ n, x n ≤ q ^ n * R + E :=
  perturbed_contraction x hq hE (stationary_error hε) hzero hstep

/-- Elementary rational power identity, proved without a library for reals. -/
theorem rat_pow_add (q : Rat) (m n : Nat) : q ^ (m + n) = q ^ m * q ^ n := by
  induction n with
  | zero => simp [Rat.pow_zero]
  | succ n ih =>
      rw [Nat.add_succ, Rat.pow_succ, ih, Rat.pow_succ, Rat.mul_assoc]

theorem rat_pow_mul (q : Rat) (h n : Nat) : q ^ (h * n) = (q ^ h) ^ n := by
  induction n with
  | zero => simp [Rat.pow_zero]
  | succ n ih =>
      rw [Nat.mul_succ, rat_pow_add, ih, Rat.pow_succ]

theorem rat_pow_mono {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ n : Nat, a ^ n ≤ b ^ n := by
  have hb : 0 ≤ b := Rat.le_trans ha hab
  intro n
  induction n with
  | zero => simp only [Rat.pow_zero]; exact Rat.le_refl
  | succ n ih =>
      rw [Rat.pow_succ, Rat.pow_succ]
      exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right ih ha)
        (Rat.mul_le_mul_of_nonneg_left hab (Rat.pow_nonneg hb))

/-- A reciprocal geometric estimate with no logarithm or square root.
Only 0 ≤ δ ≤ 1 is required. -/
theorem reciprocal_decay {δ : Rat} (hδ : 0 ≤ δ) (hδone : δ ≤ 1) :
    ∀ n : Nat, (1 + (n : Rat) * δ) * (1 - δ) ^ n ≤ 1 := by
  have hq : 0 ≤ 1 - δ := by grind
  intro n
  induction n with
  | zero => simp [Rat.pow_zero, Rat.add_zero]
  | succ n ih =>
      have hn : 0 ≤ ((n + 1 : Nat) : Rat) := Rat.natCast_nonneg (a := n + 1)
      have hs : 0 ≤ ((n + 1 : Nat) : Rat) * δ ^ 2 :=
        Rat.mul_nonneg hn (Rat.pow_nonneg hδ)
      have identity :
          (1 - δ) * (1 + ((n + 1 : Nat) : Rat) * δ) +
              ((n + 1 : Nat) : Rat) * δ ^ 2 = 1 + (n : Rat) * δ := by
        simp only [Rat.natCast_add]
        grind
      have factor : (1 - δ) * (1 + ((n + 1 : Nat) : Rat) * δ) ≤
          1 + (n : Rat) * δ := by grind
      have hp : 0 ≤ (1 - δ) ^ n := Rat.pow_nonneg hq
      have bound := Rat.mul_le_mul_of_nonneg_right factor hp
      rw [Rat.pow_succ]
      have rearrange :
          (1 + ((n + 1 : Nat) : Rat) * δ) * ((1 - δ) ^ n * (1 - δ)) =
          ((1 - δ) * (1 + ((n + 1 : Nat) : Rat) * δ)) * (1 - δ) ^ n := by
        grind
      rw [rearrange]
      exact Rat.le_trans bound ih

/-- hδ ≥ 1 makes a block of h steps at least a halving. -/
theorem block_halving {δ : Rat} (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (h : Nat) (hblock : 1 ≤ (h : Rat) * δ) : (1 - δ) ^ h ≤ (1 / 2 : Rat) := by
  have hq : 0 ≤ 1 - δ := by grind
  have hp : 0 ≤ (1 - δ) ^ h := Rat.pow_nonneg hq
  have factor : (2 : Rat) ≤ 1 + (h : Rat) * δ := by grind
  have bound := Rat.mul_le_mul_of_nonneg_right factor hp
  have decay := reciprocal_decay hδ hδone h
  grind

theorem block_decay {δ : Rat} (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (h : Nat) (hblock : 1 ≤ (h : Rat) * δ) (t : Nat) :
    (1 - δ) ^ (h * t) ≤ (1 / 2 : Rat) ^ t := by
  have hq : 0 ≤ 1 - δ := by grind
  rw [rat_pow_mul]
  exact rat_pow_mono (Rat.pow_nonneg hq) (block_halving hδ hδone h hblock) t

/-- A natural amplitude can be absorbed into its own dyadic precision offset. -/
theorem amplitude_absorb : ∀ C : Nat, (C : Rat) * (1 / 2 : Rat) ^ C ≤ 1 := by
  intro C
  induction C with
  | zero => simp only [Rat.pow_zero]; grind
  | succ n ih =>
      cases n with
      | zero => simp only [Rat.pow_zero, Rat.pow_succ]; grind
      | succ n =>
          have hn : 0 ≤ (n : Rat) := Rat.natCast_nonneg (a := n)
          have factor : (((n + 1) + 1 : Nat) : Rat) * (1 / 2 : Rat) ≤
              ((n + 1 : Nat) : Rat) := by
            simp only [Rat.natCast_add]
            grind
          have hp : 0 ≤ (1 / 2 : Rat) ^ (n + 1) := Rat.pow_nonneg (by grind)
          have bound := Rat.mul_le_mul_of_nonneg_right factor hp
          rw [Rat.pow_succ]
          have rearrange :
              (((n + 1) + 1 : Nat) : Rat) * ((1 / 2 : Rat) ^ (n + 1) * (1 / 2)) =
              ((((n + 1) + 1 : Nat) : Rat) * (1 / 2)) * (1 / 2 : Rat) ^ (n + 1) := by
            grind
          rw [rearrange]
          exact Rat.le_trans bound ih

theorem shifted_amplitude (C s : Nat) :
    (C : Rat) * (1 / 2 : Rat) ^ (s + C) ≤ (1 / 2 : Rat) ^ s := by
  have hp : 0 ≤ (1 / 2 : Rat) ^ s := Rat.pow_nonneg (by grind)
  have bound := Rat.mul_le_mul_of_nonneg_right (amplitude_absorb C) hp
  rw [rat_pow_add]
  have rearrange : (C : Rat) * ((1 / 2 : Rat) ^ s * (1 / 2 : Rat) ^ C) =
      ((C : Rat) * (1 / 2 : Rat) ^ C) * (1 / 2 : Rat) ^ s := by grind
  rw [rearrange]
  simpa using bound

/-- The radius term is below 2^(-n-3) at the explicit clock h(n+R+3). -/
theorem radius_at_clock {δ : Rat} (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (h R n : Nat) (hblock : 1 ≤ (h : Rat) * δ) :
    (1 - δ) ^ (h * (n + R + 3)) * (R : Rat) ≤ (1 / 2 : Rat) ^ (n + 3) := by
  have bound := Rat.mul_le_mul_of_nonneg_right
    (block_decay hδ hδone h hblock (n + R + 3)) (Rat.natCast_nonneg (a := R))
  have rearrange : n + R + 3 = (n + 3) + R := by omega
  rw [rearrange] at bound
  have absorb := shifted_amplitude R (n + 3)
  rw [Rat.mul_comm (R : Rat)] at absorb
  rw [rearrange]
  exact Rat.le_trans bound absorb

/-- The complete rational budget for the report's solver.

For k=n+3+C, per-step error is 2λ·2^(-k).  A rational gap δ in [0,1],
an integer block h with hδ≥1, and a cleared precision bound 2λ≤δC give
error at most 2^(-n-2) after N=h(n+R+3) steps.

The theorem concerns a supplied rational error majorant x.  The application
must separately prove that its actual analytic errors are bounded by x.
-/
theorem solver_budget {δ lam : Rat} (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (h C R n : Nat) (hblock : 1 ≤ (h : Rat) * δ)
    (hprecision : 2 * lam ≤ δ * (C : Rat)) (x : Nat → Rat)
    (hzero : x 0 ≤ (R : Rat))
    (hstep : ∀ j, x (j + 1) ≤ (1 - δ) * x j +
      2 * lam * (1 / 2 : Rat) ^ (n + 3 + C)) :
    x (h * (n + R + 3)) ≤ (1 / 2 : Rat) ^ (n + 2) := by
  let E : Rat := (C : Rat) * (1 / 2 : Rat) ^ (n + 3 + C)
  have hq : 0 ≤ 1 - δ := by grind
  have hpow : 0 ≤ (1 / 2 : Rat) ^ (n + 3 + C) := Rat.pow_nonneg (by grind)
  have hE : 0 ≤ E := Rat.mul_nonneg (Rat.natCast_nonneg (a := C)) hpow
  have hp := Rat.mul_le_mul_of_nonneg_right hprecision hpow
  have hnoise : 2 * lam * (1 / 2 : Rat) ^ (n + 3 + C) ≤ (1 - (1 - δ)) * E := by
    dsimp [E]
    grind
  have perturb := perturbed_contraction_of_noise x hq hE hnoise hzero hstep
    (h * (n + R + 3))
  have radius := radius_at_clock hδ hδone h R n hblock
  have reserve : E ≤ (1 / 2 : Rat) ^ (n + 3) := shifted_amplitude C (n + 3)
  have power : (1 / 2 : Rat) ^ (n + 3) =
      (1 / 2 : Rat) ^ (n + 2) * (1 / 2 : Rat) := Rat.pow_succ _ (n + 2)
  grind

end RationalError

end IPRAAbstractAnalysis
