import Foundation.FirstOrder.Arithmetic.HFS.PRF
import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# Two-symbol Turing machines inside models of `𝗜𝚺₁`

For a transition table `T`, given as a list of rows, this file defines the run of the machine
from the blank tape inside an arbitrary model `V` of `𝗜𝚺₁`, and a `Σ₁` sentence `haltDef T h`
of arithmetic that says "the run reaches the state `h`".

A configuration is the number `⟪q, l, r⟫`: the state `q`, the tape to the left of the head as
the binary number `l` (the cell next to the head is the lowest bit), and the tape from the head
rightwards as the binary number `r` (the head reads the lowest bit). The blank initial
configuration in state `0` is the number `0`.

* `step T c` is the next configuration; a configuration to which no row applies is its own
  successor, so a machine that reaches a state without rows stays there.
* `run T t` is the configuration after `t` steps, for `t` in `V`; it is defined with
  Foundation's `PR.Construction`, so `t` may be nonstandard.
* `haltDef_iff`: in every model of `𝗜𝚺₁`, `haltDef T h` holds exactly when some `run T t` has
  the state `h`.

Nothing here refers to a particular machine or to consistency.
-/
set_option autoImplicit false

namespace ConPA.Machine
open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-- A row `q b w d q'` of a table: in state `q` reading `b`, write `w`, move right when `right`
holds and left otherwise, and enter `q'`. -/
structure Row where
  q : ℕ
  b : ℕ
  w : ℕ
  right : Bool
  q' : ℕ

abbrev Table := List Row

section model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The configuration after applying the row `ρ` to the tape halves `l`, `r`. -/
noncomputable def out (ρ : Row) (l r : V) : V :=
  if ρ.right then ⟪(ρ.q' : V), 2 * l + (ρ.w : V), r / 2⟫
  else ⟪(ρ.q' : V), l / 2, 4 * (r / 2) + 2 * (ρ.w : V) + l % 2⟫

/-- One step of the table on a configuration. -/
noncomputable def step : Table → V → V
  | [], c => c
  | ρ :: T, c =>
    if π₁ c = (ρ.q : V) ∧ π₂ (π₂ c) % 2 = (ρ.b : V) then out ρ (π₁ (π₂ c)) (π₂ (π₂ c))
    else step T c

def outDef (ρ : Row) : 𝚺₁.Semisentence 3 :=
  if ρ.right then
    .mkSigma “c' l r. ∃ r2, !divDef r2 r 2 ∧ ∃ lr, !pairDef lr (2 * l + ↑ρ.w) r2 ∧ !pairDef c' ↑ρ.q' lr”
  else
    .mkSigma “c' l r. ∃ l2, !divDef l2 l 2 ∧ ∃ r2, !divDef r2 r 2 ∧ ∃ lb, !remDef lb l 2 ∧
      ∃ lr, !pairDef lr l2 (4 * r2 + 2 * ↑ρ.w + lb) ∧ !pairDef c' ↑ρ.q' lr”

lemma outDef_iff (ρ : Row) (c' l r : V) :
    (outDef ρ).val.Evalb ![c', l, r] ↔ c' = out ρ l r := by
  unfold outDef out
  split <;> simp [numeral_eq_natCast]

def stepDef : Table → 𝚺₁.Semisentence 2
  | [] => .mkSigma “c' c. c' = c”
  | ρ :: T => .mkSigma “c' c. ∃ q, !pi₁Def q c ∧ ∃ lr, !pi₂Def lr c ∧ ∃ l, !pi₁Def l lr ∧
      ∃ r, !pi₂Def r lr ∧ ∃ s, !remDef s r 2 ∧
        ((q = ↑ρ.q ∧ s = ↑ρ.b ∧ !(outDef ρ) c' l r) ∨
          ((q ≠ ↑ρ.q ∨ s ≠ ↑ρ.b) ∧ !(stepDef T) c' c))”

lemma stepDef_iff : ∀ (T : Table) (c' c : V), (stepDef T).val.Evalb ![c', c] ↔ c' = step T c
  | [], c', c => by simp [stepDef, step]
  | ρ :: T, c', c => by
    have ih := stepDef_iff T c' c
    by_cases h : π₁ c = (ρ.q : V) ∧ π₂ (π₂ c) % 2 = (ρ.b : V)
    · simp [stepDef, step, h, outDef_iff, numeral_eq_natCast]
    · simp [stepDef, step, h, ih, numeral_eq_natCast]
      tauto

def blueprint (T : Table) : PR.Blueprint 0 where
  zero := .mkSigma “y. y = 0”
  succ := .mkSigma “y ih n. !(stepDef T) y ih”

noncomputable def construction (T : Table) : PR.Construction V (blueprint T) where
  zero := fun _ ↦ 0
  succ := fun _ _ ih ↦ step T ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, stepDef_iff]

/-- The configuration after `t` steps from the blank tape in state `0`. -/
noncomputable def run (T : Table) (t : V) : V := (construction T).result ![] t

@[simp] lemma run_zero (T : Table) : run T (0 : V) = 0 := by simp [run, construction]

@[simp] lemma run_succ (T : Table) (t : V) : run T (t + 1) = step T (run T t) := by
  simp [run, construction]

/-- "Some configuration of the run has the state `h`." -/
def haltDef (T : Table) (h : ℕ) : 𝚺₁.Semisentence 0 :=
  .mkSigma “∃ t, ∃ c, !(blueprint T).resultDef c t ∧ !pi₁Def ↑h c”

lemma haltDef_iff (T : Table) (h : ℕ) :
    (haltDef T h).val.Evalb (M := V) ![] ↔ ∃ t : V, π₁ (run T t) = (h : V) := by
  simp [haltDef, run, (construction T).result_defined_iff, numeral_eq_natCast, eq_comm]
  refine exists_congr fun t => ?_
  rw [Subsingleton.elim (fun _ : Fin 0 => t) ![]]

end model

/-! ## The standard model -/

/-- Over the natural numbers the run is the iteration of the step function. -/
lemma run_nat (T : Table) (t : ℕ) : run (V := ℕ) T t = (step (V := ℕ) T)^[t] 0 := by
  induction t with
  | zero => simp
  | succ t ih => rw [run_succ, ih, Function.iterate_succ_apply']

/-- The halting sentence is true exactly when the iterated step function over the natural
numbers reaches the state `h`. -/
lemma haltDef_standard (T : Table) (h : ℕ) :
    (haltDef T h).val.Evalb (M := ℕ) ![] ↔ ∃ t : ℕ, π₁ ((step (V := ℕ) T)^[t] 0) = h := by
  rw [haltDef_iff]
  simp [run_nat]

/-- The halting sentence is `Σ₁`. -/
lemma haltDef_sigma_one (T : Table) (h : ℕ) : Hierarchy 𝚺 1 (haltDef T h).val :=
  (haltDef T h).sigma_prop

end ConPA.Machine
