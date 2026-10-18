import ZFCinPA.Instances
import FirstOrder.Fol

set_option autoImplicit false
noncomputable section

/-!
Small raw-form conversion and quotation of closed formulas.

The local variable/form conversion is the recursion in `ZFCinPA.Translation`.
`closeS` and the two generic quotation proofs follow the syntax-only portion of
`ZFCinPA.NativeInterp` (arrival ac89f2e948). Their broad semantic imports are
not required here. The original files remain the attribution sources.

Closing replaces every free variable by the newest bound variable. Thus these
results concern that explicitly closed formula; they assert no equality with
an unclosed quotation, no semantic interpretation, and no R3 consistency result.
-/

namespace LeanProofs.ZFCinPA.RawFormQuotation

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Split a raw De Bruijn variable into bound and free slots at depth `k`. -/
def toVar (k i : Nat) : Semiterm ℒₛₑₜ ℕ k :=
  if h : i < k then #(⟨i, h⟩ : Fin k) else &(i - k)

/-- The literal eight-constructor raw conversion, under a local name. -/
def translate : (k : Nat) → _root_.SetTheory.Form → SetTheorySemiproposition k
  | k, .fMem i j => .rel Language.Mem.mem ![toVar k i, toVar k j]
  | k, .fEq i j  => .rel Language.Eq.eq ![toVar k i, toVar k j]
  | _, .fBot     => ⊥
  | k, .fImp a b => translate k a 🡒 translate k b
  | k, .fAnd a b => translate k a ⋏ translate k b
  | k, .fOr a b  => translate k a ⋎ translate k b
  | k, .fAll a   => ∀⁰ translate (k + 1) a
  | k, .fEx a    => ∃⁰ translate (k + 1) a

/-- Close at positive depth by sending every free variable to `#0`. -/
def closeS {k : ℕ} (φ : SetTheorySemiproposition (k + 1)) : Semisentence ℒₛₑₜ (k + 1) :=
  Rew.rewrite (fun _ ↦ (#0 : Semiterm ℒₛₑₜ Empty (k + 1))) ▹ φ

/-- A named closed formula with `k + 1` bound slots. -/
def closed (k : Nat) (φ : _root_.SetTheory.Form) : Semisentence ℒₛₑₜ (k + 1) :=
  closeS (translate (k + 1) φ)

open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A closed formula's quotation is fixed by the internal free-variable shift. -/
theorem shift_quote_sen {k : ℕ} (σ : Semisentence ℒₛₑₜ k) :
    shift ℒₛₑₜ (⌜σ⌝ : V) = ⌜σ⌝ := by
  rw [LO.FirstOrder.Sentence.quote_def, ← LO.FirstOrder.Semiformula.quote_shift]
  congr 1
  rw [Rewriting.shift, ← TransitiveRewriting.comp_app, Rew.shift_comp_emb]

/-- Quotation has the displayed bound-variable arity in every IΣ1 model. -/
theorem isSemiformula_quote_sen {k : ℕ} (σ : Semisentence ℒₛₑₜ k) :
    IsSemiformula ℒₛₑₜ (k : V) (⌜σ⌝ : V) := by
  rw [LO.FirstOrder.Sentence.quote_def]
  simpa using LO.FirstOrder.Semiformula.quote_isSemiformula (V := V)
    (Rewriting.emb σ : SetTheorySemiproposition k)

/-- The exact semiproposition whose code is used; closure stays explicit. -/
theorem quote_closed (k : Nat) (φ : _root_.SetTheory.Form) :
    (⌜closed k φ⌝ : V) =
      ⌜(Rewriting.emb (closeS (translate (k + 1) φ)) : SetTheorySemiproposition (k + 1))⌝ := rfl

theorem isSemiformula_closed (k : Nat) (φ : _root_.SetTheory.Form) :
    IsSemiformula ℒₛₑₜ ((k + 1 : Nat) : V) (⌜closed k φ⌝ : V) :=
  isSemiformula_quote_sen (closed k φ)

theorem shift_closed (k : Nat) (φ : _root_.SetTheory.Form) :
    shift ℒₛₑₜ (⌜closed k φ⌝ : V) = ⌜closed k φ⌝ :=
  shift_quote_sen (closed k φ)

end LeanProofs.ZFCinPA.RawFormQuotation
