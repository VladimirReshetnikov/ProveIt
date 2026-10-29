import DiophantineConsistency.PRALanguage
import Foundation.FirstOrder.Arithmetic.Schemata

/-! Object-theory primitives for primitive-recursive arithmetic. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRATheory
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage

/-- A positional member of a finite code list. -/
def getCode : {n m : ℕ} → Codes n m → Fin m → Code n
  | _, _, .nil _, i => Fin.elim0 i
  | _, _, .cons h t, i => Fin.cases h (getCode t) i

abbrev TermN (n : ℕ) := Semiterm language Empty n

def applyCode {n m : ℕ} (c : Code m) (v : Fin m → TermN n) : TermN n := .func c v

def vars (n : ℕ) : Fin n → TermN n := fun i => .bvar i

def equalClosure {n : ℕ} (a b : TermN n) : Sentence language :=
  ∀⁰* (Semiformula.rel Language.ORing.Rel.eq ![a, b])

def zeroEquation (n : ℕ) : Sentence language :=
  equalClosure (applyCode (.zero n) (vars n)) (applyCode (.zero 0) Fin.elim0)

def projectionEquation {n : ℕ} (i : Fin n) : Sentence language :=
  equalClosure (applyCode (.proj i) (vars n)) (.bvar i)

def compositionEquation {m n : ℕ} (f : Code m) (g : Codes n m) : Sentence language :=
  equalClosure (applyCode (.comp f g) (vars n))
    (applyCode f (fun i => applyCode (getCode g i) (vars n)))

def recursionBaseEquation {n : ℕ} (f : Code n) (g : Code (n+2)) : Sentence language :=
  let params : Fin n → TermN n := vars n
  equalClosure (applyCode (.prec f g) (Fin.cases (applyCode (.zero 0) Fin.elim0) params))
    (applyCode f params)

def recursionStepEquation {n : ℕ} (f : Code n) (g : Code (n+2)) : Sentence language :=
  let params : Fin n → TermN (n+1) := fun i => .bvar i.succ
  let counter : TermN (n+1) := .bvar 0
  let previous := applyCode (.prec f g) (Fin.cases counter params)
  equalClosure (applyCode (.prec f g)
    (Fin.cases (applyCode .succ (fun _ => counter)) params))
    (applyCode g (Fin.cases counter (Fin.cases previous params)))

inductive DefiningEquation : Theory language
  | zero (n : ℕ) : DefiningEquation (zeroEquation n)
  | projection {n : ℕ} (i : Fin n) : DefiningEquation (projectionEquation i)
  | composition {m n : ℕ} (f : Code m) (g : Codes n m) :
      DefiningEquation (compositionEquation f g)
  | recursionBase {n : ℕ} (f : Code n) (g : Code (n+2)) :
      DefiningEquation (recursionBaseEquation f g)
  | recursionStep {n : ℕ} (f : Code n) (g : Code (n+2)) :
      DefiningEquation (recursionStepEquation f g)

/-- The fixed function equations plus all language equality and open induction.
Successor and order axioms remain separate until explicitly supplied. -/
def core : Theory language :=
  (𝗘𝗤 language) ∪ DefiningEquation ∪ InductionScheme language Semiformula.Open

local instance : Structure language ℕ := natStructure

theorem getCode_forget : ∀ {n m : ℕ} (g : Codes n m) (i : Fin m),
    forget (getCode g i) = forgetMany g i
  | _, _, .nil _, i => Fin.elim0 i
  | _, _, .cons _ t, i => Fin.cases rfl (fun j => getCode_forget t j) i

theorem zeroEquation_valid (n : ℕ) : (zeroEquation n).Evalb (M := ℕ) ![] := by
  simp only [zeroEquation, equalClosure, Semiformula.eval_allClosure, Semiformula.eval_rel]
  intro e
  rfl

theorem projectionEquation_valid {n : ℕ} (i : Fin n) :
    (projectionEquation i).Evalb (M := ℕ) ![] := by
  simp only [projectionEquation, equalClosure, Semiformula.eval_allClosure, Semiformula.eval_rel]
  intro e
  change (List.Vector.ofFn e).get i = e i
  exact List.Vector.get_ofFn _ _

theorem compositionEquation_valid {m n : ℕ} (f : Code m) (g : Codes n m) :
    (compositionEquation f g).Evalb (M := ℕ) ![] := by
  simp only [compositionEquation, equalClosure, Semiformula.eval_allClosure, Semiformula.eval_rel]
  intro e
  change PRAFunctionCodes.eval (forget f)
      (List.Vector.ofFn fun i => PRAFunctionCodes.eval (forgetMany g i) (List.Vector.ofFn e)) =
    PRAFunctionCodes.eval (forget f)
      (List.Vector.ofFn fun i => PRAFunctionCodes.eval (forget (getCode g i)) (List.Vector.ofFn e))
  simp only [getCode_forget]

theorem recursionBaseEquation_valid {n : ℕ} (f : Code n) (g : Code (n+2)) :
    (recursionBaseEquation f g).Evalb (M := ℕ) ![] := by
  simp only [recursionBaseEquation, equalClosure, Semiformula.eval_allClosure, Semiformula.eval_rel]
  intro e
  change PRAFunctionCodes.eval (forget f) (List.Vector.ofFn (Fin.cases 0 e)).tail =
    PRAFunctionCodes.eval (forget f) (List.Vector.ofFn e)
  congr 1

theorem recursionStepEquation_valid {n : ℕ} (f : Code n) (g : Code (n+2)) :
    (recursionStepEquation f g).Evalb (M := ℕ) ![] := by
  simp only [recursionStepEquation, equalClosure, Semiformula.eval_allClosure, Semiformula.eval_rel]
  intro e
  change PRAFunctionCodes.eval (forget g)
      (e 0 ::ᵥ PRAFunctionCodes.eval (forget (.prec f g)) (List.Vector.ofFn e) ::ᵥ
        (List.Vector.ofFn e).tail) =
    PRAFunctionCodes.eval (forget g)
      (List.Vector.ofFn (Fin.cases (e 0)
        (Fin.cases (PRAFunctionCodes.eval (forget (.prec f g)) (List.Vector.ofFn e))
          (fun i => e i.succ))))
  congr 1


theorem definingEquation_valid (φ : Sentence language) (h : DefiningEquation φ) :
    φ.Evalb (M := ℕ) ![] := by
  cases h with
  | zero n => exact zeroEquation_valid n
  | projection i => exact projectionEquation_valid i
  | composition f g => exact compositionEquation_valid f g
  | recursionBase f g => exact recursionBaseEquation_valid f g
  | recursionStep f g => exact recursionStepEquation_valid f g

local instance : Structure.Zero language ℕ := ⟨rfl⟩
local instance : Structure.One language ℕ := ⟨rfl⟩
local instance : Structure.Add language ℕ := ⟨fun x y => by
  change eval addCode (List.Vector.ofFn ![x,y]) = x+y
  rw [ofFn_two, eval_addCode]
  rfl⟩
local instance : Structure.Eq language ℕ := ⟨fun _ _ => iff_of_eq rfl⟩

theorem nat_models_succInd (φ : Semiformula language ℕ 1) :
    ℕ↓[language] ⊧ (succInd φ).univCl := by
  suffices ∀ e : ℕ → ℕ,
      φ.Eval ![0] e → (∀ x, φ.Eval ![x] e → φ.Eval ![x+1] e) →
        ∀ x, φ.Eval ![x] e by
    simpa [Semiformula.eval_univCl, succInd, models_iff,
      Matrix.constant_eq_singleton, Semiformula.eval_substs]
  intro e hz hs x
  induction x with
  | zero => exact hz
  | succ x ih => exact hs x ih

theorem nat_models_core : ℕ↓[language] ⊧* core := by
  constructor
  intro φ h
  rcases h with (heq | hdef) | hind
  · exact (Structure.Eq.models_eq language ℕ).models_set heq
  · simpa only [models_iff] using definingEquation_valid φ hdef
  · rcases hind with ⟨ψ, _, rfl⟩
    exact nat_models_succInd ψ

end DiophantineConsistency.PRATheory
