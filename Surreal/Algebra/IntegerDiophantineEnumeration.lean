import Surreal.Algebra.IntegerDiophantineSystems
import Surreal.Algebra.IntegerArithmeticComputability
import Mathlib.Computability.RE

/-!
# Enumeration of finite integer Diophantine systems

The forward direction of `odg:def:thm:ce`. Checking any fixed finite system
on integer tuples is primitive recursive; unbounded search through integer
witness tuples semidecides its existential projection. Mathlib's standard
integer and finite-function encodings are used throughout.
-/

namespace Surreal.IntegerDiophantine
open IntegerArithmeticComputability

/-- Existential search over an inhabited encodable witness type is semidecidable. -/
theorem re_exists_of_primrec {α β : Type*} [Primcodable α] [Primcodable β] [Inhabited β]
    (p : α → β → Prop) (hp : PrimrecRel p) : REPred (fun a => ∃ b, p a b) := by
  let e : ℕ → β := fun n => (Encodable.decode (α := β) n).getD default
  have he : Primrec e := Primrec.option_getD_default.comp Primrec.decode
  have hs : Function.Surjective e := fun b => ⟨Encodable.encode b, by simp [e]⟩
  letI : DecidableRel p := fun a b => hp.choose (a, b)
  have ht : PrimrecPred (fun z : α × ℕ => p z.1 (e z.2)) :=
    hp.comp Primrec.fst (he.comp Primrec.snd)
  have hr := (Partrec.rfind ht.decide.to_comp.partrec.to₂).dom_re
  apply hr.of_eq
  intro a
  simp only [Nat.rfind_dom, PFun.coe_val, Part.mem_some_iff, true_eq_decide_iff, Part.some_dom,
    implies_true, and_true]
  exact ⟨fun ⟨n, hn⟩ => ⟨e n, hn⟩, fun ⟨b, hb⟩ => by
    obtain ⟨n, rfl⟩ := hs b
    exact ⟨n, hb⟩⟩

/-- Evaluating a fixed integer polynomial on two finite tuples is primitive recursive. -/
theorem polynomial_eval_primrec {n m : ℕ} (p : MvPolynomial (Fin n ⊕ Fin m) ℤ) :
    Primrec (fun z : (Fin n → ℤ) × (Fin m → ℤ) => p.eval (Sum.elim z.1 z.2)) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using (Primrec.const c : Primrec (fun _ : (Fin n → ℤ) × (Fin m → ℤ) => c))
  | add p q hp hq =>
    simpa only [MvPolynomial.eval_add] using add_primrec.comp hp hq
  | mul_X p i hp =>
    have hi : Primrec (fun z : (Fin n → ℤ) × (Fin m → ℤ) => Sum.elim z.1 z.2 i) := by
      cases i with
      | inl i => exact Primrec.fin_app.comp Primrec.fst (Primrec.const i)
      | inr i => exact Primrec.fin_app.comp Primrec.snd (Primrec.const i)
    simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X] using mul_primrec.comp hp hi

/-- A finite conjunction of primitive-recursive predicates remains primitive recursive. -/
theorem forall_fin_primrec {α : Type*} [Primcodable α] {k : ℕ}
    (p : Fin k → α → Prop) (hp : ∀ j, PrimrecPred (p j)) : PrimrecPred (fun a => ∀ j, p j a) := by
  induction k with
  | zero =>
    exact ((Primrec.const true).primrecPred (p := fun _ : α => True)).of_eq (fun _ => by simp)
  | succ k ih =>
    exact ((hp 0).and (ih (fun j => p j.succ) (fun j => hp j.succ))).of_eq
      (fun a => (Fin.forall_fin_succ (P := fun j => p j a)).symm)

/-- The complete finite equation check is primitive recursive, including empty systems. -/
theorem System.check_primrec {n : ℕ} (p : System n) :
    PrimrecPred (fun z : (Fin n → ℤ) × (Fin p.witnesses → ℤ) =>
      ∀ j, (p.polynomial j).eval₂ (Int.castRingHom ℤ) (Sum.elim z.1 z.2) = 0) := by
  apply forall_fin_primrec
  intro j
  have h := Primrec.eq.comp (polynomial_eval_primrec (p.polynomial j)) (Primrec.const 0)
  have hc : Int.castRingHom ℤ = RingHom.id ℤ := Subsingleton.elim _ _
  simpa only [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, hc] using h

/-- Searching integer witness tuples enumerates exactly the system's free solutions. -/
theorem System.holds_re {n : ℕ} (p : System n) : REPred (fun x : Fin n → ℤ => p.Holds x) :=
  re_exists_of_primrec _ p.check_primrec

/-- Every finite-system Diophantine set of integer tuples is computably enumerable. -/
theorem Definable.re {n : ℕ} {D : Set (Fin n → ℤ)} (hD : Definable D) : REPred (· ∈ D) := by
  obtain ⟨p, hp⟩ := hD
  exact p.holds_re.of_eq hp

/-- In any ring retracting to the integers, integer-coefficient Diophantine traces are enumerable. -/
theorem Definable.integer_trace_re {n : ℕ} {R : Type*} [CommRing R] (ct : R →+* ℤ)
    {D : Set (Fin n → R)} (hD : Definable D) :
    REPred (fun x : Fin n → ℤ => (fun j => (x j : R)) ∈ D) :=
  (hD.integer_trace ct).re

/-- The forward implication of the classification for standard-supported subsets. -/
theorem Definable.standardImage_re {n : ℕ} {R : Type*} [CommRing R] (ct : R →+* ℤ)
    {D : Set (Fin n → ℤ)} (hD : Definable (standardImage D : Set (Fin n → R))) : REPred (· ∈ D) :=
  (hD.of_standardImage ct).re

end Surreal.IntegerDiophantine
