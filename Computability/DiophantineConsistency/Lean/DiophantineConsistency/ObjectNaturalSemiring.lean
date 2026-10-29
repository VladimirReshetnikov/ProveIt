import DiophantineConsistency.ObjectOmegaSemiring
import DiophantineConsistency.NaturalExpressionSemiring
import DiophantineConsistency.ObjectPolynomial

/-! # Exact semiring interpretation of the object-language polynomial graph

All assignments below range over the model's entire internal omega.
-/
namespace DiophantineConsistency.ObjectNaturalSemiring
open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency ObjectNaturalExpression ObjectPolynomial
open ObjectOmegaSemiring

universe u
variable {V : Type u} {mem : V → V → Prop} {σ : Type*}

theorem evalRel_iff (H : ZFAxioms mem) (e : NatExpr σ) (v : σ → Natural H)
    (z : Natural H) :
    EvalRel H (fun i => (v i).val) e z.val ↔ e.evalSemiring v=z := by
  induction e generalizing z with
  | constant n =>
    change z.val=natV H n ↔ (n : Natural H)=z
    constructor
    · intro h
      exact Subtype.ext h.symm
    · intro h
      exact (congrArg Subtype.val h).symm
  | var i =>
    change z.val=(v i).val ↔ v i=z
    exact ⟨fun h => Subtype.ext h.symm,fun h => (congrArg Subtype.val h).symm⟩
  | add p q hp hq | mul p q hp hq =>
    constructor
    · rintro ⟨a,b,ha,hb,hrel⟩
      let aa : Natural H := ⟨a,evalRel_result_nat H _ (fun i => (v i).property) p ha⟩
      let bb : Natural H := ⟨b,evalRel_result_nat H _ (fun i => (v i).property) q hb⟩
      have ea : p.evalSemiring v=aa := (hp aa).mp ha
      have eb : q.evalSemiring v=bb := (hq bb).mp hb
      first
      | change p.evalSemiring v+q.evalSemiring v=z
      | change p.evalSemiring v*q.evalSemiring v=z
      rw [ea,eb]
      first
      | exact (Natural.addRel_iff H aa bb z).mp hrel
      | exact (Natural.mulRel_iff H aa bb z).mp hrel
    · intro h
      first
      | exact ⟨(p.evalSemiring v).val,(q.evalSemiring v).val,
          (hp _).mpr rfl,(hq _).mpr rfl,(Natural.addRel_iff H _ _ z).mpr h⟩
      | exact ⟨(p.evalSemiring v).val,(q.evalSemiring v).val,
          (hp _).mpr rfl,(hq _).mpr rfl,(Natural.mulRel_iff H _ _ z).mpr h⟩

theorem equationRel_iff {n : ℕ} (H : ZFAxioms mem) (e : Expr (Fin n))
    (v : Fin n → Natural H) :
    EquationRel H e (fun i => (v i).val) ↔
      e.splitNatural.1.evalSemiring v=e.splitNatural.2.evalSemiring v := by
  constructor
  · rintro ⟨z,hp,hq⟩
    let zz : Natural H := ⟨z,evalRel_result_nat H _ (fun i => (v i).property) _ hp⟩
    exact ((evalRel_iff H e.splitNatural.1 v zz).mp hp).trans
      ((evalRel_iff H e.splitNatural.2 v zz).mp hq).symm
  · intro h
    exact ⟨(e.splitNatural.1.evalSemiring v).val,
      (evalRel_iff H _ v _).mpr rfl,(evalRel_iff H _ v _).mpr h.symm⟩

theorem noZeroRel_iff {n : ℕ} (H : ZFAxioms mem) (e : Expr (Fin n)) :
    NoZeroRel H e ↔ ∀ v : Fin n → Natural H,
      e.splitNatural.1.evalSemiring v ≠ e.splitNatural.2.evalSemiring v := by
  constructor
  · intro h v he
    exact h (fun i => (v i).val) (fun i => (v i).property) ((equationRel_iff H e v).mpr he)
  · intro h v hv he
    let vv : Fin n → Natural H := fun i => ⟨v i,hv i⟩
    exact h vv ((equationRel_iff H e vv).mp he)

/-- The supplied sentence is exactly semiring inequality for every internal
natural assignment, including nonstandard assignments. -/
theorem sat_noZeroForm_iff {n : ℕ} (H : ZFAxioms mem) (e : Expr (Fin n)) :
    (∀ ee : Nat → V, Sat mem ee (noZeroForm e)) ↔ ∀ v : Fin n → Natural H,
      e.splitNatural.1.evalSemiring v ≠ e.splitNatural.2.evalSemiring v :=
  (ObjectPolynomial.sat_noZeroForm_iff H e).trans (noZeroRel_iff H e)

end DiophantineConsistency.ObjectNaturalSemiring
