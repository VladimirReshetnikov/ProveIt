module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6.Source.Cantor
public import Foundation.FirstOrder.Arithmetic.HFS.PRF
@[expose] public section
open M6.Arithmetic.PA

/-! Explicit primitive-recursion blueprint for the source triangular number,
valid in every IΣ1 model, including nonstandard inputs. It is separate from the
chosen computable-predicate representation and from HFS pairing. -/
namespace M6.PA.SourceCantorInternal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

noncomputable def triangleBlueprint : PR.Blueprint 0 where
  zero := .mkSigma “z. z = 0”
  succ := .mkSigma “u z i. u = z + i + 1”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def triangleConstruction : PR.Construction V triangleBlueprint where
  zero := fun _ => 0
  succ := fun _ i z => z+i+1
  zero_defined := .mk fun v => by simp [triangleBlueprint]
  succ_defined := .mk fun v => by simp [triangleBlueprint]

noncomputable def triangleValue (n : V) : V := triangleConstruction.result ![] n
noncomputable def triangleGraph : 𝚺ᴬ₁.Semisentence 2 := triangleBlueprint.resultDef

@[simp] theorem triangle_zero : triangleValue (0 : V) = 0 := by
  simp [triangleValue,triangleConstruction]
@[simp] theorem triangle_succ (n : V) : triangleValue (n+1) = triangleValue n+n+1 := by
  simp [triangleValue,triangleConstruction]

theorem triangle_graph (z n : V) :
    triangleGraph.val.Evalb ![z,n] ↔ z=triangleValue n := by
  have he : (fun _ : Fin 0 => n) = (![] : Fin 0 → V) := by
    funext i
    exact Fin.elim0 i
  simpa [triangleGraph,triangleValue,he] using
    (triangleConstruction (V := V)).result_defined_iff ![z,n]

theorem triangle_total_unique (n : V) : ∃! z, triangleGraph.val.Evalb ![z,n] := by
  refine ⟨triangleValue n,(triangle_graph _ _).mpr rfl,?_⟩
  intro z hz
  exact (triangle_graph _ _).mp hz

theorem triangle_standard (n : Nat) : triangleValue n = M6.Source.Cantor.triangle n := by
  induction n with
  | zero => simp [M6.Source.Cantor.triangle]
  | succ n ih => simp only [triangle_succ,M6.Source.Cantor.triangle,ih]

noncomputable def pairValue (a b : V) : V := triangleValue (a+b)+b
noncomputable def pairGraph : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “z a b. ∃ t, !triangleGraph t (a+b) ∧ z = t+b”

theorem pair_graph (z a b : V) : pairGraph.val.Evalb ![z,a,b] ↔ z=pairValue a b := by
  simp [pairGraph,triangle_graph,pairValue]

theorem pair_total_unique (a b : V) : ∃! z, pairGraph.val.Evalb ![z,a,b] := by
  refine ⟨pairValue a b,(pair_graph _ _ _).mpr rfl,?_⟩
  intro z hz
  exact (pair_graph _ _ _).mp hz

theorem pair_standard (a b : Nat) : pairValue a b = M6.Source.Cantor.pair a b := by
  simp only [pairValue,triangle_standard,M6.Source.Cantor.pair]

noncomputable def triangleTotalSentence : ArithmeticSentence := “∀ n, ∃ z, !triangleGraph z n”
noncomputable def pairTotalSentence : ArithmeticSentence := “∀ a b, ∃ z, !pairGraph z a b”

theorem pa_proves_triangle_total : theory ⊢ triangleTotalSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [triangleTotalSentence,models_iff]
  simp [triangle_graph]

theorem pa_proves_pair_total : theory ⊢ pairTotalSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [pairTotalSentence,models_iff]
  simp [pair_graph]

#print axioms triangle_standard
#print axioms pair_standard
#print axioms pa_proves_triangle_total
#print axioms pa_proves_pair_total
end M6.PA.SourceCantorInternal

