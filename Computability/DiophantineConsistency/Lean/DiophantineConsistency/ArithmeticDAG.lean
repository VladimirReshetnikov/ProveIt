import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.List.GetD
import Mathlib.Logic.Relation
import Mathlib.Tactic

/-! # Topological binary arithmetic circuits and their polynomial semantics -/
namespace DiophantineConsistency.ArithmeticDAG

open MvPolynomial

inductive Node (inputs fixed : ℕ) where
  | literal (value : ℤ)
  | input (index : Fin inputs)
  | constant (index : Fin fixed)
  | add (left right : ℕ)
  | sub (left right : ℕ)
  | mul (left right : ℕ)
  deriving DecidableEq, Repr

namespace Node
variable {inputs fixed : ℕ}

def dependencies : Node inputs fixed → List ℕ
  | .add a b | .sub a b | .mul a b => [a,b]
  | _ => []

def isBinary : Node inputs fixed → Bool
  | .add _ _ | .sub _ _ | .mul _ _ => true
  | _ => false

def kind : Node inputs fixed → ℕ
  | .literal _ => 0
  | .input _ => 1
  | .constant _ => 2
  | .add _ _ => 3
  | .sub _ _ => 4
  | .mul _ _ => 5

def eval {R : Type*} [CommRing R] (p : Fin fixed → R) (x : Fin inputs → R)
    (values : List R) : Node inputs fixed → R
  | .literal z => (z : R)
  | .input i => x i
  | .constant i => p i
  | .add a b => values.getD a 0 + values.getD b 0
  | .sub a b => values.getD a 0 - values.getD b 0
  | .mul a b => values.getD a 0 * values.getD b 0

theorem eval_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (p : Fin fixed → R) (x : Fin inputs → R) (values : List R)
    (n : Node inputs fixed) :
    n.eval (fun i => φ (p i)) (fun i => φ (x i)) (values.map φ) =
      φ (n.eval p x values) := by
  have hg (i : ℕ) : (values.map φ).getD i 0 = φ (values.getD i 0) := by
    simpa only [map_zero] using (List.getD_map (l := values) (d := 0) φ (n := i))
  cases n <;> simp only [eval,hg,map_intCast,map_add,map_sub,map_mul]
end Node

variable {inputs fixed : ℕ}

/-- Append one evaluated node, in the original topological order. -/
def run {R : Type*} [CommRing R] (p : Fin fixed → R) (x : Fin inputs → R) :
    List (Node inputs fixed) → List R → List R
  | [],values => values
  | n::ns,values => run p x ns (values ++ [n.eval p x values])

theorem run_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (p : Fin fixed → R) (x : Fin inputs → R)
    (nodes : List (Node inputs fixed)) (values : List R) :
    run (fun i => φ (p i)) (fun i => φ (x i)) nodes (values.map φ) =
      (run p x nodes values).map φ := by
  induction nodes generalizing values with
  | nil => rfl
  | cons n ns ih =>
    simpa only [run, List.map_append, List.map_singleton, Node.eval_map] using
      ih (values ++ [n.eval p x values])

/-- Total semantics use zero for invalid references; topology excludes them. -/
def value {R : Type*} [CommRing R] (nodes : List (Node inputs fixed)) (output : ℕ)
    (p : Fin fixed → R) (x : Fin inputs → R) : R := (run p x nodes []).getD output 0

theorem value_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (nodes : List (Node inputs fixed)) (output : ℕ)
    (p : Fin fixed → R) (x : Fin inputs → R) :
    value nodes output (fun i => φ (p i)) (fun i => φ (x i)) =
      φ (value nodes output p x) := by
  unfold value
  have hr := run_map φ p x nodes []
  simp only [List.map_nil] at hr
  rw [hr]
  simpa only [map_zero] using
    (List.getD_map (l := run p x nodes []) (d := 0) φ (n := output))

noncomputable def polynomial (nodes : List (Node inputs fixed)) (output : ℕ)
    (p : Fin fixed → ℤ) : MvPolynomial (Fin inputs) ℤ :=
  value nodes output (fun i => C (p i)) X

theorem eval_polynomial (nodes : List (Node inputs fixed)) (output : ℕ)
    (p : Fin fixed → ℤ) (x : Fin inputs → ℤ) :
    MvPolynomial.eval x (polynomial nodes output p) = value nodes output p x := by
  simpa only [polynomial,MvPolynomial.eval_C,MvPolynomial.eval_X] using
    (value_map (MvPolynomial.eval x) nodes output (fun i => C (p i)) X).symm

/-- Every reference is to a previously evaluated node. -/
def Topological (nodes : List (Node inputs fixed)) : Prop :=
  ∀ i : Fin nodes.length, ∀ j ∈ (nodes.getD i.val (.literal 0)).dependencies, j < i.val

instance (nodes : List (Node inputs fixed)) : Decidable (Topological nodes) :=
  inferInstanceAs (Decidable (∀ i : Fin nodes.length,
    ∀ j ∈ (nodes.getD i.val (.literal 0)).dependencies, j < i.val))

/-- Edges point from an operand to a consumer. -/
def Edge (nodes : List (Node inputs fixed)) (i j : ℕ) : Prop :=
  i ∈ (nodes.getD j (.literal 0)).dependencies

def Reaches (nodes : List (Node inputs fixed)) (output i : ℕ) : Prop :=
  Relation.ReflTransGen (Edge nodes) i output

/-- A later consumer certificate proves genuine ancestor reachability. -/
theorem reaches_of_laterConsumer (nodes : List (Node inputs fixed)) (output : ℕ)
    (hconsumer : ∀ i < output, ∃ j, i < j ∧ j ≤ output ∧ Edge nodes i j) :
    ∀ i ≤ output, Reaches nodes output i := by
  intro i hi
  have hgeneral : ∀ d, ∀ i ≤ output, output-i = d → Reaches nodes output i := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro i hi hdi
      by_cases he : i = output
      · subst i
        exact Relation.ReflTransGen.refl
      · obtain ⟨j,hij,hjo,hedge⟩ := hconsumer i (by omega)
        have hdist : output-j < d := by omega
        exact Relation.ReflTransGen.head hedge (ih (output-j) hdist j hjo rfl)
  exact hgeneral (output-i) i hi rfl

/-- A concrete later-consumer table proves reachability for each node. -/
theorem reaches_of_consumer_table (nodes : List (Node inputs fixed)) (consumers : List ℕ)
    (output : ℕ) (hlen : nodes.length = output + 1)
    (hc : ∀ i : Fin output, i.val < consumers.getD i.val 0 ∧
      consumers.getD i.val 0 ≤ output ∧ Edge nodes i.val (consumers.getD i.val 0))
    (i : ℕ) (hi : i < nodes.length) : Reaches nodes output i := by
  apply reaches_of_laterConsumer nodes output (fun j hj => ⟨_, hc ⟨j, hj⟩⟩) i
  omega

def operationCount (nodes : List (Node inputs fixed)) : ℕ :=
  ((Finset.range nodes.length).filter (fun i => (nodes.getD i (.literal 0)).isBinary)).card

def kindCount (nodes : List (Node inputs fixed)) (k : ℕ) : ℕ :=
  ((Finset.range nodes.length).filter (fun i => (nodes.getD i (.literal 0)).kind = k)).card

noncomputable def liveOperationCount (nodes : List (Node inputs fixed)) (output : ℕ) : ℕ := by
  classical
  exact ((Finset.range nodes.length).filter (fun i =>
    (nodes.getD i (.literal 0)).isBinary ∧ Reaches nodes output i)).card

theorem liveOperationCount_eq (nodes : List (Node inputs fixed)) (output : ℕ)
    (h : ∀ i < nodes.length, Reaches nodes output i) :
    liveOperationCount nodes output = operationCount nodes := by
  classical
  have he : (Finset.range nodes.length).filter (fun i =>
      (nodes.getD i (.literal 0)).isBinary ∧ Reaches nodes output i) =
      (Finset.range nodes.length).filter (fun i => (nodes.getD i (.literal 0)).isBinary) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_range]
    exact ⟨fun hi => ⟨hi.1,hi.2.1⟩,fun hi => ⟨hi.1,hi.2,h i hi.1⟩⟩
  exact congrArg Finset.card he

end DiophantineConsistency.ArithmeticDAG
