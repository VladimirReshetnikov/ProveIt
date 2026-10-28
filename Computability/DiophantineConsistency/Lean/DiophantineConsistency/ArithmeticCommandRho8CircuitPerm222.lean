import DiophantineConsistency.ArithmeticCommandCircuitPerm222
import DiophantineConsistency.ArithmeticCommandRulePerm222

/-! One fixed circuit for unrestricted rho8, before choosing any model/input.
The generic finite dominated-implication derivation is interpreted in a
syntactic expression algebra. Its proof predicate retains the circuit
existential outside all model/input quantifiers. There is no internal
proof-code recursion, circuit interpreter or global proof-word history. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCommandRho8CircuitPerm222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCode254 ArithmeticCommandCircuitPerm222
open ArithmeticCommandLeafPerm222 ArithmeticCommandRulePerm222
universe u

/-- Fixed symbolic formula inputs, distinct from numeric word syntax. -/
inductive Expr where
  | input0 | input1 | input2 | input3
  | imp (left right : Expr)

def Expr.circuit : Expr → Circuit
  | .input0 => .input0
  | .input1 => .input1
  | .input2 => .input2
  | .input3 => .input3
  | .imp a b => .imp a.circuit b.circuit

noncomputable def Expr.eval {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (e : Expr) (a b c u : V) : V := e.circuit.eval a b c u

inductive Below : Expr → Expr → Prop
  | refl (a : Expr) : Below a a
  | left {a b : Expr} (c : Expr) : Below a b → Below a (.imp b c)
  | right {a c : Expr} (b : Expr) : Below a c → Below a (.imp b c)

theorem below_eval {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {x y : Expr} (h : Below x y) (a b c u : V) : x.eval a b c u ≤ y.eval a b c u := by
  induction h with
  | refl => exact le_rfl
  | left z h ih =>
    exact le_trans ih (tagged_components 0 _ _).1
  | right z h ih =>
    exact le_trans ih (tagged_components 0 _ _).2

def exprLanguage : DominatedImplication.Language Expr where
  imp := Expr.imp
  below := Below
  refl := Below.refl
  grow_left := Below.left
  grow_right := Below.right

/-- Actual numeric MP word, represented by a finite circuit expression. -/
def mpCircuit (B pa pab : Circuit) : Circuit :=
  .append pa (Circuit.consDrop (.append pab (Circuit.consNip
    (Circuit.consDrop (Circuit.consNip (Circuit.consMp B
      (Circuit.consAx B .zero .zero (.append (Circuit.nips 10) Circuit.terminator))))))))

theorem eval_mpCircuit {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (B pa pab : Circuit) (a b c u : V) :
    (mpCircuit B pa pab).eval a b c u =
      mpBlockWord (B.eval a b c u) (pa.eval a b c u) (pab.eval a b c u) := by
  simp only [mpCircuit,Circuit.eval,Circuit.eval_consDrop,Circuit.eval_consNip,
    Circuit.eval_consMp,Circuit.eval_consAx,Circuit.eval_nips,Circuit.eval_terminator,
    mpBlockWord,mpTail]

/-- The witness is fixed before any model or any of the four inputs. -/
def Uniform (p : Expr) : Prop :=
  ∃ e : Circuit, ∀ {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    ∀ a b c u : V, Contract (e.eval a b c u) (p.eval a b c u)

/-- Restricted rows are implemented by the physical guarded leaf. MP
constructs its circuit with minor first, although Dom takes major first. -/
theorem uniform_restricted : DominatedImplication.Restricted exprLanguage Uniform.{u} := by
  constructor
  · intro A B hmajor hminor
    obtain ⟨major,hm⟩ := hmajor
    obtain ⟨minor,hn⟩ := hminor
    refine ⟨mpCircuit B.circuit minor major,?_⟩
    intro V inst sat a b c u
    rw [eval_mpCircuit]
    exact mp_contract (hn a b c u) (hm a b c u)
  · intro A B C U hbelow
    refine ⟨Circuit.leaf 8 A.circuit B.circuit C.circuit U.circuit,?_⟩
    intro V inst sat a b c u
    rw [Circuit.eval_leaf]
    exact leaf8 _ _ _ _ (below_eval hbelow a b c u)

/-- The complete finite generic derivation supplies the uniform witness. -/
theorem unrestricted_expr (A B C U : Expr) :
    Uniform.{u} (DominatedImplication.rho8 exprLanguage A B C U) :=
  DominatedImplication.rho8_all uniform_restricted A B C U

/-- One externally finite circuit works in every internal model at all inputs.
Its arithmetic graph is the already proved literal `Circuit.graph`. -/
theorem exists_rho8_circuit :
    ∃ e : Circuit, ∀ {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
      ∀ a b c u : V, Contract (e.eval a b c u) (ArithmeticTemplates254.rho8 a b c u) := by
  obtain ⟨e,he⟩ := unrestricted_expr.{u} .input0 .input1 .input2 .input3
  refine ⟨e,?_⟩
  intro V inst sat a b c u
  exact he a b c u

end DiophantineConsistency.ArithmeticCommandRho8CircuitPerm222
