module
public import PA196.Arithmetic.LiteralWords
@[expose] public section

/-! Calibration of the uniform arithmetic command interpreter to the
executable natural-number interpreter. This is an additional exactness
check, not a restriction of the all-model command theorems. -/
namespace PA196.Arithmetic.CommandStep
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open M6.PA M6.PA.SourceCantorInternal HeadGraphs CommandWord LiteralWords

noncomputable def storeCode (s : Commands.Store) : Nat := stateCode s.t s.w s.d s.h
noncomputable def optionStoreCode : Option Commands.Store → Nat
  | none => 0
  | some s => storeCode s

theorem gate_standard (a b c d : Nat) : gateValue a b c d = Commands.Code.gate a b c := by
  by_cases ha : c = a <;> by_cases hb : c = b <;>
    simp [gateValue, Commands.Code.gate, ha, hb, ActualArithmeticGraph.eval_standard, bundle_exact]

theorem schemaHeads_standard (D H A d h : Nat) :
    schemaHeads D H A d h = Commands.Code.heads D H A d h := by
  simp only [schemaHeads, Commands.Code.heads, ActualArithmeticGraph.eval_standard,
    head1_exact, head2_exact, head3_exact, head4_exact, head5_exact, head6_exact,
    rho8_exact, universal_exact]

theorem step_standard (c : Commands.Command) (s : Commands.Store) :
    stepValue (Commands.atom c) (storeCode s) = optionStoreCode (Commands.step c s) := by
  cases c with
  | shift =>
    change stepValue 0 (stateCode s.t s.w s.d s.h) = _
    rw [shift_value]
    have hl : decodeLeft s.w = (M6.Source.Cantor.decode s.w).1 :=
      congrArg Prod.fst (decode_standard s.w)
    have hr : decodeRight s.w = (M6.Source.Cantor.decode s.w).2 :=
      congrArg Prod.snd (decode_standard s.w)
    by_cases hh : s.t + s.h = 1 <;>
      simp [Commands.step, hh, optionStoreCode, storeCode, hl, hr]
  | mp b =>
    have hm : Commands.atom (.mp b) = mpCode (V := Nat) b := by
      simpa using mp_atom_numeral (V := Nat) b
    rw [hm]
    unfold storeCode
    rw [mp_value, ActualArithmeticGraph.eval_standard, implication_exact, pair_standard]
    by_cases hh : Commands.Code.I s.t (s.d + b) = s.h <;>
      simp [Commands.step, hh, optionStoreCode, storeCode]
  | ax c x y =>
    have ha : Commands.atom (.ax c x y) = axCode (V := Nat) c x y := by
      simpa using ax_atom_numeral (V := Nat) c x y
    rw [ha]
    unfold storeCode
    rw [ax_value, gate_standard, schemaHeads_standard]
    have hp : (pairValue : Nat → Nat → Nat) = M6.Source.Cantor.pair :=
      funext fun a => funext fun b => pair_standard a b
    rw [hp]
    rfl

theorem run_standard (xs : List Commands.Command) (s : Commands.Store) :
    wordValue (literalValue (Commands.atoms xs)) (storeCode s) =
      optionStoreCode (Commands.run xs s) := by
  induction xs generalizing s with
  | nil => simp [Commands.atoms, Commands.run, optionStoreCode]
  | cons c cs ih =>
    simp only [Commands.atoms, List.map_cons, literal_cons, natCast_nat, word_cons]
    rw [step_standard]
    cases he : Commands.step c s with
    | none => simp [Commands.run, he, optionStoreCode]
    | some u => simpa [Commands.atoms, Commands.run, he, optionStoreCode] using ih u

theorem run_halts_iff (xs : List Commands.Command) (s : Commands.Store) :
    wordValue (literalValue (Commands.atoms xs)) (storeCode s) = 0 ↔
      Commands.run xs s = none := by
  rw [run_standard]
  cases he : Commands.run xs s with
  | none => simp [optionStoreCode]
  | some u => simp [optionStoreCode, storeCode, stateCode_ne_zero]

theorem word_graph_halts_standard (xs : List Commands.Command) (s : Commands.Store) :
    wordGraph.val.Evalb ![0, literalValue (Commands.atoms xs), storeCode s] ↔
      Commands.run xs s = none := by
  rw [word_graph, eq_comm, run_halts_iff]

#print axioms step_standard
#print axioms run_standard
#print axioms word_graph_halts_standard
end PA196.Arithmetic.CommandStep
