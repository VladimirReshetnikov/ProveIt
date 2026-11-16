module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualBasis
public import M6.Source.ActualSelectedHeads
public import M6.Source.ActualRuleMacros
@[expose] public section
open M6.Arithmetic.PA

/-! Structural compilation of the literal actual finite proof datatype into
actual arithmetic commands. A compiled proof either halts early or returns its
formula preserving the arbitrary stack. No PA-proof interpretation or internal
arithmetization is assumed. -/
namespace M6.PA.NativeCalculus.ActualBasis
open M6.Source M6.Source.Enumeration M6.Source.Cantor
open M6.Source.ActualCommandMacros

attribute [local irreducible] PUSH H genTail mpTail headWord head8Word gateWord
  commandsEval commandEval

def compile {a : Nat} : Proof a → List Command
  | .mp (b := b) p q => compile q ++ PUSH ++ compile p ++ PUSH ++ mpTail b
  | .all x p => compile p ++ genTail x
  | .r1 a b => headWord 1 a b 0
  | .r2 a b c => headWord 2 a b c
  | .r3 a b c => headWord 3 a b c
  | .r4 a b c => headWord 4 a b c
  | .r5 a b c => headWord 5 a b c
  | .r6 a b => headWord 6 a b 0
  | .r7 a b c => headWord 7 a b c
  | .r8 a b c u _ => head8Word a b c u
  | .bundle a b c _ _ => gateWord a b c

theorem source_wim_eq (a b : Nat) : AXCode.wim a b = wim a b := by
  simp only [AXCode.wim,wim]
theorem source_wal_eq (a b : Nat) : AXCode.wal a b = wal a b := by
  simp only [AXCode.wal,wal]

theorem append_none {xs ys : List Command} {s : CommandStore}
    (h : commandsEval xs s = none) : commandsEval (xs++ys) s = none := by
  rw [commandsEval_append,h]
  rfl

theorem append_some_none {xs ys : List Command} {s mid : CommandStore}
    (hx : commandsEval xs s = some mid) (hy : commandsEval ys mid = none) :
    commandsEval (xs++ys) s = none := by
  rw [commandsEval_append,hx]
  exact hy

theorem compile_result {a : Nat} (p : Proof a) (t w : Nat) :
    commandsEval (compile p) ⟨t,w,0,0⟩ = none ∨
      commandsEval (compile p) ⟨t,w,0,0⟩ = some ⟨a,w,0,0⟩ := by
  induction p generalizing t w with
  | @mp a b p q ihp ihq =>
    rcases ihq t w with hq | hq
    · exact Or.inl (append_none (append_none (append_none (append_none hq))))
    have hqpush := append_total hq (PUSH_total (wim a b) w 0 0)
    rcases ihp 0 (pair (wim a b) w) with hp | hp
    · exact Or.inl (append_none (append_none (append_some_none hqpush hp)))
    have hboth := append_total (append_total hqpush hp) (PUSH_total a (pair (wim a b) w) 0 0)
    have hm := mpTail_result a b w
    rw [source_wim_eq] at hm
    by_cases ha : a = 1
    · rw [ite_eq_left ha] at hm
      exact Or.inl (append_some_none hboth hm)
    · rw [ite_eq_right ha] at hm
      exact Or.inr (append_total hboth hm)
  | @all x a p ih =>
    rcases ih t w with hp | hp
    · exact Or.inl (append_none hp)
    · have hg := genTail_total x a w
      rw [source_wal_eq] at hg
      exact Or.inr (append_total hp hg)
  | r1 a b => exact Or.inr (head1_total a b 0 t w)
  | r2 a b c => exact Or.inr (head2_total a b c t w)
  | r3 a b c => exact Or.inr (head3_total a b c t w)
  | r4 a b c => exact Or.inr (head4_total a b c t w)
  | r5 a b c => exact Or.inr (head5_total a b c t w)
  | r6 a b => exact Or.inr (head6_total a b 0 t w)
  | r7 a b c => exact Or.inr (head7_total a b c t w)
  | r8 a b c u hu => exact Or.inr (head8_total a b c u t w hu)
  | bundle a b c ha hb =>
    right
    have hg : ActualAXCode.gate a b c = ActualAXCode.bundle a b c := by
      simp only [ActualAXCode.gate,ha,hb,false_or,ite_false]
    exact (gateWord_total a b c t w).trans
      (congrArg (fun v => (some ⟨v,w,0,0⟩ : Option CommandStore)) hg)

def haltWord (p : Proof 1) : List Command := [.ax 0 0 0] ++ compile p ++ [.shift]

theorem haltWord_universal (p : Proof 1) (s : CommandStore) :
    commandsEval (haltWord p) s = none := by
  let mid : CommandStore := ⟨ActualAXCode.gate s.d s.h 0,
    (ActualAXCode.pa135Heads s.d s.h 0 s.d s.h ++ [s.t]).foldr pair s.w,0,0⟩
  have hreset : commandsEval [.ax 0 0 0] s = some mid := by
    simp only [commandsEval,commandEval,Nat.add_zero,Option.bind_some,mid]
  rcases compile_result p mid.t mid.w with hp | hp
  · change commandsEval (compile p) mid = none at hp
    exact append_none (append_some_none hreset hp)
  · change commandsEval (compile p) mid = some ⟨1,mid.w,0,0⟩ at hp
    apply append_some_none (append_total hreset hp)
    simp [commandsEval,commandEval]

#print axioms compile_result
#print axioms haltWord_universal
end M6.PA.NativeCalculus.ActualBasis

