module
public import PA196.Commands.HeadSelectors
public import PA196.Logic.Basic
@[expose] public section

/-!
Compile every finite derivation in the exact PA196 calculus to a command word.
The result is operational: a word halts early or returns the derived formula
while preserving an arbitrary incoming stack. It does not assert that this
external recursion has already been arithmetized inside Peano arithmetic.
-/
namespace PA196.Commands
open M6.Source.Cantor

theorem logic_implication_code (a b : Nat) : Logic.wim a b = Code.I a b := rfl
theorem logic_universal_code (a b : Nat) : Logic.wal a b = Code.U a b := rfl
theorem logic_membership_code (a b : Nat) : Logic.wel a b = Code.M a b := rfl
theorem logic_equality_code (a b : Nat) : Logic.weq a b = Code.E a b := rfl
theorem logic_head1_code (d h : Nat) : Logic.head1 d h = Code.head1 d h := rfl
theorem logic_head2_code (d a h : Nat) : Logic.head2 d a h = Code.head2 d a h := rfl
theorem logic_head3_code (h d a : Nat) : Logic.head3 h d a = Code.head3 d a h := rfl
theorem logic_head4_code (h d a : Nat) : Logic.head4 h d a = Code.head4 d a h := rfl
theorem logic_head5_code (d h : Nat) : Logic.head5 d h = Code.head5 d h := rfl
theorem logic_head6_code (d a h : Nat) : Logic.head6 d a h = Code.head6 d a h := rfl
theorem logic_rho8_code (a b c u : Nat) : Logic.rho8 a b c u = Code.rho8 a b c u := rfl
theorem logic_bundle_code (a b c : Nat) : Logic.bundle a b c = Code.bundle a b c := rfl

attribute [local irreducible] push pop generalize mpSuffix select selectRho8 selectGate run step

def compile {a : Nat} : Logic.Derivation a → List Command
  | .mp (b := b) p q => compile q ++ push ++ compile p ++ push ++ mpSuffix b
  | .all i p => compile p ++ generalize i
  | .h1 d h => select 6 d h 0
  | .h2 d a h => select 5 d h a
  | .h3 h d a => select 4 d h a
  | .h4 h d a => select 3 d h a
  | .h5 d h => select 2 d h 0
  | .h6 d a h => select 1 d h a
  | .r8 a b c u _ => selectRho8 a b c u
  | .gate a b c _ _ => selectGate a b c

theorem compile_result {a : Nat} (p : Logic.Derivation a) (t w : Nat) :
    run (compile p) ⟨t, w, 0, 0⟩ = none ∨
      run (compile p) ⟨t, w, 0, 0⟩ = some ⟨a, w, 0, 0⟩ := by
  induction p generalizing t w with
  | @mp a b p q ihp ihq =>
    rcases ihq t w with hq | hq
    · exact Or.inl (append_none (append_none (append_none (append_none hq))))
    have hqpush := append_total hq (push_total (Logic.wim a b) w 0 0)
    rcases ihp 0 (pair (Logic.wim a b) w) with hp | hp
    · exact Or.inl (append_none (append_none (append_some_none hqpush hp)))
    have hboth := append_total (append_total hqpush hp)
      (push_total a (pair (Logic.wim a b) w) 0 0)
    have hm := mpSuffix_result a b w
    rw [← logic_implication_code] at hm
    by_cases ha : a = 1
    · rw [ite_eq_left ha] at hm
      exact Or.inl (append_some_none hboth hm)
    · rw [ite_eq_right ha] at hm
      exact Or.inr (append_total hboth hm)
  | @all i a p ih =>
    rcases ih t w with hp | hp
    · exact Or.inl (append_none hp)
    · have hg := generalize_total i a w
      rw [← logic_universal_code] at hg
      exact Or.inr (append_total hp hg)
  | h1 d h => exact Or.inr (select_head1_total d h 0 t w)
  | h2 d a h => exact Or.inr (select_head2_total d h a t w)
  | h3 h d a => exact Or.inr (select_head3_total d h a t w)
  | h4 h d a => exact Or.inr (select_head4_total d h a t w)
  | h5 d h => exact Or.inr (select_head5_total d h 0 t w)
  | h6 d a h => exact Or.inr (select_head6_total d h a t w)
  | r8 a b c u hu => exact Or.inr (selectRho8_total a b c u t w hu)
  | gate a b c ha hb =>
    right
    have hg : Code.gate a b c = Logic.bundle a b c := by
      simp only [Code.gate, ha, hb, false_or, ite_false, logic_bundle_code]
    exact (selectGate_total a b c t w).trans
      (congrArg (fun v => (some ⟨v, w, 0, 0⟩ : Option Store)) hg)

def haltWord (p : Logic.Derivation 1) : List Command :=
  [.ax 0 0 0] ++ compile p ++ [.shift]

/-- A derivation of falsity gives a finite command word halting from every
incoming store; previous computations may leave arbitrary register contents. -/
theorem haltWord_universal (p : Logic.Derivation 1) (s : Store) :
    run (haltWord p) s = none := by
  let mid : Store := ⟨Code.gate s.h s.d 0,
    (Code.heads s.d s.h 0 s.d s.h ++ [s.t]).foldr pair s.w, 0, 0⟩
  have hreset : run [.ax 0 0 0] s = some mid := by
    simp only [run, ax_step, Nat.add_zero, Option.bind_some, mid]
  rcases compile_result p mid.t mid.w with hp | hp
  · change run (compile p) mid = none at hp
    exact append_none (append_some_none hreset hp)
  · change run (compile p) mid = some ⟨1, mid.w, 0, 0⟩ at hp
    apply append_some_none (append_total hreset hp)
    simp [run, step]

#print axioms compile_result
#print axioms haltWord_universal
end PA196.Commands
