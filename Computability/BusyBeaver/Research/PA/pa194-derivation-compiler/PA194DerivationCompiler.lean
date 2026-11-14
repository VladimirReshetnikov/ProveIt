import PA194HeadSelectors
import PA194RhoSelector
import PA194GateSelector
import PA194Diagonal
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA194DerivationCompiler
open M6.Source.Cantor PA196.Commands PA196.Commands.Code PA194Words
open PA194HeadSelectors PA194RhoSelector PA194GateSelector PA194Diagonal
attribute [local irreducible] PA194Words.run PA194Words.pop PA194Words.push PA194Words.discard PA194Words.generalize PA194Words.mpSuffix PA194HeadSelectors.select PA194RhoSelector.selectRho8 PA194GateSelector.selectGate PA194Diagonal.selectDiagonal

/-- The separate-diagonal numerical calculus implemented by PA194's AX. -/
inductive Derivation : Nat → Type where
  | mp {a b} : Derivation a → Derivation (I a b) → Derivation b
  | all (a : Nat) {b} : Derivation b → Derivation (U a b)
  | h1 (d h : Nat) : Derivation (head1 d h)
  | h2 (d a h : Nat) : Derivation (head2 d a h)
  | h3 (h d a : Nat) : Derivation (head3 d a h)
  | h4 (h d a : Nat) : Derivation (head4 d a h)
  | h5 (d h : Nat) : Derivation (head5 d h)
  | h6 (d a h : Nat) : Derivation (head6 d a h)
  | r8 (a b c u : Nat) : u ≤ a → Derivation (rho8 a b c u)
  | gate (a b c : Nat) : c ≠ a → c ≠ b → Derivation (oldBundle a b c)
  | diagonal (c : Nat) : Derivation (PA194AXSymbolic.diagonal c)

theorem append_none {xs ys : List Command} {s : Store} (h : PA194Words.run xs s = none) :
    PA194Words.run (xs ++ ys) s = none := by rw [PA194Words.run_append,h]; rfl

theorem append_some_none {xs ys : List Command} {s m : Store}
    (h : PA194Words.run xs s = some m) (g : PA194Words.run ys m = none) :
    PA194Words.run (xs ++ ys) s = none := by rw [PA194Words.run_append,h]; exact g

def compile {a : Nat} : Derivation a → List Command
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
  | .diagonal c => selectDiagonal c

theorem compile_result {a : Nat} (p : Derivation a) (t w : Nat) :
    PA194Words.run (compile p) ⟨t,w,0,0⟩ = none ∨
      PA194Words.run (compile p) ⟨t,w,0,0⟩ = some ⟨a,w,0,0⟩ := by
  induction p generalizing t w with
  | @mp a b p q ihp ihq =>
    rcases ihq t w with hq | hq
    · exact Or.inl (append_none (append_none (append_none (append_none hq))))
    have hqpush := append_total hq (push_total (I a b) w 0 0)
    rcases ihp 0 (pair (I a b) w) with hp | hp
    · exact Or.inl (append_none (append_none (append_some_none hqpush hp)))
    have hboth := append_total (append_total hqpush hp) (push_total a (pair (I a b) w) 0 0)
    have hm := mpSuffix_result a b w
    by_cases ha : a = 1
    · rw [if_pos ha] at hm
      exact Or.inl (append_some_none hboth hm)
    · rw [if_neg ha] at hm
      exact Or.inr (append_total hboth hm)
  | @all i a p ih =>
    rcases ih t w with hp | hp
    · exact Or.inl (append_none hp)
    · exact Or.inr (append_total hp (generalize_total i a w))
  | h1 d h => exact Or.inr (select_head1_total d h 0 t w)
  | h2 d a h => exact Or.inr (select_head2_total d h a t w)
  | h3 h d a => exact Or.inr (select_head3_total d h a t w)
  | h4 h d a => exact Or.inr (select_head4_total d h a t w)
  | h5 d h => exact Or.inr (select_head5_total d h 0 t w)
  | h6 d a h => exact Or.inr (select_head6_total d h a t w)
  | r8 a b c u hu => exact Or.inr (selectRho8_total a b c u t w hu)
  | gate a b c ha hb =>
    right
    have hg : PA194AXReadable.guardedOldBundle a b c = oldBundle a b c := by
      simp [PA194AXReadable.guardedOldBundle,Ne.symm ha,Ne.symm hb]
    exact (selectGate_total a b c t w).trans
      (congrArg (fun v => (some ⟨v,w,0,0⟩ : Option Store)) hg)
  | diagonal c => exact Or.inr (selectDiagonal_total c t w)

def haltWord (p : Derivation 1) : List Command := [.ax 0 0 0] ++ compile p ++ [.shift]

theorem haltWord_universal (p : Derivation 1) (s : Store) :
    PA194Words.run (haltWord p) s = none := by
  let mid : Store := ⟨PA194AXReadable.guardedOldBundle s.h s.d 0,
    ([PA194AXSymbolic.diagonal 0] ++ heads s.d s.h 0 s.d s.h ++ [s.t]).foldr pair s.w,0,0⟩
  have hreset : PA194Words.run [.ax 0 0 0] s = some mid := by
    simp only [PA194Words.run,PA194Words.step,PA194CommandTransfer.step,Nat.add_zero,Option.bind_some,mid]
  rcases compile_result p mid.t mid.w with hp | hp
  · change PA194Words.run (compile p) mid = none at hp
    exact append_none (append_some_none hreset hp)
  · change PA194Words.run (compile p) mid = some ⟨1,mid.w,0,0⟩ at hp
    apply append_some_none (append_total hreset hp)
    simp [PA194Words.run,PA194Words.step,PA194CommandTransfer.step]

#print axioms compile_result
#print axioms haltWord_universal
end PA194DerivationCompiler
