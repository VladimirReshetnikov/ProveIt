module
public import PA196.Commands.Words
@[expose] public section

/-! Exact selectors for every generated head and the guarded gate. The head
number in `select` is its stack position, counted from the top starting at one,
so positions one through six select paper heads six through one. -/
namespace PA196.Commands
open M6.Source.Cantor Code

def pops : Nat → List Command
  | 0 => []
  | n + 1 => pop ++ pops n

theorem pops_stack (xs : List Nat) (t a w d h : Nat) :
    run (pops (xs.length + 1)) ⟨t, (xs ++ [a]).foldr pair w, d, h⟩ =
      some ⟨t, w, 0, a⟩ := by
  induction xs generalizing d h with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, pops, List.append_nil,
      List.nil_append, List.foldr_cons, List.foldr_nil] using pop_total t a w d h
  | cons x xs ih =>
    simp only [List.length_cons, List.cons_append, List.foldr_cons, pops,
      run_append, pop_total, Option.bind_some]
    simpa only [pops, run_append] using ih 0 x

def select (j D H A : Nat) : List Command :=
  discard ++ ([.ax A D H] ++ List.replicate (j + 1) .shift) ++ pops (8 - j)

def selectRho8 (a b c u : Nat) : List Command :=
  (discard ++ offset u) ++ ([.ax b (a - u) c] ++ List.replicate 8 .shift) ++ pop

theorem selectRho8_total (a b c u t w : Nat) (hu : u ≤ a) :
    run (selectRho8 a b c u) ⟨t, w, 0, 0⟩ = some ⟨rho8 a b c u, w, 0, 0⟩ := by
  have hadd : u + (a - u) = a := by omega
  have hx := ax_shift8 b (a - u) c 0 w u 0
  simp only [Nat.zero_add, hadd] at hx
  exact append_total
    (append_total (append_total (discard_total t w) (offset_total u w)) hx)
    (pop_total (rho8 a b c u) 0 w 0 (U u 0))

def selectGate (a b c : Nat) : List Command :=
  discard ++ [.ax c b a] ++ pops 9

theorem selectGate_total (a b c t w : Nat) :
    run (selectGate a b c) ⟨t, w, 0, 0⟩ = some ⟨gate a b c, w, 0, 0⟩ := by
  have hx : run [.ax c b a] ⟨0, w, 0, 0⟩ =
      some ⟨gate a b c, (heads b a c 0 0 ++ [0]).foldr pair w, 0, 0⟩ := by
    simp [run, ax_step]
  exact append_total (append_total (discard_total t w) hx)
    (pops_stack (heads b a c 0 0) (gate a b c) 0 w 0 0)

#print axioms pops_stack
#print axioms selectRho8_total
#print axioms selectGate_total
end PA196.Commands
