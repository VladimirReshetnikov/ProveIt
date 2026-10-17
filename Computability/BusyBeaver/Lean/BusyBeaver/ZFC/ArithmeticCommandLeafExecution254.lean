import BusyBeaver.ZFC.ArithmeticCommandBlockExecution254

/-!
All-internal execution of the original eight axiom leaves and
bundle leaf. The finite list notation records their fixed AX stack positions.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticCommandLeafExecution254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCode254
open ArithmeticTemplates254 (rho2 rho3 rho4 rho5 rho6 rho7 rho8 bundle)
open ArithmeticCommandStep254 ArithmeticCommandAppend254 ArithmeticCommandRun254
open ArithmeticCommandExecution254 ArithmeticProofWordContract254 ArithmeticCommandBlockExecution254
open ArithmeticCommandBlocks254 (Circuit)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem eval_nips_cont (t s d : V) (xs : List V) (h last rest : V)
    (hh : h ≠ 1) (hx : ∀ x, x ∈ xs → x ≠ 1) :
    evalValue (appendValue (nipsWord (xs.length+1)) rest)
      (stateValue t (pushL (xs++[last]) s) d h) = evalValue rest (stateValue t s d last) :=
  eval_append_success _ _ _ _ (eval_nips t s d xs h last hh hx)

/-- Pop to one AX entry, move it to top, and restore the saved stack. -/
theorem select_entry (xs : List V) (x : V) (ys : List V) (last g h s : V)
    (hh : h ≠ 1) (hg : g ≠ 1) (hx : x ≠ 1)
    (hxs : ∀ y, y ∈ xs → y ≠ 1) (hys : ∀ y, y ∈ ys → y ≠ 1) :
    evalValue (appendValue (nipsWord (xs.length+1)) (dropWord 0 (nipsWord (ys.length+2))))
      (stateValue g (pushL (xs++x::(ys++[last])) s) 0 h) = someState x s 0 last := by
  have hs : pushL (xs++x::(ys++[last])) s = pushL (xs++[x]) (pushL (ys++[last]) s) := by
    rw [← pushL_append]
    simp
  rw [hs, eval_nips_cont g _ 0 xs h x _ hh hxs, eval_drop]
  have he := eval_nips x s (0+0) (g::ys) x last hx (fun y hy => by
    cases List.mem_cons.mp hy with
    | inl h => rw [h]; exact hg
    | inr h => exact hys y h)
  rw [show ys.length+2 = (g::ys).length+1 by simp]
  simpa [pushL] using he

/-- Exact original leaf constructor, parameterized by its AX row position. -/
noncomputable def leafWord (j : Nat) (a b c u : V) : V :=
  (Circuit.leaf j .input0 .input1 .input2 .input3).eval a b c u

theorem leaf_contract (j : Nat) (a b c u x : V) (xs ys : List V)
    (hsplit : axList a 0 b c u = xs++x::ys)
    (hj : xs.length+1 = j) (hk : ys.length+2 = 11-j) : Contract (leafWord j a b c u) x := by
  intro t s
  right
  have hx : x ≠ 1 := axList_ne_one a 0 b c u x (by rw [hsplit]; simp)
  have hxs : ∀ y, y ∈ xs → y ≠ 1 := fun y hy => axList_ne_one a 0 b c u y (by rw [hsplit]; simp [hy])
  have hys : ∀ y, y ∈ ys → y ≠ 1 := fun y hy => axList_ne_one a 0 b c u y (by rw [hsplit]; simp [hy])
  simp only [leafWord, Circuit.leaf, circuit_append, circuit_consAx, circuit_consDrop,
    circuit_nips, Circuit.eval_input0, Circuit.eval_input1, Circuit.eval_input2,
    Circuit.eval_input3, Circuit.eval_zero]
  rw [eval_append_success _ _ _ _ (eval_discard a b c u t s), eval_ax]
  simp only [zero_add, axStack_eq]
  rw [hsplit, ← hk, ← hj]
  have he := select_entry xs x ys 0 (gateValue a b c) 0 s (by simp) (gate_ne_one a b c) hx hxs hys
  simpa [List.append_assoc] using he

theorem leaf1 (a b c u : V) : Contract (Circuit.leaf1.eval a b c u) (rho1 a b) :=
  leaf_contract 1 a b 0 0 _ [] _ rfl rfl rfl

theorem leaf2 (a b c u : V) : Contract (Circuit.leaf2.eval a b c u) (rho2 a b c) :=
  leaf_contract 2 a b c 0 _ [_] _ rfl rfl rfl

theorem leaf3 (a b c u : V) : Contract (Circuit.leaf3.eval a b c u) (rho3 a b c) :=
  leaf_contract 3 a b c 0 _ [_,_] _ rfl rfl rfl

theorem leaf4 (a b c u : V) : Contract (Circuit.leaf4.eval a b c u) (rho4 a b c) :=
  leaf_contract 4 a b c 0 _ [_,_,_] _ rfl rfl rfl

theorem leaf5 (a b c u : V) : Contract (Circuit.leaf5.eval a b c u) (rho5 a b c) :=
  leaf_contract 5 a b c 0 _ [_,_,_,_] _ rfl rfl rfl

theorem leaf6 (a b c u : V) : Contract (Circuit.leaf6.eval a b c u) (rho6 a b) :=
  leaf_contract 6 a b 0 0 _ [_,_,_,_,_] _ rfl rfl rfl

theorem leaf7 (a b c u : V) : Contract (Circuit.leaf7.eval a b c u) (rho7 a b c) :=
  leaf_contract 7 a b c 0 _ [_,_,_,_,_,_] _ rfl rfl rfl

theorem leaf8 (a b c u : V) : Contract (Circuit.leaf8.eval a b c u) (rho8 a b c u) :=
  leaf_contract 8 a b c u _ [_,_,_,_,_,_,_] _ rfl rfl rfl

theorem bundle_contract (a b c u : V) (h1 : c ≠ a) (h2 : c ≠ b) :
    Contract ((Circuit.bundleLeaf .input0 .input1 .input2).eval a b c u) (bundle a b c) := by
  intro t s
  right
  simp only [Circuit.bundleLeaf, circuit_append, circuit_consAx, circuit_nips,
    Circuit.eval_input0, Circuit.eval_input1, Circuit.eval_input2, Circuit.eval_zero]
  rw [eval_append_success _ _ _ _ (eval_discard a b c u t s), eval_ax]
  simp only [zero_add, axStack_eq]
  rw [show gateValue a b c = bundle a b c by simp [gateValue, h1, h2]]
  exact eval_nips (bundle a b c) s 0 (axList a 0 b c 0) 0 0 (by simp) (axList_ne_one _ _ _ _ _)

end SetTheory.BusyBeaver.ZFC.ArithmeticCommandLeafExecution254
