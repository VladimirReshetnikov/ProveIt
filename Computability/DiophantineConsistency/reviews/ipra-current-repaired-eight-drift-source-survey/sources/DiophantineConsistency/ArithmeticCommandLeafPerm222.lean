import DiophantineConsistency.ArithmeticCommandBlockPerm222

/-! Finite actual C222 AX selection and halt-or-restored-success contracts.
The physical AX fourth label is the old counter: direct rho8 retains u≤a.
False1 is only a conditional target terminator, never an axiom leaf.
No GEN/MP proof composition, represented compiler, or history is claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.ArithmeticCommandLeafPerm222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254 ArithmeticTemplates254
open ArithmeticCommandStepPerm222 ArithmeticCommandAppendPerm222
open ArithmeticCommandRunPerm222 ArithmeticCommandCompositionPerm222
open ArithmeticCommandBlockPerm222
attribute [local irreducible] Code254.P
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- All internal initial tops and saved stacks, with zero counter/cache. -/
def Contract (word target : V) : Prop := ∀ top S,
  evalValue word (stateValue top S 0 0)=0 ∨
  evalValue word (stateValue top S 0 0)=someState target S 0 0

private instance state_delta : 𝚫₁-Function₄[V] stateValue :=
  state_defined.graph_delta.to_definable
private instance someState_delta : 𝚫₁-Function₄[V] someState :=
  someState_defined.graph_delta.to_definable
private instance eval_delta : 𝚫₁-Function₂[V] evalValue :=
  eval_defined_delta.to_definable

instance contract_definable : 𝚷₁-Relation (Contract (V := V)) := by
  unfold Contract
  definability

theorem truth_contract : Contract (discardWord : V) 0 :=
  fun top S => Or.inr (eval_discard top S)

/-- The last loaded cache may be1; no later NIP tests it. -/
theorem select_entry (xs : List V) (x : V) (ys : List V) (last g h S : V)
    (hh : h≠1) (hg : g≠1) (hx : x≠1)
    (hxs : ∀ y, y∈xs → y≠1) (hys : ∀ y, y∈ys → y≠1) :
    evalValue (appendValue (nipsWord (xs.length+1))
      (dropWord (nipsWord (ys.length+2))))
      (stateValue g (pushL (xs++x::(ys++[last])) S) 0 h)=someState x S 0 last := by
  have hs : pushL (xs++x::(ys++[last])) S =
      pushL (xs++[x]) (pushL (ys++[last]) S) := by
    rw [← pushL_append]
    simp
  rw [hs,eval_nips_cont g _ 0 xs h x _ hh hxs,eval_drop]
  have he := eval_nips x S 0 (g::ys) x last hx (fun y hy => by
    cases List.mem_cons.mp hy with
    | inl h => rw [h]; exact hg
    | inr h => exact hys y h)
  rw [show ys.length+2=(g::ys).length+1 by simp]
  simpa only [pushL,List.cons_append] using he

/-- Nine physical positions; rho6 uses AX's c and row7 is growG. -/
noncomputable def leafWord (j : Nat) (a b c u : V) : V :=
  appendValue discardWord (appendValue (Jword u)
    (axWord c (a-u) b (appendValue (nipsWord j) (dropWord (nipsWord (11-j))))))

theorem eval_leaf (j : Nat) (a b c u x : V) (xs ys : List V) (hu : u≤a)
    (hsplit : axList a 0 b c u=xs++x::ys)
    (hj : xs.length+1=j) (hk : ys.length+2=11-j) (top S : V) :
    evalValue (leafWord j a b c u) (stateValue top S 0 0)=someState x S 0 0 := by
  have hx : x≠1 := axList_ne_one a 0 b c u x (by rw [hsplit]; simp)
  have hxs : ∀ y, y∈xs → y≠1 := fun y hy =>
    axList_ne_one a 0 b c u y (by rw [hsplit]; simp [hy])
  have hys : ∀ y, y∈ys → y≠1 := fun y hy =>
    axList_ne_one a 0 b c u y (by rw [hsplit]; simp [hy])
  rw [leafWord,eval_discard_ax top S a b c u _ hu,axStack_eq,hsplit,← hk,← hj]
  simpa only [List.append_assoc,List.cons_append] using
    select_entry xs x ys 0 (gateValue a b c) 0 S (by simp) (gate_ne_one a b c) hx hxs hys

theorem leaf_contract (j : Nat) (a b c u x : V) (xs ys : List V) (hu : u≤a)
    (hsplit : axList a 0 b c u=xs++x::ys)
    (hj : xs.length+1=j) (hk : ys.length+2=11-j) : Contract (leafWord j a b c u) x :=
  fun top S => Or.inr (eval_leaf j a b c u x xs ys hu hsplit hj hk top S)

theorem leaf1 (a b : V) : Contract (leafWord 1 a b 0 0) (rho1 a b) :=
  leaf_contract 1 a b 0 0 _ [] _ (by simp) rfl rfl rfl
theorem leaf2 (a b c : V) : Contract (leafWord 2 a b c 0) (rho2 a b c) :=
  leaf_contract 2 a b c 0 _ [_] _ (by simp) rfl rfl rfl
theorem leaf3 (a b c : V) : Contract (leafWord 3 a b c 0) (rho3 a b c) :=
  leaf_contract 3 a b c 0 _ [_,_] _ (by simp) rfl rfl rfl
theorem leaf4 (a b c : V) : Contract (leafWord 4 a b c 0) (rho4 a b c) :=
  leaf_contract 4 a b c 0 _ [_,_,_] _ (by simp) rfl rfl rfl
theorem leaf5 (a b c : V) : Contract (leafWord 5 a b c 0) (rho5 a b c) :=
  leaf_contract 5 a b c 0 _ [_,_,_,_] _ (by simp) rfl rfl rfl
/-- AX physically places rho6(a,c); this adapter supplies c=b. -/
theorem leaf6 (a b : V) : Contract (leafWord 6 a 0 b 0) (rho6 a b) :=
  leaf_contract 6 a 0 b 0 _ [_,_,_,_,_] _ (by simp) rfl rfl rfl
theorem leaf7 (a b c : V) :
    Contract (leafWord 7 a b c 0) (ArithmeticTemplates222.growG a b c) :=
  leaf_contract 7 a b c 0 _ [_,_,_,_,_,_] _ (by simp) rfl rfl rfl
/-- Direct physical selection keeps its real truncated-subtraction guard. -/
theorem leaf8 (a b c u : V) (hu : u≤a) :
    Contract (leafWord 8 a b c u) (rho8 a b c u) :=
  leaf_contract 8 a b c u _ [_,_,_,_,_,_,_] _ hu rfl rfl rfl
theorem leaf9 (a b c u : V) (hu : u≤a) :
    Contract (leafWord 9 a b c u) (wal u 0) :=
  leaf_contract 9 a b c u _ [_,_,_,_,_,_,_,_] _ hu rfl rfl rfl

noncomputable def bundleWord (a b c : V) : V :=
  appendValue discardWord (appendValue (Jword 0) (axWord c a b (nipsWord 10)))

/-- Gate collisions are retained, rather than asserted to be seed axioms. -/
theorem eval_bundle (a b c top S : V) :
    evalValue (bundleWord a b c) (stateValue top S 0 0)=
      someState (gateValue a b c) S 0 0 := by
  have he := eval_discard_ax top S a b c 0 (nipsWord 10) (by simp)
  simp only [Arithmetic.sub_zero] at he
  rw [bundleWord,he,axStack_eq]
  exact eval_nips _ S 0 (axList a 0 b c 0) 0 0 (by simp) (axList_ne_one a 0 b c 0)

theorem gate_contract (a b c : V) : Contract (bundleWord a b c) (gateValue a b c) :=
  fun top S => Or.inr (eval_bundle a b c top S)
theorem bundle_contract (a b c : V) (ha : c≠a) (hb : c≠b) :
    Contract (bundleWord a b c) (ArithmeticSeedTemplates222.bundle222 a b c) := by
  simpa only [gateValue,ha,hb,or_self,if_false] using gate_contract a b c
theorem bundle_collision (a b c : V) (h : c=a ∨ c=b) :
    Contract (bundleWord a b c) 0 := by
  simpa only [gateValue,if_pos h] using gate_contract a b c

noncomputable def terminatorWord : V := dropWord (nipWord (nipWord 0))

/-- The first NIP loads false1 from cache0; the next NIP tests it. -/
theorem eval_terminator (S : V) :
    evalValue terminatorWord (stateValue 1 S 0 0)=0 := by
  simp [terminatorWord,eval_drop,eval_nip]

/-- Conditional on an existing false-target block, not a false axiom. -/
theorem false_target_halts (word : V) (h : Contract word 1) (top S : V) :
    evalValue (appendValue word terminatorWord) (stateValue top S 0 0)=0 := by
  rcases h top S with hh | hs
  · exact eval_append_halt _ _ _ hh
  · rw [eval_append_success _ _ _ _ hs,eval_terminator]

end DiophantineConsistency.ArithmeticCommandLeafPerm222
