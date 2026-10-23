import DiophantineConsistency.ArithmeticDAGSemantics

/-! # Certificate checker for sharing powers in an arithmetic DAG -/
namespace DiophantineConsistency.ArithmeticDAG
variable {inputs fixed : ℕ} {R : Type*} [CommRing R]

def PowerStep (nodes : List (Node inputs fixed)) (label : ℕ → ℕ) (i : ℕ) : Prop :=
  match nodes.getD i (.literal 0) with
  | .mul a b => label a ≠ 0 ∧ label b ≠ 0 ∧ label i = label a+label b
  | _ => False

instance (nodes : List (Node inputs fixed)) (label : ℕ → ℕ) (i : ℕ) :
    Decidable (PowerStep nodes label i) := by
  unfold PowerStep
  split <;> infer_instance

private theorem PowerStep.spec {nodes : List (Node inputs fixed)} {label : ℕ → ℕ} {i : ℕ}
    (h : PowerStep nodes label i) : ∃ a b,
      nodes.getD i (.literal 0) = .mul a b ∧ label a ≠ 0 ∧ label b ≠ 0 ∧
        label i = label a+label b := by
  cases hn : nodes.getD i (.literal 0) <;> simp_all [PowerStep]

/-- Numeric exponent labels certify all original pure-power nodes. -/
theorem run_power (p : Fin fixed → R) (x : Fin inputs → R)
    (nodes : List (Node inputs fixed)) (htop : Topological nodes) (label : ℕ → ℕ)
    (base : ℕ) (hlbase : label base = 1)
    (hstep : ∀ i < nodes.length, i ≠ base → label i ≠ 0 → PowerStep nodes label i) :
    ∀ i < nodes.length, label i ≠ 0 →
      (run p x nodes []).getD i 0 = ((run p x nodes []).getD base 0) ^ label i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi hli
    by_cases hib : i = base
    · subst i
      rw [hlbase,pow_one]
    · obtain ⟨a,b,hn,hla,hlb,he⟩ := (hstep i hi hib hli).spec
      have ha : a < i := htop ⟨i,hi⟩ a (by rw [hn];simp [Node.dependencies])
      have hb : b < i := htop ⟨i,hi⟩ b (by rw [hn];simp [Node.dependencies])
      rw [run_node_equation p x nodes htop i hi,hn]
      simp only [Node.evalAt]
      rw [ih a ha (ha.trans hi) hla,ih b hb (hb.trans hi) hlb,he,pow_add]

/-- Matching binary nodes may use different operand indices. -/
def NodeRel (rel : ℕ → ℕ → Prop) : Node inputs fixed → Node inputs fixed → Prop
  | .literal a,.literal b => a = b
  | .input a,.input b => a = b
  | .constant a,.constant b => a = b
  | .add a b,.add c d | .sub a b,.sub c d | .mul a b,.mul c d => rel a c ∧ rel b d
  | _,_ => False

instance (rel : ℕ → ℕ → Prop) [DecidableRel rel] (n m : Node inputs fixed) :
    Decidable (NodeRel rel n m) := by
  cases n <;> cases m <;> simp only [NodeRel] <;> infer_instance

theorem evalAt_of_NodeRel (p : Fin fixed → R) (x : Fin inputs → R)
    (rel : ℕ → ℕ → Prop) (old new : Node inputs fixed) (v w : ℕ → R)
    (h : NodeRel rel old new) (hv : ∀ i j, rel i j → w j = v i) :
    new.evalAt p x w = old.evalAt p x v := by
  cases old <;> cases new <;> simp_all [NodeRel,Node.evalAt]
  all_goals rw [hv _ _ h.1,hv _ _ h.2]

/-- Reference correspondence either uses the retained index map or equal power labels. -/
def PowerRef (old : List (Node inputs fixed)) (oldLabel newLabel indexMap : ℕ → ℕ)
    (i j : ℕ) : Prop :=
  i < old.length ∧ if newLabel j = 0 then indexMap j = i else oldLabel i = newLabel j

instance (old : List (Node inputs fixed)) (oldLabel newLabel indexMap : ℕ → ℕ)
    (i j : ℕ) : Decidable (PowerRef old oldLabel newLabel indexMap i j) := by
  unfold PowerRef
  infer_instance

def PowerRewriteStep (old new : List (Node inputs fixed))
    (oldLabel newLabel indexMap : ℕ → ℕ) (base i : ℕ) : Prop :=
  if i = base ∨ newLabel i = 0 then
    indexMap i < old.length ∧ NodeRel (PowerRef old oldLabel newLabel indexMap)
      (old.getD (indexMap i) (.literal 0)) (new.getD i (.literal 0))
  else PowerStep new newLabel i

instance (old new : List (Node inputs fixed)) (oldLabel newLabel indexMap : ℕ → ℕ)
    (base i : ℕ) : Decidable (PowerRewriteStep old new oldLabel newLabel indexMap base i) := by
  unfold PowerRewriteStep
  infer_instance

/-- Complete rewrite soundness over every commutative ring. No circuit is unrolled. -/
theorem value_eq_of_powerRewrite (p : Fin fixed → R) (x : Fin inputs → R)
    (old new : List (Node inputs fixed)) (hold : Topological old) (hnew : Topological new)
    (oldLabel newLabel indexMap : ℕ → ℕ) (oldBase newBase oldOutput newOutput : ℕ)
    (hlold : oldLabel oldBase = 1) (hlnew : newLabel newBase = 1)
    (hbase : indexMap newBase = oldBase)
    (holdStep : ∀ i < old.length, i ≠ oldBase → oldLabel i ≠ 0 → PowerStep old oldLabel i)
    (hnewStep : ∀ i < new.length,
      PowerRewriteStep old new oldLabel newLabel indexMap newBase i)
    (houtput : newOutput < new.length) (houtputLabel : newLabel newOutput = 0)
    (houtputMap : indexMap newOutput = oldOutput) :
    value new newOutput p x = value old oldOutput p x := by
  let u : ℕ → R := fun i => (run p x old []).getD i 0
  let B := u oldBase
  let v : ℕ → R := fun i => if newLabel i = 0 then u (indexMap i) else B ^ newLabel i
  have hpower := run_power p x old hold oldLabel oldBase hlold holdStep
  have href (i j : ℕ) (h : PowerRef old oldLabel newLabel indexMap i j) : v j = u i := by
    obtain ⟨hi,hrel⟩ := h
    by_cases hz : newLabel j = 0
    · simpa only [PowerRef,v,if_pos hz] using congrArg u (by simpa only [hz,if_true] using hrel)
    · have he : oldLabel i = newLabel j := by simpa only [if_neg hz] using hrel
      have hli : oldLabel i ≠ 0 := by omega
      rw [show u i = B ^ oldLabel i from hpower i hi hli]
      simp only [v,if_neg hz,he]
  have hlocal : ∀ i < new.length, v i = (new.getD i (.literal 0)).evalAt p x v := by
    intro i hi
    have hs := hnewStep i hi
    by_cases hcase : i = newBase ∨ newLabel i = 0
    · rw [PowerRewriteStep,if_pos hcase] at hs
      obtain ⟨hm,hn⟩ := hs
      have hv : v i = u (indexMap i) := by
        by_cases hz : newLabel i = 0
        · simp only [v,if_pos hz]
        · have hib : i = newBase := hcase.resolve_right hz
          subst i
          simp only [v,hlnew,one_ne_zero,if_false,pow_one,B,hbase]
      calc
        v i = u (indexMap i) := hv
        _ = (old.getD (indexMap i) (.literal 0)).evalAt p x u :=
          run_node_equation p x old hold _ hm
        _ = (new.getD i (.literal 0)).evalAt p x v := (evalAt_of_NodeRel p x _ _ _ u v hn href).symm
    · rw [PowerRewriteStep,if_neg hcase] at hs
      obtain ⟨a,b,hn,hla,hlb,he⟩ := hs.spec
      have hli : newLabel i ≠ 0 := fun hz => hcase (Or.inr hz)
      simp only [v,if_neg hli,hn,Node.evalAt,if_neg hla,if_neg hlb,he,pow_add]
  rw [value_eq_of_node_equations p x new hnew newOutput houtput v hlocal]
  simp only [v,houtputLabel,if_pos,houtputMap,u,value]

end DiophantineConsistency.ArithmeticDAG
