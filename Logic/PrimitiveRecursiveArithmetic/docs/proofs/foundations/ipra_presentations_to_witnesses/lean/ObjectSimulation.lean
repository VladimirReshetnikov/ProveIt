import ObjectFusion

/-!
# Quantifier-free relational simulation in object iPRA

`simulation` accepts an actual local preservation derivation for a QF relation.
It synthesizes the iterated relation and its QF induction proof. Arbitrary
host predicates are not reflected into `Prf PRAAx`.
-/

namespace LeanProofs.ConciseIPRA.FiniteMethods

open Syn
open scoped Fm

def tuple2 {n : Nat} (x y : PTm n) : Fin 2 → PTm n :=
  Fin.cases x (fun _ => y)

@[simp] theorem tuple2_zero {n : Nat} (x y : PTm n) : tuple2 x y 0 = x := rfl
@[simp] theorem tuple2_one {n : Nat} (x y : PTm n) : tuple2 x y 1 = y := rfl

theorem subst_tuple2 {n m : Nat} (σ : Fin n → PTm m) (x y : PTm n) :
    (fun i => Syn.subst σ (tuple2 x y i)) = tuple2 (Syn.subst σ x) (Syn.subst σ y) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem tuple2_var : tuple2 (var 0 : PTm 2) (var 1) = var := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  have hj : j = 0 := by omega
  subst j
  rfl

theorem qf_subst {n m : Nat} (A : Fm PTm n) (hA : A.QF) (σ : Fin n → PTm m) :
    (A.subst σ).QF := by
  induction A generalizing m with
  | eq => trivial
  | bot => trivial
  | and A B ihA ihB => exact ⟨ihA hA.1 σ, ihB hA.2 σ⟩
  | or A B ihA ihB => exact ⟨ihA hA.1 σ, ihB hA.2 σ⟩
  | imp A B ihA ihB => exact ⟨ihA hA.1 σ, ihB hA.2 σ⟩
  | all A _ => exact False.elim hA
  | ex A _ => exact False.elim hA

def localSimulation (R : Fm PTm 2) (f g : PR 1) : Fm PTm 2 :=
  R.subst (tuple2 (unary f (var 0)) (unary g (var 1)))

/-- counter 0; first initial state 1; second initial state 2. -/
def simulationInvariant (R : Fm PTm 2) (f g : PR 1) : Fm PTm 3 :=
  R.subst (tuple2 (iterTerm f (var 0) (var 1)) (iterTerm g (var 0) (var 2)))

theorem simulation (R : Fm PTm 2) (hR : R.QF) (f g : PR 1)
    (hlocal : [R] ⊢[PRAAx] localSimulation R f g) :
    [R] ⊢[PRAAx] Fm.all (simulationInvariant R f g) := by
  apply PRA.qfInd (simulationInvariant R f g) (qf_subst _ hR _)
  · simp only [simulationInvariant, Fm.subst_subst, subst_tuple2,
      subst_iterTerm, Syn.subst_var, Syn.inst_zero, Syn.inst_one]
    have hb : [R] ⊢[PRAAx] R.subst (tuple2 (var 0) (var 1)) := by
      simpa only [tuple2_var, Fm.subst_id] using (Prf.hyp0 (Ax := PRAAx) (Γ := []) (φ := R))
    apply Prf.eqSubst R (tuple2 (var 0) (var 1)) _ ?_ hb
    intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · exact Prf.eqSymm (iter_zero f (var 0))
    · exact Prf.eqSymm (iter_zero g (var 1))
  · simp only [simulationInvariant, Fm.subst_subst, subst_tuple2,
      subst_iterTerm, Syn.subst_var, Syn.repl_zero,
      List.map_cons, List.map_nil]
    let σ : Fin 2 → PTm 3 :=
      tuple2 (iterTerm f (var 0) (var 1)) (iterTerm g (var 0) (var 2))
    have hs : simulationInvariant R f g :: [R.shift] ⊢[PRAAx]
        R.subst (tuple2 (unary f (iterTerm f (var 0) (var 1)))
          (unary g (iterTerm g (var 0) (var 2)))) := by
      have ht := hlocal.subst σ
      simp only [localSimulation, Fm.subst_subst, subst_tuple2,
        subst_unary, Syn.subst_var, σ, tuple2_zero, tuple2_one,
        List.map_cons, List.map_nil] at ht
      exact ht.weaken (by simp [simulationInvariant])
    apply Prf.eqSubst R _ _ ?_ hs
    intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · exact Prf.eqSymm (iter_succ f (var 0) (var 1))
    · exact Prf.eqSymm (iter_succ g (var 0) (var 2))

end LeanProofs.ConciseIPRA.FiniteMethods

#print axioms LeanProofs.ConciseIPRA.FiniteMethods.simulation
