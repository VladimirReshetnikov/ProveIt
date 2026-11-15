import PA194FoundationOrdinalEmpty
import PA194SourceTemplates
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
namespace M6.PA.RelationalSource.Ordinal
open LO LO.FirstOrder ND

@[simp] theorem q_q_bvar_one {n m : Nat} (τ : Rew language Nat n Nat m) :
    τ.q.q (.bvar (1 : Fin (n+2))) = .bvar 1 := by
  change τ.q.q (.bvar (Fin.succ (0 : Fin (n+1)))) = _
  rw [Rew.q_bvar_succ,Rew.q_bvar_zero]
  rfl

@[simp] theorem q_q_q_bvar_two {n m : Nat} (τ : Rew language Nat n Nat m) :
    τ.q.q.q (.bvar (2 : Fin (n+3))) = .bvar 2 := by
  change τ.q.q.q (.bvar (Fin.succ (Fin.succ (0 : Fin (n+1))))) = _
  rw [Rew.q_bvar_succ,Rew.q_bvar_succ,Rew.q_bvar_zero]
  rfl

theorem zero_rew {n m : Nat} (τ : Rew language Nat n Nat m) (z : Term n) :
    Semiformula.rewAux τ (zero z) = zero (τ z) := by
  simp [zero, mem, Semiformula.rewAux, Semiformula.neg, Rew.q_comp_bShift_app, Rew.q_bvar_zero, Rew.q_bvar_succ] <;> rfl

theorem successor_rew {n m : Nat} (τ : Rew language Nat n Nat m) (x z : Term n) :
    Semiformula.rewAux τ (successor x z) = successor (τ x) (τ z) := by
  simp [successor, sourceIff, sourceImply, mem, eq, Semiformula.rewAux, Semiformula.neg, Rew.q_comp_bShift_app, Rew.q_bvar_zero, Rew.q_bvar_succ] <;> rfl

theorem domain_rew {n m : Nat} (τ : Rew language Nat n Nat m) (z : Term n) :
    Semiformula.rewAux τ (domain z) = domain (τ z) := by
  simp [domain,representative,memberIr,transitive,memberTransitive,memberLinear,
    internalExtrema,subset,nonempty,least,greatest, mem,eq,Semiformula.rewAux,
    Semiformula.neg, Semiformula.imp_eq, Rew.q_comp_bShift_app, Rew.q_bvar_zero, Rew.q_bvar_succ, q_q_bvar_one, q_q_q_bvar_two]
#print axioms zero_rew
#print axioms successor_rew
#print axioms domain_rew
end M6.PA.RelationalSource.Ordinal
