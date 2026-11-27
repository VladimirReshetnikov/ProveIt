import IPRADerivations.Foundations.BackwardDemand

/-!
# The explicit constant-loss observation budget

Finite-demand packet, equation `eq:constant-loss-budget`. The loss is
computed from persistent numerical data by a fixed PR program. Its value is
an internal natural parameter, not an external fixed numeral. The actual
backward program satisfies `b(j)=K+c*j` and `h(t)=K+c*(N∸t)` everywhere,
including zero loss, zero horizon and out-of-range totalized schedule values.
The resulting finite-transfer sentence requires only the initial observation
at `K+c*N`; schedule correctness is derived here.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Foundations.BackwardDemandBounds

open_ipra exports
open LeanProofs.IPRA.Foundations.BackwardDemand
open LeanProofs.IPRA.Foundations.BoundedFormulas (BF)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Demand arguments are stage, requested precision and persistent data. The fixed `loss` program reads the loss from those data. -/
def lossF (loss : PR 1) : PR 3 := PTm.toPR (var 1 + ap1 loss (var 2))

theorem loss_at (loss : PR 1) (stage k c : PTm n) :
    Γ ⊢[PRAAx] ap3 (lossF loss) stage k c ≐ k + ap1 loss c := by
  have e := toPR_eq (Γ := Γ) (var 1 + ap1 loss (var 2) : PTm 3) ![stage, k, c]
  change Γ ⊢[PRAAx] ap3 (lossF loss) stage k c ≐
    Syn.subst ![stage, k, c] (var 1 + ap1 loss (var 2) : PTm 3) at e
  refine e.eqTrans ?_
  simp only [PTm.subst_add, subst_ap1, Syn.subst_var,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  exact .eqRefl _

theorem backward_loss (loss : PR 1) (N K j c : PTm n) :
    Γ ⊢[PRAAx] backward (lossF loss) N K j c ≐ K + ap1 loss c * j := by
  have all : Γ ⊢[PRAAx] .all
      (backward (lossF loss) (Syn.shift N) (Syn.shift K) (var 0) (Syn.shift c) ≐
        Syn.shift K + ap1 loss (Syn.shift c) * var 0) := by
    ipra_qfind (trivial) [subst_backward, subst_ap1]
    · exact (backward_zero (lossF loss) N K c).eqTrans (by ipra_ring)
    · exact (backward_succ (lossF loss) (Syn.shift N) (Syn.shift K) (var 0) (Syn.shift c)).eqTrans
        ((loss_at loss _ _ _).eqTrans ((congrAdd Prf.hyp0 (.eqRefl _)).eqTrans (by ipra_ring)))
  ipra_simpa_inst [Fm.subst_eq, subst_backward, PTm.subst_add, PTm.subst_mul, subst_ap1] using Prf.allE j all

theorem horizon_loss (loss : PR 1) (N K t c : PTm n) :
    Γ ⊢[PRAAx] horizon (lossF loss) N K t c ≐ K + ap1 loss c * monus N t :=
  backward_loss loss N K (monus N t) c

theorem initial_budget (loss : PR 1) (N K c : PTm n) :
    Γ ⊢[PRAAx] horizon (lossF loss) N K zero c ≐ K + ap1 loss c * N :=
  (horizon_loss loss N K zero c).eqTrans (congrAdd (.eqRefl _) (congrMul (.eqRefl _) (monus_zero N)))

theorem constant_loss_transfer (A : BF) (loss : PR 1) (N K c : PTm n)
    (hstep : Γ ⊢[PRAAx] localStep A (lossF loss) N c)
    (hbase : Γ ⊢[PRAAx] observation A zero (K + ap1 loss c * N) c) :
    Γ ⊢[PRAAx] observation A N K c :=
  transfer A (lossF loss) N K c
    (observation_demand_congr A zero c (initial_budget loss N K c).eqSymm hbase) hstep

theorem constant_loss_schedule (loss : PR 1) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (horizon (lossF loss) (var 0) (var 1) (var 2) (var 3) ≐
        var 1 + ap1 loss (var 3) * monus (var 0) (var 2)) :=
  closeUniv 4 (horizon_loss loss _ _ _ _)

/-- The source equation with the loss itself an explicitly quantified input. -/
theorem numerical_constant_schedule :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (horizon (lossF (.proj 0)) (var 0) (var 1) (var 2) (var 3) ≐
        var 1 + var 3 * monus (var 0) (var 2)) := by
  apply closeUniv 4
  have projection : ([] : List (Fm PTm 4)) ⊢[PRAAx]
      ap1 (.proj 0) (var 3) ≐ var 3 := by
    simpa [ap1] using PRA.proj (Γ := ([] : List (Fm PTm 4))) (0 : Fin 1) ![var 3]
  exact (horizon_loss (.proj 0) (var 0) (var 1) (var 2) (var 3)).eqTrans
    (congrAdd (.eqRefl _) (congrMul projection (.eqRefl _)))

theorem constant_loss_transfer_closed (A : BF) (loss : PR 1) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (localStep A (lossF loss) (var 0) (var 2) ⟶
        observation A zero (var 1 + ap1 loss (var 2) * var 0) (var 2) ⟶
        observation A (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (constant_loss_transfer A loss _ _ _ Prf.hyp1 Prf.hyp0)))

#print axioms loss_at
#print axioms backward_loss
#print axioms initial_budget
#print axioms constant_loss_schedule
#print axioms numerical_constant_schedule
#print axioms constant_loss_transfer_closed

end LeanProofs.IPRA.Foundations.BackwardDemandBounds
