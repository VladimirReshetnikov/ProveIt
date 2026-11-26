import IPRADerivations.Analysis.DifferentialEquations.EulerPolygons.EulerProgram
import IPRADerivations.Analysis.DifferentialEquations.EulerPolygons.EulerAlgebra
import IPRADerivations.Analysis.DifferentialEquations.OdeGrowth

/-!
# The bound of the exact Euler array at its nodes

Packet: `analysis/ipra_certified_continuation_2026-11-19`, `paper/sections/07_ode.tex`, Lemma `lem:ode-polybound`
("Bounds produced by the Euler program"), the bound at the nodes: "Induction in `eq:exact-euler` gives
`‖X_{n,j}‖ ≤ (1 + K/n)^j U ≤ G U`" with `G = 3^K` (`eq:ode-constants`).

For the Euler program `Xn / Xd` of `EulerPolygons/EulerProgram` with mesh `n = n₀ + 1`, an initial vector `v / dv` with
`dv > 0` and `|v_i| ≤ U dv`, and the hypothesis `KBound B x K` (`‖B(t)‖ ≤ K` with positive denominators), the
following are derived in iPRA, for a node index `j` that is a term:

* `node_inv`: for `j ≤ n`, `Xd(j) > 0` and `n^j |Xn(j)_i| ≤ (n + K)^j U Xd(j)` for every component `i`, by
  quantifier-free induction on `j` (the step is `EulerAlgebra.node_step`, `‖X'‖ ≤ (1 + K/n) ‖X‖`);
* `Xd_pos`: the denominators are positive ("denominator positivity" of the implementation plan);
* `euler_node_bound`: `|Xn(j)_i| ≤ 3^K U Xd(j)` for `j ≤ n`, that is `‖X_{n,j}‖ ≤ G U`, by the integer geometric
  bound `(n + K)^j ≤ 3^K n^j` (`lem:ode-growth`, `Analysis/DifferentialEquations/OdeGrowth.growth_le`, which rests on
  `Foundations/DiscreteGronwall.growth`); `euler_node_norm`: the same for the maximum norm term
  `nrm` of the numerator vector.
-/

namespace LeanProofs.IPRA.Analysis.EulerNodeBound

open_ipra
open LeanProofs.IPRA.Foundations.TupleRecursion LeanProofs.IPRA.Foundations.SignedNorms
  LeanProofs.IPRA.Foundations.SignedCone LeanProofs.IPRA.Analysis.EulerProgram
open LeanProofs.IPRA.Analysis.OdeGrowth (growth_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')

variable {n d : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Positivity -/

/-- A successor is positive. -/
theorem succ_pos₀ (a : PTm n) : Γ ⊢[PRAAx] lt zero (succ a) := by
  show Γ ⊢[PRAAx] le (succ zero) (succ a)
  ipra_le 𝔞 a

/-- A product of positive terms is positive. -/
theorem mul_pos₀ {a b : PTm n} (ha : Γ ⊢[PRAAx] lt zero a) (hb : Γ ⊢[PRAAx] lt zero b) :
    Γ ⊢[PRAAx] lt zero (a * b) := by
  have ha' : Γ ⊢[PRAAx] le (succ zero) a := ha
  have hb' : Γ ⊢[PRAAx] le (succ zero) b := hb
  show Γ ⊢[PRAAx] le (succ zero) (a * b)
  ipra_le sl ha' * sl hb' + sl ha' + sl hb'

/-! ## The invariant -/

/-- For `j ≤ n`: the denominator is positive and `n^j |Xn(j)_i| ≤ (n + K)^j U Xd(j)`. -/
def NodeInv (B : Kernel d) (v : Fin d → ZT n) (dv U K x nn j : PTm n) : Fm PTm n :=
  le j nn ⟶ (lt zero (Xd B dv j nn x) ⋏
    conjFin fun i => le (pw nn j * abs (Xn B v j nn x i)) (pw (nn + K) j * (U * Xd B dv j nn x)))

@[simp] theorem subst_NodeInv {m : ℕ} (σ : Fin n → PTm m) (B : Kernel d) (v : Fin d → ZT n)
    (dv U K x nn j : PTm n) :
    (NodeInv B v dv U K x nn j).subst σ =
      NodeInv B (fun l => (v l).subst σ) (Syn.subst σ dv) (Syn.subst σ U) (Syn.subst σ K) (Syn.subst σ x)
        (Syn.subst σ nn) (Syn.subst σ j) := by
  simp only [NodeInv, Fm.subst_imp, Fm.subst_and, subst_le, subst_lt, subst_conjFin, subst_abs, subst_Xn,
    subst_Xd, PTm.subst_mul, PTm.subst_add, subst_ap2, ConciseIPRA.PTm.subst_zero]

theorem NodeInv_QF (B : Kernel d) (v : Fin d → ZT n) (dv U K x nn j : PTm n) :
    (NodeInv B v dv U K x nn j).QF :=
  ⟨le_QF _ _, lt_QF _ _, conjFin_QF fun _ => le_QF _ _⟩

section Step

variable {B : Kernel d} {v : Fin d → ZT n} {dv U K x n₀ j : PTm n}

/-- The base of the induction: `|v_i| ≤ U dv` at `j = 0`. -/
theorem node_inv_base (hdv : Γ ⊢[PRAAx] lt zero dv) (hv : ∀ i, Γ ⊢[PRAAx] le (abs (v i)) (U * dv)) :
    (Γ ⊢[PRAAx] lt zero (Xd B dv zero (succ n₀) x)) ∧
      ∀ i, Γ ⊢[PRAAx] le (pw (succ n₀) zero * abs (Xn B v zero (succ n₀) x i))
        (pw (succ n₀ + K) zero * (U * Xd B dv zero (succ n₀) x)) := by
  refine ⟨le_congr (.eqRefl _) (Xd_eq_zero B dv (succ n₀) x).eqSymm hdv, fun i => ?_⟩
  have p₁ := natEq (pw_zero (Γ := Γ) (succ n₀))
  have p₂ := natEq (pw_zero (Γ := Γ) (succ n₀ + K))
  simp only [Q.mk_one, map_one] at p₁ p₂
  refine le_abs_of_bd₀ ((bd_of_le₁ (hv i)).congr ?_ ?_)
  · rw [p₁, Xn_zero, _root_.one_mul]
  · simp only [Q.mk_mul, map_mul]
    rw [p₂, Xd_zero, _root_.one_mul]

/-- The step of the induction: one Euler step multiplies the norm by at most `1 + K/n`. -/
theorem node_inv_step (hK : Γ ⊢[PRAAx] KBound B x K) (hj : Γ ⊢[PRAAx] le (succ j) (succ n₀))
    (hD : Γ ⊢[PRAAx] lt zero (Xd B dv j (succ n₀) x))
    (ih : ∀ i, Γ ⊢[PRAAx] le (pw (succ n₀) j * abs (Xn B v j (succ n₀) x i))
      (pw (succ n₀ + K) j * (U * Xd B dv j (succ n₀) x))) :
    (Γ ⊢[PRAAx] lt zero (Xd B dv (succ j) (succ n₀) x)) ∧
      ∀ i, Γ ⊢[PRAAx] le (pw (succ n₀) (succ j) * abs (Xn B v (succ j) (succ n₀) x i))
        (pw (succ n₀ + K) (succ j) * (U * Xd B dv (succ j) (succ n₀) x)) := by
  have hjn : Γ ⊢[PRAAx] le j (succ n₀) := le_trans (le_succ_self j) hj
  have hnn : Γ ⊢[PRAAx] lt zero (succ n₀) := succ_pos₀ n₀
  obtain ⟨hb, hrow⟩ := kbound_use hK hnn hjn
  refine ⟨le_congr (.eqRefl _) (Xd_eq_succ B dv j (succ n₀) x).eqSymm (mul_pos₀ hD (mul_pos₀ hnn hb)),
    fun i => ?_⟩
  have e₁ := natEq (pw_succ (Γ := Γ) (succ n₀) j)
  have e₂ := natEq (pw_succ (Γ := Γ) (succ n₀ + K) j)
  simp only [Q.mk_mul, Q.mk_add, map_mul, map_add] at e₁ e₂
  have hM : RowBd (Nonneg Γ) (fun i k => ZT.toZ Γ (B.numAt i k j (succ n₀) x))
      (𝔞 K * 𝔞 (B.denAt j (succ n₀) x)) :=
    rowBd_congr (rowBd_of_le₁ hrow) (fun _ _ => rfl) (by simp only [Q.mk_mul, map_mul])
  have hx : ∀ k, Bd (Nonneg Γ) (𝔞 (pw (succ n₀) j) * ZT.toZ Γ (Xn B v j (succ n₀) x k))
      (𝔞 (pw (succ n₀ + K) j) * (𝔞 U * 𝔞 (Xd B dv j (succ n₀) x))) := fun k =>
    (bd_of_le (ih k)).congr rfl (by simp only [Q.mk_mul, map_mul])
  have hT : Nonneg Γ (𝔞 (pw (succ n₀ + K) j) * (𝔞 U * 𝔞 (Xd B dv j (succ n₀) x))) :=
    nn_mul (nn_term _) (nn_mul (nn_term _) (nn_term _))
  have r := EulerAlgebra.node_step nnCone (nn_term (succ n₀)) (nn_term (B.denAt j (succ n₀) x)) hT hM
    (Xn_succ B v j (succ n₀) x) hx i
  refine le_abs_of_bd₀ ((r.smul nnCone (nn_term (succ n₀))).congr ?_ ?_)
  · rw [e₁]; ring
  · simp only [Q.mk_mul, map_mul]
    rw [e₂, Xd_succ]; ring

end Step

/-- `lem:ode-polybound` at the nodes, graded: for `j ≤ n`, `Xd(j) > 0` and
`n^j |Xn(j)_i| ≤ (n + K)^j U Xd(j)`. -/
theorem node_inv {B : Kernel d} {v : Fin d → ZT n} {dv U K x : PTm n} (n₀ : PTm n)
    (hK : Γ ⊢[PRAAx] KBound B x K) (hdv : Γ ⊢[PRAAx] lt zero dv)
    (hv : ∀ i, Γ ⊢[PRAAx] le (abs (v i)) (U * dv)) (j : PTm n) :
    Γ ⊢[PRAAx] NodeInv B v dv U K x (succ n₀) j := by
  have hall : Γ ⊢[PRAAx] Fm.all (NodeInv B (fun l => zshift (v l)) (Syn.shift dv) (Syn.shift U) (Syn.shift K)
      (Syn.shift x) (succ (Syn.shift n₀)) (var 0)) := by
    ipra_qfind (NodeInv_QF _ _ _ _ _ _ _ _) [subst_NodeInv, zshift_inst, zshift_repl]
    · obtain ⟨a, b⟩ := node_inv_base (B := B) (K := K) (x := x) (n₀ := n₀) hdv hv
      exact .impI (.andI a.wk (conjFin_intro fun i => (b i).wk))
    · refine .impI ?_
      have hj : (le (succ (var 0)) (succ (Syn.shift n₀)) ::
          NodeInv B (fun l => zshift (v l)) (Syn.shift dv) (Syn.shift U) (Syn.shift K) (Syn.shift x)
            (succ (Syn.shift n₀)) (var 0) :: Γ.map Fm.shift) ⊢[PRAAx]
          le (succ (var 0)) (succ (Syn.shift n₀)) := Prf.hyp0
      have ih := Prf.impE (φ := le (var 0) (succ (Syn.shift n₀))) Prf.hyp1 (le_trans (le_succ_self _) hj)
      obtain ⟨a, b⟩ := node_inv_step (U := Syn.shift U) (kbound_shift hK).wk.wk hj (.andE₁ ih)
        (conjFin_elim (.andE₂ ih))
      exact .andI a (conjFin_intro b)
  have h := Prf.allE j hall
  simp only [subst_NodeInv, zshift_inst, Syn.subst_inst_shift, Syn.subst_var, Syn.inst_zero,
    ConciseIPRA.PTm.subst_succ] at h
  exact h

section Bounds

variable {B : Kernel d} {v : Fin d → ZT n} {dv U K x n₀ j : PTm n}

/-- The denominators of the Euler array are positive. -/
theorem Xd_pos (hK : Γ ⊢[PRAAx] KBound B x K) (hdv : Γ ⊢[PRAAx] lt zero dv)
    (hj : Γ ⊢[PRAAx] le j (succ n₀)) : Γ ⊢[PRAAx] lt zero (Xd B dv j (succ n₀) x) :=
  .andE₁ (Prf.impE (node_inv (v := fun _ : Fin d => ZT.natLit 0) (U := zero) n₀ hK hdv
    (fun _ => abs_zero_le _) j) hj)

/-- `lem:ode-polybound` at the nodes: `‖X_{n,j}‖ ≤ 3^K U` for `j ≤ n`. -/
theorem euler_node_bound (hK : Γ ⊢[PRAAx] KBound B x K) (hdv : Γ ⊢[PRAAx] lt zero dv)
    (hv : ∀ i, Γ ⊢[PRAAx] le (abs (v i)) (U * dv)) (hj : Γ ⊢[PRAAx] le j (succ n₀)) (i : Fin d) :
    Γ ⊢[PRAAx] le (abs (Xn B v j (succ n₀) x i)) (pw (num 3) K * U * Xd B dv j (succ n₀) x) := by
  have h := conjFin_elim (.andE₂ (Prf.impE (node_inv n₀ hK hdv hv j) hj)) i
  have g := growth_le (k₀ := n₀) (A := K) (eq_add_of_le hj).eqSymm
  have hpos := pw_pos' (Γ := Γ) (p := succ n₀) (congrSucc (pred_succ n₀).eqSymm) j
  refine mul_le_cancel (d' := pred (pw (succ n₀) j))
    (le_congr (congrMul hpos (.eqRefl _)) (congrMul hpos (.eqRefl _)) ?_)
  ipra_le sl h + sl g * (𝔞 U * 𝔞 (Xd B dv j (succ n₀) x))

/-- `lem:ode-polybound` at the nodes, for the maximum norm of the numerator vector:
`‖Xn(j)‖ ≤ 3^K U Xd(j)` for `j ≤ n`. -/
theorem euler_node_norm (hK : Γ ⊢[PRAAx] KBound B x K) (hdv : Γ ⊢[PRAAx] lt zero dv)
    (hv : ∀ i, Γ ⊢[PRAAx] le (abs (v i)) (U * dv)) (hj : Γ ⊢[PRAAx] le j (succ n₀)) :
    Γ ⊢[PRAAx] le (nrm fun i => Xn B v j (succ n₀) x i) (pw (num 3) K * U * Xd B dv j (succ n₀) x) :=
  nrm_le fun i => euler_node_bound hK hdv hv hj i

end Bounds

end LeanProofs.IPRA.Analysis.EulerNodeBound
