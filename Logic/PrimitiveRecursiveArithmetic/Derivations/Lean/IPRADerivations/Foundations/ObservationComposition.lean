import IPRADerivations.Foundations.FiniteQueryTable
import IPRADerivations.Foundations.ReverseDemand
import IPRADerivations.Probability.UnionUtility

/-!
# Composition of finite observation contracts

Packet: `foundations/ipra_framework`, `paper/sections/03_representations.tex`, the finite observation
contract `eq:observation-contract`, `V(a, u(a, k)) → W(a, k, F(a, k))`, and Theorem
`thm:observation-composition` ("Composition of observation contracts"): if a second construction needs the
outputs `F(a, j)` for the indices of a PR finite list `J(a, k)`, and its local correctness is derived from the
bounded Boolean fold of their guarantees and a further observation `V(a, v(a, k))`, then
`U(a, k) = max(v(a, k), max_{j ∈ J(a, k)} u(a, j))` is a sufficient input horizon. "By monotonicity, the
hypothesis gives each required smaller observation. Instantiate the contract at the corresponding index,
obtain each output guarantee, and insert these derivations into the second correctness derivation."

Validity of the input at horizon `t` is a bit `V(t, a)`, the guarantee of output `j` a bit `W(j, a)`, the
list is `J(i, a)`, `i < L`. The hypotheses (`ObsData`) are rules: `V` is monotone in the horizon, and the
first contract `V(u(j)) = 1 → W(j) = 1`.

* `uJB`, `WJB` (with `inst2_uJB`, `inst2_WJB`): the resources `u(J(i))` and guarantees `W(J(i))` along the
  list; `horizon`: `U = max(v, max_{i<L} u(J(i)))` (`UnionUtility.Mx`);
* `v_le_horizon`, `comp_le_horizon`: `v ≤ U` and `u(J(i)) ≤ U` for `i < L`;
* `guarantees`: from `V(U) = 1`, the Boolean fold `∏_{i<L} W(J(i)) = 1`
  (`FiniteQueryTable.table_good`);
* `compose_obs` (`thm:observation-composition`): a second contract
  `∏_{i<L} W(J(i)) = 1 → V(v) = 1 → Out` gives `V(U) = 1 → Out`.
-/

namespace LeanProofs.IPRA.Foundations.ObservationComposition

open_ipra exports
open LeanProofs.IPRA.Foundations.FiniteQueryTable (table_good)
open LeanProofs.IPRA.Probability.UnionUtility (Mx mx_upper)
open LeanProofs.IPRA.Probability.Ninther (mx)

variable (V u W J : PTm 2)

/-- `u(J(i, a), a)`. -/
def uJB : PTm 2 := Syn.subst ![J, Syn.var 1] u

/-- `W(J(i, a), a)`. -/
def WJB : PTm 2 := Syn.subst ![J, Syn.var 1] W

theorem inst2_uJB {k : ℕ} (i a : PTm k) : inst2 (uJB u J) i a = inst2 u (inst2 J i a) a := by
  simp only [inst2, uJB, Syn.subst_subst]
  congr 1; funext t; fin_cases t <;> simp

theorem inst2_WJB {k : ℕ} (i a : PTm k) : inst2 (WJB W J) i a = inst2 W (inst2 J i a) a := by
  simp only [inst2, WJB, Syn.subst_subst]
  congr 1; funext t; fin_cases t <;> simp

/-- The horizon `U = max(v, max_{i<L} u(J(i)))`. -/
abbrev horizon {k : ℕ} (v L a : PTm k) : PTm k := mx v (Mx (uJB u J) L a)

/-- The contracts: monotonicity of the input validity and the first observation contract. -/
structure ObsData : Prop where
  mono : ∀ {k : ℕ} {Δ : List (Fm PTm k)} {s t a : PTm k},
    (Δ ⊢[PRAAx] inst2 V t a ≐ one) → (Δ ⊢[PRAAx] le s t) → (Δ ⊢[PRAAx] inst2 V s a ≐ one)
  first : ∀ {k : ℕ} {Δ : List (Fm PTm k)} {j a : PTm k},
    (Δ ⊢[PRAAx] inst2 V (inst2 u j a) a ≐ one) → (Δ ⊢[PRAAx] inst2 W j a ≐ one)

variable {V u W J}

theorem v_le_horizon {k : ℕ} {Δ : List (Fm PTm k)} (v L a : PTm k) :
    Δ ⊢[PRAAx] le v (horizon u J v L a) := le_mx_left _ _

theorem comp_le_horizon {k : ℕ} {Δ : List (Fm PTm k)} {i v L a : PTm k} (hi : Δ ⊢[PRAAx] lt i L) :
    Δ ⊢[PRAAx] le (inst2 u (inst2 J i a) a) (horizon u J v L a) := by
  have m := mx_upper (uJB u J) (x := a) hi
  rw [inst2_uJB] at m
  exact le_trans m (le_mx_right _ _)

theorem shift_horizon {k : ℕ} (v L a : PTm k) :
    Syn.shift (horizon u J v L a) = horizon u J (Syn.shift v) (Syn.shift L) (Syn.shift a) := by
  simp [Syn.shift, horizon, Mx]

/-- From `V(U) = 1`: every listed output meets its guarantee, as one Boolean fold. -/
theorem guarantees (H : ObsData V u W) {k : ℕ} {Δ : List (Fm PTm k)} {v L a : PTm k}
    (hV : Δ ⊢[PRAAx] inst2 V (horizon u J v L a) a ≐ one) :
    Δ ⊢[PRAAx] ap2 (prodF (WJB W J)) L a ≐ one := by
  refine table_good (WJB W J) (.allI (.impI ?_))
  have hV' := hV.shift
  simp only [Fm.shift, Fm.subst_eq, subst_inst2, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] at hV'
  have e : Syn.subst (fun i => Syn.var i.succ) (horizon u J v L a) =
      horizon u J (Syn.shift v) (Syn.shift L) (Syn.shift a) := shift_horizon v L a
  rw [e] at hV'
  have hi : (lt (Syn.var 0) (Syn.shift L) :: Δ.map Fm.shift) ⊢[PRAAx] lt (Syn.var 0) (Syn.shift L) := Prf.hyp0
  have c := comp_le_horizon (u := u) (J := J) (v := Syn.shift v) (a := Syn.shift a) hi
  have w := H.first (H.mono hV'.wk c)
  rw [inst2_WJB]
  exact w

/-- `thm:observation-composition`: the horizon `U` suffices for the composed contract. -/
theorem compose_obs (H : ObsData V u W) {k : ℕ} {Δ : List (Fm PTm k)} {v L a : PTm k} {Out : Fm PTm k}
    (second : Δ ⊢[PRAAx] (ap2 (prodF (WJB W J)) L a ≐ one) ⟶ (inst2 V v a ≐ one) ⟶ Out)
    (hV : Δ ⊢[PRAAx] inst2 V (horizon u J v L a) a ≐ one) : Δ ⊢[PRAAx] Out :=
  .impE (.impE second (guarantees H hV)) (H.mono hV (v_le_horizon v L a))

end LeanProofs.IPRA.Foundations.ObservationComposition
