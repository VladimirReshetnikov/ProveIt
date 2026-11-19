import IPRADerivations.Foundations.WindowStability
import IPRADerivations.Foundations.ApproximateWitness

/-!
# The represented finite window: the selected endpoints

Packet: `foundations/ipra_framework`, `paper/sections/05_metastability.tex`, Theorem `thm:real-window`
("Represented finite-window stability"), the estimate of its proof: with `j` the first index minimizing
the rational differences of the endpoint observations and `Δ` the minimum,

`K Δ ≤ a_K − a_0`, and "the true increase across the selected endpoints is at most
`s_{n_{j+1}} − s_{n_j} ≤ Δ + 2δ`".

Values are numerators over a common denominator: `a_i` the observations, `s_i` the true values at the
candidate starts, `|a_i − s_i| ≤ δ`. The differences are shifted by `c = 2δ` so that they are natural
numbers, `d_i = a_{i+1} + c − a_i` (`Foundations/WindowStability`), and `j = argmin d` is the selected
index (`Foundations/ApproximateWitness`).

* `selected_increase`: with `K = K′ + 1` differences,
  `K s_{j+1} + a_0 ≤ K s_j + a_K + K c`, i.e. `K (s_{j+1} − s_j) ≤ (a_K − a_0) + 2Kδ`: the true increase
  across the selected endpoints is at most the average observed increase plus `2δ`.

The observations at the two selected endpoints are the only instances of the approximation hypothesis
that are used. The candidate starts, the choice of `K` against the bound `B` and the final margin are
arithmetic of the application.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.RealWindow

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.FiniteLaws (Mn)
open LeanProofs.IPRA.Foundations.ApproximateWitness (argmin argmin_spec)
open LeanProofs.IPRA.Foundations.WindowStability (min_gap)
open LeanProofs.IPRA.Foundations.FrontierSoundness (lt_succ_of_le')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `thm:real-window`: the true increase across the selected endpoints, multiplied by the number of
differences, is at most the total observed increase plus `2Kδ`. -/
theorem selected_increase {a d s : PTm 2} {K' x c δ : PTm n}
    (hd : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (succ K')) ⟶
      (inst2 d (var 0) (Syn.shift x) + inst2 a (var 0) (Syn.shift x) ≐
        inst2 a (succ (var 0)) (Syn.shift x) + Syn.shift c)))
    (hc : Γ ⊢[PRAAx] c ≐ δ + δ)
    (ho₁ : Γ ⊢[PRAAx] le (inst2 s (succ (argmin d K' x)) x) (inst2 a (succ (argmin d K' x)) x + δ))
    (ho₂ : Γ ⊢[PRAAx] le (inst2 a (argmin d K' x) x) (inst2 s (argmin d K' x) x + δ)) :
    Γ ⊢[PRAAx] le (succ K' * inst2 s (succ (argmin d K' x)) x + inst2 a zero x)
      (succ K' * inst2 s (argmin d K' x) x + inst2 a (succ K') x + succ K' * c) := by
  have mg := min_gap hd
  have spec := argmin_spec (Γ := Γ) d K' x
  have inc := Prf.allE (argmin d K' x) hd
  simp only [Fm.subst_imp, Fm.subst_eq, subst_lt, subst_inst2, PTm.subst_add, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ] at inc
  have e_inc := natEq (Prf.impE inc (lt_succ_of_le' (Prf.andE₁ spec)))
  have e_spec := natEq (Prf.andE₂ spec)
  have e_c := natEq hc
  ipra_le sl mg + (𝔟 K' + 1) * (sl ho₁ + sl ho₂) using
    linear_combination (𝔟 K' + 1) * (e_inc - e_spec + e_c)

end LeanProofs.IPRA.Foundations.RealWindow
