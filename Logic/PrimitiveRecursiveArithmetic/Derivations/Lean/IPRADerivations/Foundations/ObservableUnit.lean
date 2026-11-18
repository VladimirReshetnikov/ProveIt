import IPRADerivations.Foundations.EigenvalueBound
import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.Core.Fubini

/-!
# The unit identity gives a nonzero coordinate (`ipra_presentations_to_witnesses`, `thm:finite-observable-image`)

Packet: `foundations/ipra_presentations_to_witnesses`, theorem `thm:finite-observable-image`,
first step of its proof: "For a fixed valid `p`, let `v = (b_1(p), …, b_D(p))`. The unit
identity implies that `v ≠ 0`: if all entries vanished, their indicated linear combination
would be zero, contradicting one."

In natural-number form, with `β_i = |b_i(p)|` and the unit identity `1 = ∑_i c_i b_i(p)` split
by sign into `∑_{i<D} cp_i β_i = ∑_{i<D} cn_i β_i + 1`:

* `sum_vanish`: if `β_i = 0` for all `i < D`, then `∑_{i<D} c_i β_i = 0`;
* `unit_seed`: the bounded search `wit β D x` (the least `i < D` with `β_i ≠ 0`) succeeds:
  `wit β D x < D` and `β_{wit} ≠ 0`. This is the constructive content of `v ≠ 0`;
* `unit_seed_pos`: `β_{wit}` is positive, so it is a seed for the list gcd of
  `Foundations/PrimitiveScaling`.

The remaining steps of the theorem are applications of `Foundations/EigenvaluePrimitive`,
`Foundations/EigenvalueBound` and `Foundations/EigenvalueGrid` to each observable; the product
of the coordinate grids and its cardinality `∏_k (2 R_k + 1)` are not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.ObservableUnit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.BoundedReflection (exB wit ex_cases ex_elim ex_none)
open LeanProofs.IPRA.Foundations.EigenvalueBound (wB inst2_wB)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

variable (c β : PTm 2)

theorem inst2_zeroB (i x : PTm k) : inst2 (zero : PTm 2) i x = zero := by simp [inst2]

/-- If every `β_i` with `i < D` vanishes, so does `∑_{i<D} c_i β_i`. -/
theorem sum_vanish {D x : PTm k} (h : Γ ⊢[PRAAx] exB β D x ≐ zero) :
    Γ ⊢[PRAAx] ap2 (sumF (wB c β)) D x ≐ zero := by
  refine (sum_congr_bounded (wB c β) (zero : PTm 2) x x D (.allI (.impI ?_))).eqTrans
    (sum_zeroB D x)
  rw [inst2_wB, inst2_zeroB]
  have h' := h.shift
  have e : Fm.shift (exB β D x ≐ zero) = (exB β (Syn.shift D) (Syn.shift x) ≐ zero) := by
    simp [Fm.shift, Syn.shift]
  rw [e] at h'
  have z := natEq (ex_none β h'.wk
    (Prf.hyp0 (Γ := Γ.map Fm.shift) (φ := lt (var 0) (Syn.shift D))))
  apply deriveNat; ipra_simps
  linear_combination 𝔞 (inst2 c (var 0) (Syn.shift x)) * z

variable (cp cn : PTm 2)

/-- The unit identity makes the bounded search for a nonzero coordinate succeed. -/
theorem unit_seed {D x : PTm k}
    (h : Γ ⊢[PRAAx] ap2 (sumF (wB cp β)) D x ≐ ap2 (sumF (wB cn β)) D x + one) :
    Γ ⊢[PRAAx] lt (wit β D x) D ⋏ neg (inst2 β (wit β D x) x ≐ zero) := by
  refine .orE (ex_cases β D x) ?_ (ex_elim β Prf.hyp0)
  have hz : ((exB β D x ≐ zero) :: Γ) ⊢[PRAAx] exB β D x ≐ zero := Prf.hyp0
  have sp := natEq (sum_vanish cp β hz)
  have sn := natEq (sum_vanish cn β hz)
  have e := natEq (h.wk (ψ := exB β D x ≐ zero))
  refine succ_ne_zero' (a := zero) _ ?_
  apply deriveNat; ipra_simps
  linear_combination sp - sn - e

/-- The coordinate found by the search is positive. -/
theorem unit_seed_pos {D x : PTm k}
    (h : Γ ⊢[PRAAx] ap2 (sumF (wB cp β)) D x ≐ ap2 (sumF (wB cn β)) D x + one) :
    Γ ⊢[PRAAx] inst2 β (wit β D x) x ≐ succ (pred (inst2 β (wit β D x) x)) :=
  .orE (zero_or_succ (inst2 β (wit β D x) x))
    (.botE _ (.impE (Prf.andE₂ (unit_seed β cp cn h)).wk Prf.hyp0)) Prf.hyp0

end LeanProofs.IPRA.Foundations.ObservableUnit
