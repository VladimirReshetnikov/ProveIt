import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.Core.ProdLemmas

/-!
# Elimination of a bounded auxiliary choice (`ipra_resources_and_elimination_2026-11-15`, `thm:exhaustive`, `prop:singleton`)

Packet: `foundations/ipra_resources_and_elimination_2026-11-15`, Section 6.

`thm:exhaustive`: "Suppose iPRA proves, for every good candidate,
`Good(a, c) ⟶ (p ∈ L(a, c) ⟷ R(a, c, p))`. Suppose also that it proves the pointwise coverage
assertion `P(a, p) ⟶ ∃ c ≤ B(a) (Good(a, c) ∧ R(a, c, p))`. Then a fixed PR program produces a
... complete list of all `p` satisfying `P(a, p)` ... No chosen function sending `p` to a
candidate `c` is required." Proof: "given `P(a, p)`, eliminate the existential ... Its witness
is an enumerated good candidate, and the candidate-completeness theorem puts `p` into the
corresponding list."

`prop:singleton`, the part proved in iPRA: for `P(e, t)` = "machine `e` first halts at step
`t`", "if `s < t` and `P(e, s)`, then the negative earlier-halting condition in `P(e, t)` fails.
Decidable comparison of `s, t` therefore proves `P(e, s) ∧ P(e, t) ⟶ s = t`."

With the predicates as bits (terms `g`, `r`, `m` for `Good`, `R` and membership in `L`, in the
candidate and a parameter):

* `ne_mul`, `ne_of_mul_left`, `ne_of_mul_right`: a product of bits is nonzero exactly when
  both are;
* `ex_bit_mono`: a bounded existential bit transfers along a pointwise implication (the witness
  is the least one, a term: no choice);
* `exhaustive_complete`: from candidate completeness and the coverage bit, `p` belongs to the
  list of some good candidate `c ≤ B`: it is in the union of the lists;
* `exhaustive_sound`: conversely a member of the union satisfies `R` for a good candidate;
* `First`, `first_unique`: for any bit `q`, two first successes of `q` coincide;
* `singleton_list`: hence a list without repetitions whose entries are all first successes has
  no two positions.

Not derived: the union list as one term with duplicates removed, and the two
non-computability statements of `prop:singleton` (they are about all total computable
procedures, not statements of iPRA).
-/

namespace LeanProofs.IPRA.Foundations.ExhaustiveWitness

open_ipra exports
open LeanProofs.IPRA.Foundations.BoundedReflection (exB wit ex_intro ex_elim ex_none)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-! ## Products of bits -/

theorem pos_of_ne {s : PTm k} (h : Γ ⊢[PRAAx] neg (s ≐ zero)) : Γ ⊢[PRAAx] s ≐ succ (pred s) :=
  .orE (zero_or_succ s) (.botE _ (.impE h.wk Prf.hyp0)) Prf.hyp0

theorem ne_mul {s t : PTm k} (hs : Γ ⊢[PRAAx] neg (s ≐ zero)) (ht : Γ ⊢[PRAAx] neg (t ≐ zero)) :
    Γ ⊢[PRAAx] neg (s * t ≐ zero) :=
  .impI (succ_ne_zero' _ ((pos_mul' (pos_of_ne hs) (pos_of_ne ht)).wk.eqSymm.eqTrans Prf.hyp0))

theorem ne_of_mul_left {s t : PTm k} (h : Γ ⊢[PRAAx] neg (s * t ≐ zero)) :
    Γ ⊢[PRAAx] neg (s ≐ zero) :=
  .impI (.impE h.wk ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)))

theorem ne_of_mul_right {s t : PTm k} (h : Γ ⊢[PRAAx] neg (s * t ≐ zero)) :
    Γ ⊢[PRAAx] neg (t ≐ zero) :=
  .impI (.impE h.wk ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)))

/-! ## Bounded existential bits -/

/-- A bounded existential bit transfers along a pointwise implication. -/
theorem ex_bit_mono (f f' : PTm 2) {N y : PTm k}
    (hp : ∀ c : PTm k, (Γ ⊢[PRAAx] lt c N) → (Γ ⊢[PRAAx] neg (inst2 f c y ≐ zero)) →
      (Γ ⊢[PRAAx] neg (inst2 f' c y ≐ zero)))
    (h : Γ ⊢[PRAAx] exB f N y ≐ one) : Γ ⊢[PRAAx] exB f' N y ≐ one :=
  ex_intro f' (hp _ (Prf.andE₁ (ex_elim f h)) (Prf.andE₂ (ex_elim f h))) (Prf.andE₁ (ex_elim f h))

section Exhaustive

variable (g r m : PTm 2)

/-- The bit `[Good(a, c) ∧ R(a, c, p)]`. -/
def goodR : PTm 2 := g * r

/-- The bit `[Good(a, c) ∧ p ∈ L(a, c)]`. -/
def goodM : PTm 2 := g * m

theorem goodR_at (c y : PTm k) : inst2 (goodR g r) c y = inst2 g c y * inst2 r c y := by
  simp [inst2, goodR]

theorem goodM_at (c y : PTm k) : inst2 (goodM g m) c y = inst2 g c y * inst2 m c y := by
  simp [inst2, goodM]

/-- `thm:exhaustive`, completeness: under the coverage assertion, `p` lies in the list of a good
candidate below the bound. -/
theorem exhaustive_complete {B y : PTm k}
    (hcand : ∀ c : PTm k, (Γ ⊢[PRAAx] neg (inst2 g c y ≐ zero)) →
      (Γ ⊢[PRAAx] neg (inst2 r c y ≐ zero)) → (Γ ⊢[PRAAx] neg (inst2 m c y ≐ zero)))
    (hcover : Γ ⊢[PRAAx] exB (goodR g r) (succ B) y ≐ one) :
    Γ ⊢[PRAAx] exB (goodM g m) (succ B) y ≐ one := by
  refine ex_bit_mono (goodR g r) (goodM g m) (fun c _ h => ?_) hcover
  rw [goodR_at] at h
  rw [goodM_at]
  exact ne_mul (ne_of_mul_left h) (hcand c (ne_of_mul_left h) (ne_of_mul_right h))

/-- `thm:exhaustive`, soundness: a member of the union of the lists satisfies `R` for a good
candidate below the bound. -/
theorem exhaustive_sound {B y : PTm k}
    (hcand : ∀ c : PTm k, (Γ ⊢[PRAAx] neg (inst2 g c y ≐ zero)) →
      (Γ ⊢[PRAAx] neg (inst2 m c y ≐ zero)) → (Γ ⊢[PRAAx] neg (inst2 r c y ≐ zero)))
    (hmem : Γ ⊢[PRAAx] exB (goodM g m) (succ B) y ≐ one) :
    Γ ⊢[PRAAx] exB (goodR g r) (succ B) y ≐ one := by
  refine ex_bit_mono (goodM g m) (goodR g r) (fun c _ h => ?_) hmem
  rw [goodM_at] at h
  rw [goodR_at]
  exact ne_mul (ne_of_mul_left h) (hcand c (ne_of_mul_left h) (ne_of_mul_right h))

end Exhaustive

/-! ## First successes are unique -/

section First

variable (q : PTm 2)

/-- `t` is the first success of `q`: `q(t) ≠ 0` and there is no success below `t`. -/
def First (t y : PTm k) : Fm PTm k := neg (inst2 q t y ≐ zero) ⋏ (exB q t y ≐ zero)

/-- `prop:singleton`: `P(e, s) ∧ P(e, t) ⟶ s = t` for the first-success predicate. -/
theorem first_unique {s t y : PTm k} (hs : Γ ⊢[PRAAx] First q s y)
    (ht : Γ ⊢[PRAAx] First q t y) : Γ ⊢[PRAAx] s ≐ t := by
  refine .orE (lt_or_le s t) ?_ ?_
  · exact .botE _ (.impE (Prf.andE₁ hs).wk (ex_none q (Prf.andE₂ ht).wk Prf.hyp0))
  · refine .orE (lt_or_eq_of_le Prf.hyp0) ?_ (Prf.eqSymm Prf.hyp0)
    exact .botE _ (.impE (Prf.andE₁ ht).wk.wk (ex_none q (Prf.andE₂ hs).wk.wk Prf.hyp0))

/-- A list without repetitions whose entries are first successes has no two positions. -/
theorem singleton_list {l₀ l₁ y : PTm k} (h₀ : Γ ⊢[PRAAx] First q l₀ y)
    (h₁ : Γ ⊢[PRAAx] First q l₁ y) (hd : Γ ⊢[PRAAx] neg (l₀ ≐ l₁)) : Γ ⊢[PRAAx] Fm.bot :=
  .impE hd (first_unique q h₀ h₁)

end First

end LeanProofs.IPRA.Foundations.ExhaustiveWitness
