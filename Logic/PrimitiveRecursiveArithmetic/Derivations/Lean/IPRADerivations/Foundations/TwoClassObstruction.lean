import IPRADerivations.Foundations.BoundedFormulas

/-!
# The two-class obstruction (`ipra_categorical_methods`, `thm:no-two-class-skeleton`)

Packet: `foundations/ipra_categorical_methods`, Section 7, Subsection "A uniformly decidable
two-class obstruction". For a fixed term `h(n, e)` (in the packet: `h(e, n) = 1` when machine
`e` has halted within `n` steps) put `b(n) = sg h(n, e)` and

`m E_e n ⟺ b(m) = b(n)`,

a decidable equivalence relation with at most two classes. The arithmetic content of the
subsection is derived for an arbitrary term `h`:

* `E_refl`, `E_symm`, `E_trans`: the equivalence laws;
* `three_classes`: among any three numbers two are equivalent (the counting bound; no covering
  list is included in it);
* `cover_decides`: let `h` be persistent (`Persistent`: `h(n, e) = 0` and `m ≤ n` give
  `h(m, e) = 0`, that is, a halted machine stays halted). If `t` is equivalent to some `a ≤ H`
  and `h(H, e) = 0`, then `h(t, e) = 0`;
* `never_halts`: hence, if every `t` is equivalent to some object below `H` (a finite list of
  representatives with largest entry `H` meets every class) and `h(H, e) = 0`, then
  `∀ t. h(t, e) = 0`: the single test `h(H, e)` decides halting.

The conclusion of the packet's theorem, that no computable procedure produces such a list
uniformly in `e`, is a statement of computability theory about the fixed simulator and is not
an iPRA sentence; it is not formalized. What is derived is the reduction it rests on.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.TwoClassObstruction

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.Foundations.BoundedReflection (sg_cases one_ne_zero)
open LeanProofs.IPRA.Foundations.BoundedFormulas (sg_of_pos sg_of_zero)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

variable {k : ℕ} {Γ : List (Fm PTm k)}

section Classes

variable (h : PTm 2)

/-- The bit `b(n) = sg h(n, e)`. -/
abbrev bit (n e : PTm k) : PTm k := sg (inst2 h n e)

/-- `m E_e n`: the bits of `m` and `n` agree. -/
abbrev E (m n e : PTm k) : Fm PTm k := bit h m e ≐ bit h n e

theorem E_refl (m e : PTm k) : Γ ⊢[PRAAx] E h m m e := .eqRefl _

theorem E_symm {m n e : PTm k} (h₁ : Γ ⊢[PRAAx] E h m n e) : Γ ⊢[PRAAx] E h n m e := h₁.eqSymm

theorem E_trans {m n p e : PTm k} (h₁ : Γ ⊢[PRAAx] E h m n e) (h₂ : Γ ⊢[PRAAx] E h n p e) :
    Γ ⊢[PRAAx] E h m p e := h₁.eqTrans h₂

private theorem same {x y c : PTm k} (hx : Γ ⊢[PRAAx] x ≐ c) (hy : Γ ⊢[PRAAx] y ≐ c) :
    Γ ⊢[PRAAx] x ≐ y := hx.eqTrans hy.eqSymm

/-- Among any three numbers, two are equivalent: there are at most two classes. -/
theorem three_classes (a b c e : PTm k) :
    Γ ⊢[PRAAx] E h a b e ⋎ (E h a c e ⋎ E h b c e) := by
  refine .orE (sg_cases (inst2 h a e)) ?_ ?_
  · refine .orE (sg_cases (inst2 h b e)) (.orI₁ (same Prf.hyp1 Prf.hyp0)) ?_
    refine .orE (sg_cases (inst2 h c e)) (.orI₂ (.orI₁ (same hyp2 Prf.hyp0))) ?_
    exact .orI₂ (.orI₂ (same Prf.hyp1 Prf.hyp0))
  · refine .orE (sg_cases (inst2 h b e)) ?_ (.orI₁ (same Prf.hyp1 Prf.hyp0))
    refine .orE (sg_cases (inst2 h c e)) (.orI₂ (.orI₂ (same Prf.hyp1 Prf.hyp0))) ?_
    exact .orI₂ (.orI₁ (same hyp2 Prf.hyp0))

/-- `sg x = 0` gives `x = 0`. -/
theorem zero_of_sg {x : PTm k} (hx : Γ ⊢[PRAAx] sg x ≐ zero) : Γ ⊢[PRAAx] x ≐ zero :=
  .orE (zero_or_succ x) Prf.hyp0 (one_ne_zero _ ((sg_of_pos Prf.hyp0).eqSymm.eqTrans hx.wk))

/-- Persistence: not halted within `n` steps gives not halted within `m ≤ n` steps. -/
structure Persistent : Prop where
  mono : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {m n e : PTm k},
    (Γ ⊢[PRAAx] le m n) → (Γ ⊢[PRAAx] inst2 h n e ≐ zero) → (Γ ⊢[PRAAx] inst2 h m e ≐ zero)

variable {h}

/-- If `t` is equivalent to some `a ≤ H` and `h(H, e) = 0`, then `h(t, e) = 0`. -/
theorem cover_decides (P : Persistent h) {H t e : PTm k}
    (hH : Γ ⊢[PRAAx] inst2 h H e ≐ zero)
    (hc : Γ ⊢[PRAAx] Fm.ex (le (var 0) (Syn.shift H) ⋏
      E h (Syn.shift t) (var 0) (Syn.shift e))) :
    Γ ⊢[PRAAx] inst2 h t e ≐ zero := by
  refine .exE hc ?_
  have e₁ : Fm.shift (inst2 h t e ≐ zero) = (inst2 h (Syn.shift t) (Syn.shift e) ≐ zero) := by
    simp [Fm.shift, Syn.shift]
  rw [e₁]
  have hH' := hH.shift
  have e₂ : Fm.shift (inst2 h H e ≐ zero) = (inst2 h (Syn.shift H) (Syn.shift e) ≐ zero) := by
    simp [Fm.shift, Syn.shift]
  rw [e₂] at hH'
  -- the representative `a = var 0` has not halted
  have ha : ((le (var 0) (Syn.shift H) ⋏ E h (Syn.shift t) (var 0) (Syn.shift e)) ::
      Γ.map Fm.shift) ⊢[PRAAx] inst2 h (var 0) (Syn.shift e) ≐ zero :=
    P.mono (Prf.andE₁ Prf.hyp0) hH'.wk
  exact zero_of_sg ((Prf.andE₂ Prf.hyp0).eqTrans (sg_of_zero ha))

/-- If every `t` is equivalent to some object below `H` and `h(H, e) = 0`, then `h(t, e) = 0`
for all `t`: the one test `h(H, e)` decides halting. -/
theorem never_halts (P : Persistent h) {H e : PTm k}
    (hH : Γ ⊢[PRAAx] inst2 h H e ≐ zero)
    (hcov : Γ ⊢[PRAAx] Fm.all (Fm.ex (le (var 0) (Syn.shift (Syn.shift H)) ⋏
      E h (Syn.shift (var 0)) (var 0) (Syn.shift (Syn.shift e))))) :
    Γ ⊢[PRAAx] Fm.all (inst2 h (var 0) (Syn.shift e) ≐ zero) := by
  refine .allI ?_
  have hH' := hH.shift
  have e₂ : Fm.shift (inst2 h H e ≐ zero) = (inst2 h (Syn.shift H) (Syn.shift e) ≐ zero) := by
    simp [Fm.shift, Syn.shift]
  rw [e₂] at hH'
  exact cover_decides P hH' hcov.allOpen

end Classes

/-! ## An instance: the threshold bit -/

/-- `h(n, e) = n ∸ e`: zero up to `e`, nonzero afterwards. -/
def thr : PTm 2 := LeanProofs.IPRA.PTm.monus (var 0) (var 1)

theorem thr_at (n e : PTm k) : inst2 thr n e = LeanProofs.IPRA.PTm.monus n e := by
  simp [inst2, thr]

/-- The threshold bit is persistent. -/
theorem thr_persistent : Persistent thr where
  mono := fun hmn hn => by
    rw [thr_at] at hn ⊢
    exact le_trans hmn hn

end LeanProofs.IPRA.Foundations.TwoClassObstruction
