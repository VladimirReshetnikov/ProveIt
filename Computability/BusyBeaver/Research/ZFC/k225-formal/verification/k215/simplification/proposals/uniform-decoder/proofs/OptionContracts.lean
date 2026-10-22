import Init

/-!
Generic contracts for finite proof-enumerator command blocks.

`Returns r x` means that the block halts early (`none`) or returns exactly `x`.
This is the disjunction used by EnumPerm.Contract, abstracted independently of
natural-number formula codes. In this application `none` is actual halting of
the enumerator, not divergence. The application must separately prove the
global invariant that every early halt yields a genuine refutation.

This file changes no ProveIt definitions. It supplies reusable proof rules.
-/

namespace ProofSimplification.OptionContracts

universe u v

def Returns {α : Type u} (r : Option α) (x : α) : Prop :=
  r = none ∨ r = some x

theorem returns_iff {α : Type u} {r : Option α} {x : α} :
    Returns r x ↔ ∀ y, r = some y → y = x := by
  constructor
  · intro h y hy
    cases h with
    | inl hn => rw [hn] at hy; cases hy
    | inr hx => rw [hx] at hy; cases hy; rfl
  · intro h
    cases hr : r with
    | none => exact Or.inl rfl
    | some y => exact Or.inr (congrArg some (h y hr))

theorem bind_returns {α : Type u} {β : Type v}
    {r : Option α} {x : α} {f : α → Option β} {y : β}
    (hr : Returns r x) (hf : Returns (f x) y) :
    Returns (r.bind f) y := by
  cases hr with
  | inl hn => rw [hn]; exact Or.inl rfl
  | inr hx => rw [hx]; exact hf

theorem bind_halts {α : Type u} {β : Type v}
    {r : Option α} {x : α} {f : α → Option β}
    (hr : Returns r x) (hf : f x = none) : r.bind f = none := by
  cases hr with
  | inl hn => rw [hn]; rfl
  | inr hx => rw [hx]; exact hf

section Blocks

variable {Cmd W : Type u} (step : Cmd → W → Option W)

def exec : List Cmd → W → Option W
  | [], w => some w
  | c :: cs, w => (step c w).bind (exec cs)

theorem exec_append (p q : List Cmd) (s : W) :
    exec step (p ++ q) s = (exec step p s).bind (exec step q) := by
  induction p generalizing s with
  | nil => rfl
  | cons c cs ih =>
    change (step c s).bind (exec step (cs ++ q)) =
      ((step c s).bind (exec step cs)).bind (exec step q)
    cases step c s with
    | none => rfl
    | some t => exact ih t

theorem append_returns {p q : List Cmd} {s t u : W}
    (hp : Returns (exec step p s) t) (hq : Returns (exec step q t) u) :
    Returns (exec step (p ++ q) s) u := by
  rw [exec_append]
  exact bind_returns hp hq

theorem append_halts {p q : List Cmd} {s t : W}
    (hp : Returns (exec step p s) t) (hq : exec step q t = none) :
    exec step (p ++ q) s = none := by
  rw [exec_append]
  exact bind_halts hp hq

/-- The unknown proof block is discharged once; only the concrete suffix
    needs symbolic execution. This is the shape of `gen_contract`. -/
theorem prefix_rule {p q : List Cmd} {start : W}
    {output final : W} (hp : Returns (exec step p start) output)
    (hq : exec step q output = some final) :
    Returns (exec step (p ++ q) start) final :=
  append_returns step hp (Or.inr hq)

/-- Two symbolic subproofs followed by a suffix, as in modus ponens. -/
theorem two_prefix_rule {p q tail : List Cmd} {s t u v : W}
    (hp : Returns (exec step p s) t) (hq : Returns (exec step q t) u)
    (ht : Returns (exec step tail u) v) :
    Returns (exec step (p ++ (q ++ tail)) s) v :=
  append_returns step hp (append_returns step hq ht)

end Blocks

#print axioms returns_iff
#print axioms bind_returns
#print axioms bind_halts
#print axioms exec_append
#print axioms append_returns
#print axioms append_halts
#print axioms prefix_rule
#print axioms two_prefix_rule

end ProofSimplification.OptionContracts
