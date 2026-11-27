import IPRADerivations.Foundations.MixedRadixGrid

/-!
# Limits of finite diagrams of finite sets (`ipra_categorical_methods`, "Finite limits, including equalizers and pullbacks")

Packet: `foundations/ipra_categorical_methods`, Section 4: "A finite diagram is a finite table
category `J` and a table functor `D` assigning the finite set `[d_i]` to each object `i` and a
function table `D(a)` to each arrow `a : i → j`. List all tuples `x = (x_i)`, `x_i < d_i`, whose
ambient number is `P = ∏_i d_i` ... Retain a tuple exactly when every arrow satisfies
`D(a)(x_i) = x_j` (L). Let `L` be the increasing list of retained tuple codes. Its size is a PR
number `ℓ ≤ P` ... Coordinate selection gives a cone `p_i : [ℓ] → [d_i]`. For any cone
`q_i : [z] → [d_i]` and `t < z`, the tuple `(q_i(t))_i` satisfies (L), by the cone equations.
Its rank in `L` therefore defines a table `u : [z] → [ℓ]`. Then `p_i u = q_i` for every `i`. If
`v` also has these projection equations, ... finite tuple extensionality and injectivity of
ranking give `v(t) = u(t)`."

`Foundations/FilteredEnumeration` has the rank/select list of a retained subset and the case of
equalizers. Here the diagram is arbitrary: `r` objects with sizes `B_i` (terms) and `m` arrows
`src e → tgt e` with function terms `f_e(·, y)` (`r`, `m`, `src`, `tgt` are parameters of the
Lean statements; each instance is one iPRA derivation). Tuples are the mixed-radix codes of
`Foundations/MixedRadixGrid`. The retention test `K(n, y)` is a parameter with its two
defining properties as hypotheses: `K(n, y) ≠ 0` exactly when the digits of `n` satisfy (L).

* `code_congr`: equal digit tuples have equal codes (finite tuple extensionality);
* `proj K B y i j`: the cone `p_i(j)`, the `i`-th digit of the `j`-th retained code;
* `proj_lt`, `proj_compat`: the cone lands in `[B_i]` and satisfies (L) on every arrow;
* `factor_lt`, `factor_proj`: for a compatible tuple `c` (a value of a cone `q`), the mediator
  `u = rank K (code B c) y` is below `ℓ` and `p_i(u) = c_i` for every `i`;
* `limit_unique`: any `v < ℓ` with `p_i(v) = c_i` for every `i` equals that mediator.

For the empty diagram (`r = 0`, `m = 0`) the product is `1` and the limit is `[1]` when the
test retains the code `0`. A cospan is `r = 3`, `m = 2`: pullbacks. Not derived: the test `K` as
a term built from the arrow tables (a product of equality bits over the arrows), and finite
colimits by bounded equivalence closure for a general diagram (the coequalizer is
`Foundations/FiniteCoequalizer`).
-/

namespace LeanProofs.IPRA.Foundations.FiniteLimits

open_ipra exports
open LeanProofs.IPRA.Foundations.MixedRadixGrid
  (prodT code dig code_lt dig_congr dig_code dig_lt code_dig grid_complete)
open LeanProofs.IPRA.Foundations.FilteredEnumeration (rank sel sel_spec)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-- Finite tuple extensionality: equal digits give equal codes. -/
theorem code_congr : {r : ℕ} → (B : Fin r → PTm k) → {d d' : Fin r → PTm k} →
    (∀ i, Γ ⊢[PRAAx] d i ≐ d' i) → (Γ ⊢[PRAAx] code B d ≐ code B d')
  | 0, _, _, _, _ => .eqRefl _
  | _ + 1, B, _, _, h =>
    congrAdd (congrMul (code_congr (fun i => B i.succ) fun i => h i.succ) (.eqRefl _)) (h 0)

section Limit

variable {r m : ℕ} (K : PTm 2) (B : Fin r → PTm k) (y : PTm k)
variable (src tgt : Fin m → Fin r) (f : Fin m → PTm 2)

/-- The cone: `p_i(j)` is the `i`-th coordinate of the `j`-th retained tuple. -/
abbrev proj (i : Fin r) (j : PTm k) : PTm k := dig B (sel K j (prodT B) y) i

/-- The cone lands in the objects of the diagram. -/
theorem proj_lt (hB : ∀ i, Γ ⊢[PRAAx] B i ≐ succ (pred (B i))) (i : Fin r) (j : PTm k) :
    Γ ⊢[PRAAx] lt (proj K B y i j) (B i) :=
  dig_lt hB _ i

/-- The cone equations (L): `D(a)(p_i(j)) = p_{i'}(j)` for every arrow `a : i → i'`. -/
theorem proj_compat
    (hs : ∀ n : PTm k, (Γ ⊢[PRAAx] neg (inst2 K n y ≐ zero)) →
      ∀ e, Γ ⊢[PRAAx] inst2 (f e) (dig B n (src e)) y ≐ dig B n (tgt e))
    {j : PTm k} (hj : Γ ⊢[PRAAx] lt j (rank K (prodT B) y)) (e : Fin m) :
    Γ ⊢[PRAAx] inst2 (f e) (proj K B y (src e) j) y ≐ proj K B y (tgt e) j :=
  hs _ (Prf.andE₁ (Prf.andE₂ (sel_spec K hj))) e

/-- A compatible tuple is retained. -/
theorem compat_kept
    (hc : ∀ n : PTm k, (∀ e, Γ ⊢[PRAAx] inst2 (f e) (dig B n (src e)) y ≐ dig B n (tgt e)) →
      (Γ ⊢[PRAAx] neg (inst2 K n y ≐ zero)))
    (hB : ∀ i, Γ ⊢[PRAAx] B i ≐ succ (pred (B i))) {c : Fin r → PTm k}
    (hlt : ∀ i, Γ ⊢[PRAAx] lt (c i) (B i))
    (hcomp : ∀ e, Γ ⊢[PRAAx] inst2 (f e) (c (src e)) y ≐ c (tgt e)) :
    Γ ⊢[PRAAx] neg (inst2 K (code B c) y ≐ zero) :=
  hc _ fun e =>
    (congrInst2 (f e) (dig_code hB hlt (src e)) (.eqRefl y)).eqTrans
      ((hcomp e).eqTrans (dig_code hB hlt (tgt e)).eqSymm)

/-- The mediator of a cone value is an index of the limit. -/
theorem factor_lt
    (hc : ∀ n : PTm k, (∀ e, Γ ⊢[PRAAx] inst2 (f e) (dig B n (src e)) y ≐ dig B n (tgt e)) →
      (Γ ⊢[PRAAx] neg (inst2 K n y ≐ zero)))
    (hB : ∀ i, Γ ⊢[PRAAx] B i ≐ succ (pred (B i))) {c : Fin r → PTm k}
    (hlt : ∀ i, Γ ⊢[PRAAx] lt (c i) (B i))
    (hcomp : ∀ e, Γ ⊢[PRAAx] inst2 (f e) (c (src e)) y ≐ c (tgt e)) :
    Γ ⊢[PRAAx] lt (rank K (code B c) y) (rank K (prodT B) y) :=
  Prf.andE₁ (grid_complete K hlt (compat_kept K B y src tgt f hc hB hlt hcomp))

/-- The factorization: `p_i(u) = c_i` for the mediator `u`. -/
theorem factor_proj
    (hc : ∀ n : PTm k, (∀ e, Γ ⊢[PRAAx] inst2 (f e) (dig B n (src e)) y ≐ dig B n (tgt e)) →
      (Γ ⊢[PRAAx] neg (inst2 K n y ≐ zero)))
    (hB : ∀ i, Γ ⊢[PRAAx] B i ≐ succ (pred (B i))) {c : Fin r → PTm k}
    (hlt : ∀ i, Γ ⊢[PRAAx] lt (c i) (B i))
    (hcomp : ∀ e, Γ ⊢[PRAAx] inst2 (f e) (c (src e)) y ≐ c (tgt e)) (i : Fin r) :
    Γ ⊢[PRAAx] proj K B y i (rank K (code B c) y) ≐ c i :=
  (dig_congr B
    (Prf.andE₂ (grid_complete K hlt (compat_kept K B y src tgt f hc hB hlt hcomp))) i).eqTrans
    (dig_code hB hlt i)

/-- Uniqueness of the mediator: an index of the limit with the same projections is the rank of
the tuple. -/
theorem limit_unique (hB : ∀ i, Γ ⊢[PRAAx] B i ≐ succ (pred (B i))) {c : Fin r → PTm k}
    {v : PTm k} (hv : Γ ⊢[PRAAx] lt v (rank K (prodT B) y))
    (hp : ∀ i, Γ ⊢[PRAAx] proj K B y i v ≐ c i) :
    Γ ⊢[PRAAx] v ≐ rank K (code B c) y := by
  have s := sel_spec K hv
  have e : Γ ⊢[PRAAx] sel K v (prodT B) y ≐ code B c :=
    (code_dig hB (Prf.andE₁ s)).eqSymm.eqTrans (code_congr B hp)
  exact (Prf.andE₂ (Prf.andE₂ s)).eqSymm.eqTrans (congrAp2 (sumF (sgB K)) e (.eqRefl _))

end Limit

end LeanProofs.IPRA.Foundations.FiniteLimits
