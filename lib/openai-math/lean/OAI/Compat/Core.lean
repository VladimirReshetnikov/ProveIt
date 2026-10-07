/-
Added for ProveIt (not an upstream file; distributed with this directory under
the same Apache-2.0 license). Backport of declarations that the upstream
library uses from its newer toolchain (Lean v4.34.1, Mathlib d13f23b7) but that
are absent from this repository's Lean 4.32.0 / Mathlib v4.32.0. Statements
are the upstream ones. Delete when the toolchain is upgraded.
-/

set_option autoImplicit false

universe u

theorem ite_eq_left {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} :
    (ite c t e) = t :=
  @if_pos c h hc α t e

theorem ite_eq_right {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t e : α} :
    (ite c t e) = e :=
  @if_neg c h hnc α t e

theorem dite_eq_left {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α}
    {e : ¬ c → α} : (dite c t e) = t hc :=
  @dif_pos c h hc α t e

theorem dite_eq_right {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c → α}
    {e : ¬ c → α} : (dite c t e) = e hnc :=
  @dif_neg c h hnc α t e
