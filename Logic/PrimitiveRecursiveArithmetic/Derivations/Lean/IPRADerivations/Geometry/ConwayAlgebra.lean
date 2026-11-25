import IPRADerivations.Core.Tactic
import IPRADerivations.Core.Gcd
import IPRADerivations.Core.Parity
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas

/-!
# The affine and area algebra of the Conway criterion

Packet: `geometry/conway_criterion_ipra_2026-11-16` (Sections 2 and 4: `lem:halfturnalgebra`,
the edge identities behind `lem:Jlaws`, `lem:Jcentral` and the algebra of `thm:periodarea`).
Points have two integer coordinates; an integer is a formal difference of two naturals (`ZT`).
A half-turn about the doubled centre `s` is `x ↦ s − x`, a translation is `x ↦ x + w`, and
`det(x, y) = x₁ y₂ − x₂ y₁`.

Closed identities (universally quantified over all coordinates):

* `half_inv`, `half_half`, `half_trans` (`lem:halfturnalgebra`): `s − (s − x) = x`,
  `q − (p − x) = x + (q − p)`, `p − (x + w) = (p − x) − w`;
* `det_translate`, `det_half`: the contribution of one edge `(a, b)` to the shoelace sum under a
  translation and under a half-turn,
  `det(a + w, b + w) = det(a, b) + det(w, b − a)` and
  `det(s − a, s − b) = det(a, b) + det(s, a − b)`;
* `det_sym`: `det(X + Y, X − Y) = −2 det(X, Y)`;
* `period_area`: with `D = B + t`, `E = A + t` and `u = E + F − B − C`,
  `det(t, u) = det(B, C) + det(C, D) + det(E, F) + det(F, A) − det(t, B − A)`.

Rules, for arbitrary integer terms:

* `zt_cancel_two`: `u + u = v + v` gives `u = v`;
* `central_path` (`lem:Jcentral`): an integer `J` with `−J = J + det(X + Y, X − Y)` equals
  `det(X, Y)`; this is the shoelace sum of a centrally symmetric path from `X` to `Y`;
* `period_area_paths` (`thm:periodarea`): from the five path relations
  `J_a + J_d = −det(t, B − A)`, `J_b = det(B, C)`, `J_c = det(C, D)`, `J_e = det(E, F)` and
  `J_f = det(F, A)`, the boundary sum `J_a + ⋯ + J_f` equals `det(t, u)`.

The sums over the vertices of a path, and the torus argument of the packet, are not formalized
here.
-/

namespace LeanProofs.IPRA.Geometry.ConwayAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

/-- `det((x₁, x₂), (y₁, y₂)) = x₁ y₂ − x₂ y₁`. -/
abbrev det {n : ℕ} (x₁ x₂ y₁ y₂ : ZT n) : ZT n := x₁ * y₂ - x₂ * y₁

/-! ## Three points -/

section Three

abbrev a₁ : ZT 12 := .var2 0 1
abbrev a₂ : ZT 12 := .var2 2 3
abbrev b₁ : ZT 12 := .var2 4 5
abbrev b₂ : ZT 12 := .var2 6 7
abbrev c₁ : ZT 12 := .var2 8 9
abbrev c₂ : ZT 12 := .var2 10 11

/-- `a − (a − c) = c`. -/
def halfInvFormula : Fm PTm 12 := ZT.eq (a₁ - (a₁ - c₁)) c₁ ⋏ ZT.eq (a₂ - (a₂ - c₂)) c₂

/-- `b − (a − c) = c + (b − a)`. -/
def halfHalfFormula : Fm PTm 12 :=
  ZT.eq (b₁ - (a₁ - c₁)) (c₁ + (b₁ - a₁)) ⋏ ZT.eq (b₂ - (a₂ - c₂)) (c₂ + (b₂ - a₂))

/-- `a − (c + b) = (a − c) − b`. -/
def halfTransFormula : Fm PTm 12 :=
  ZT.eq (a₁ - (c₁ + b₁)) ((a₁ - c₁) - b₁) ⋏ ZT.eq (a₂ - (c₂ + b₂)) ((a₂ - c₂) - b₂)

/-- `det(a + c, b + c) = det(a, b) + det(c, b − a)`. -/
def detTranslateFormula : Fm PTm 12 :=
  ZT.eq (det (a₁ + c₁) (a₂ + c₂) (b₁ + c₁) (b₂ + c₂)) (det a₁ a₂ b₁ b₂ + det c₁ c₂ (b₁ - a₁) (b₂ - a₂))

/-- `det(c − a, c − b) = det(a, b) + det(c, a − b)`. -/
def detHalfFormula : Fm PTm 12 :=
  ZT.eq (det (c₁ - a₁) (c₂ - a₂) (c₁ - b₁) (c₂ - b₂)) (det a₁ a₂ b₁ b₂ + det c₁ c₂ (a₁ - b₁) (a₂ - b₂))

/-- `det(a + b, a − b) = −2 det(a, b)`. -/
def detSymFormula : Fm PTm 12 :=
  ZT.eq (det (a₁ + b₁) (a₂ + b₂) (a₁ - b₁) (a₂ - b₂)) (-(ZT.natLit 2 * det a₁ a₂ b₁ b₂))

theorem half_inv_open : ([] : List (Fm PTm 12)) ⊢[PRAAx] halfInvFormula := by
  unfold halfInvFormula; exact .andI (by ipra_ring) (by ipra_ring)

theorem half_half_open : ([] : List (Fm PTm 12)) ⊢[PRAAx] halfHalfFormula := by
  unfold halfHalfFormula; exact .andI (by ipra_ring) (by ipra_ring)

theorem half_trans_open : ([] : List (Fm PTm 12)) ⊢[PRAAx] halfTransFormula := by
  unfold halfTransFormula; exact .andI (by ipra_ring) (by ipra_ring)

theorem det_translate_open : ([] : List (Fm PTm 12)) ⊢[PRAAx] detTranslateFormula := by
  unfold detTranslateFormula; ipra_ring

theorem det_half_open : ([] : List (Fm PTm 12)) ⊢[PRAAx] detHalfFormula := by
  unfold detHalfFormula; ipra_ring

theorem det_sym_open : ([] : List (Fm PTm 12)) ⊢[PRAAx] detSymFormula := by
  unfold detSymFormula; ipra_ring

/-- A half-turn is an involution. -/
theorem half_inv : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 12 halfInvFormula := closeAll 12 half_inv_open

/-- Two half-turns compose to the translation by the difference of the doubled centres. -/
theorem half_half : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 12 halfHalfFormula := closeAll 12 half_half_open

/-- A half-turn conjugates a translation to the opposite translation. -/
theorem half_trans : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 12 halfTransFormula := closeAll 12 half_trans_open

/-- The shoelace term of an edge under a translation. -/
theorem det_translate : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 12 detTranslateFormula :=
  closeAll 12 det_translate_open

/-- The shoelace term of an edge under a half-turn. -/
theorem det_half : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 12 detHalfFormula := closeAll 12 det_half_open

theorem det_sym : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 12 detSymFormula := closeAll 12 det_sym_open

end Three

/-! ## The period–area identity -/

section Period

abbrev A₁ : ZT 20 := .var2 0 1
abbrev A₂ : ZT 20 := .var2 2 3
abbrev B₁ : ZT 20 := .var2 4 5
abbrev B₂ : ZT 20 := .var2 6 7
abbrev C₁ : ZT 20 := .var2 8 9
abbrev C₂ : ZT 20 := .var2 10 11
abbrev F₁ : ZT 20 := .var2 12 13
abbrev F₂ : ZT 20 := .var2 14 15
abbrev t₁ : ZT 20 := .var2 16 17
abbrev t₂ : ZT 20 := .var2 18 19

abbrev D₁ : ZT 20 := B₁ + t₁
abbrev D₂ : ZT 20 := B₂ + t₂
abbrev E₁ : ZT 20 := A₁ + t₁
abbrev E₂ : ZT 20 := A₂ + t₂
abbrev u₁ : ZT 20 := E₁ + F₁ - B₁ - C₁
abbrev u₂ : ZT 20 := E₂ + F₂ - B₂ - C₂

/-- `det(t, u) = det(B, C) + det(C, D) + det(E, F) + det(F, A) − det(t, B − A)`. -/
def periodAreaFormula : Fm PTm 20 :=
  ZT.eq (det t₁ t₂ u₁ u₂)
    (det B₁ B₂ C₁ C₂ + det C₁ C₂ D₁ D₂ + det E₁ E₂ F₁ F₂ + det F₁ F₂ A₁ A₂ - det t₁ t₂ (B₁ - A₁) (B₂ - A₂))

/-- The doubled centres `p = B + C`, `q = C + D`, `r = E + F`, `s = F + A` satisfy `q = p + t`,
`r = s + t`, and `u = r − p`. -/
def centresFormula : Fm PTm 20 :=
  (ZT.eq (C₁ + D₁) ((B₁ + C₁) + t₁) ⋏ ZT.eq (C₂ + D₂) ((B₂ + C₂) + t₂)) ⋏
    ((ZT.eq (E₁ + F₁) ((F₁ + A₁) + t₁) ⋏ ZT.eq (E₂ + F₂) ((F₂ + A₂) + t₂)) ⋏
      (ZT.eq u₁ ((E₁ + F₁) - (B₁ + C₁)) ⋏ ZT.eq u₂ ((E₂ + F₂) - (B₂ + C₂))))

theorem period_area_open : ([] : List (Fm PTm 20)) ⊢[PRAAx] periodAreaFormula := by
  unfold periodAreaFormula; ipra_ring

theorem centres_open : ([] : List (Fm PTm 20)) ⊢[PRAAx] centresFormula := by
  unfold centresFormula
  exact .andI (.andI (by ipra_ring) (by ipra_ring))
    (.andI (.andI (by ipra_ring) (by ipra_ring)) (.andI (by ipra_ring) (by ipra_ring)))

theorem period_area : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 20 periodAreaFormula := closeAll 20 period_area_open

theorem centres : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 20 centresFormula := closeAll 20 centres_open

end Period

/-! ## Rules for arbitrary integer terms -/

section Rules

variable {n : ℕ} {Γ : List (Fm PTm n)}

alias cancel_two_nat := Common.two_mul_cancel

/-- `u + u = v + v` gives `u = v`. -/
theorem zt_cancel_two {u v : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (u + u) (v + v)) : Γ ⊢[PRAAx] ZT.eq u v := by
  have h' : Γ ⊢[PRAAx] (u.pos + u.pos) + (v.neg + v.neg) ≐ (v.pos + v.pos) + (u.neg + u.neg) := h
  have d : Γ ⊢[PRAAx] two * (u.pos + v.neg) ≐ two * (v.pos + u.neg) := by
    ipra_lc natEq h'
  exact cancel_two_nat d

/-- `lem:Jcentral`: an integer `J` with `−J = J + det(X + Y, X − Y)` equals `det(X, Y)`. -/
theorem central_path {J X₁ X₂ Y₁ Y₂ : ZT n}
    (h : Γ ⊢[PRAAx] ZT.eq (-J) (J + det (X₁ + Y₁) (X₂ + Y₂) (X₁ - Y₁) (X₂ - Y₂))) :
    Γ ⊢[PRAAx] ZT.eq J (det X₁ X₂ Y₁ Y₂) := by
  refine zt_cancel_two (ZT.derive ?_)
  have e := ZT.toZ_eq h
  ipra_simps
  linear_combination -e

/-- `thm:periodarea`: the boundary shoelace sum of a Conway datum is `det(t, u)`. -/
theorem period_area_paths {Ja Jb Jc Jd Je Jf P₁ P₂ Q₁ Q₂ R₁ R₂ S₁ S₂ w₁ w₂ : ZT n}
    (had : Γ ⊢[PRAAx] ZT.eq (Ja + Jd) (-(det w₁ w₂ (Q₁ - P₁) (Q₂ - P₂))))
    (hb : Γ ⊢[PRAAx] ZT.eq Jb (det Q₁ Q₂ R₁ R₂))
    (hc : Γ ⊢[PRAAx] ZT.eq Jc (det R₁ R₂ (Q₁ + w₁) (Q₂ + w₂)))
    (he : Γ ⊢[PRAAx] ZT.eq Je (det (P₁ + w₁) (P₂ + w₂) S₁ S₂))
    (hf : Γ ⊢[PRAAx] ZT.eq Jf (det S₁ S₂ P₁ P₂)) :
    Γ ⊢[PRAAx] ZT.eq (Ja + Jb + Jc + Jd + Je + Jf)
      (det w₁ w₂ (P₁ + w₁ + S₁ - Q₁ - R₁) (P₂ + w₂ + S₂ - Q₂ - R₂)) := by
  ipra_lc ZT.toZ_eq had + ZT.toZ_eq hb + ZT.toZ_eq hc + ZT.toZ_eq he + ZT.toZ_eq hf

end Rules

end LeanProofs.IPRA.Geometry.ConwayAlgebra
