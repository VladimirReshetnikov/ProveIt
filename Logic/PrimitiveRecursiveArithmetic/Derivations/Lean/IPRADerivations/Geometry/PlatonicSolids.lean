import IPRADerivations.Core.Order

/-!
# The five Platonic solids (`platonic_solids_ipra`)

The counting part of the packet (`paper/sections/02_counting.tex`): a convex
polyhedron with `V` vertices, `E` edges and `F` faces, every face a `p`-gon and
`q` faces at every vertex, satisfies `V − E + F = 2`, `qV = 2E` and `pF = 2E`; with
`p, q ≥ 3` this forces `(p − 2)(q − 2) < 4`, so `{p, q}` is one of
`{3,3}, {3,4}, {4,3}, {3,5}, {5,3}`.

In iPRA the variables are natural numbers `V, E, F, p', q'` with `p = p' + 3` and
`q = q' + 3`, and the theorem is the implication from the three relations to the
disjunction of the five cases. The proof is the packet's: multiplying Euler's
relation by `pq` gives `E (2p + 2q) = E pq + 2pq`, which is impossible when
`pq ≥ 2p + 2q`, i.e. when `p'q' + p' + q' ≥ 3`; the remaining cases with
`p', q' ≤ 2` are checked one by one.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.PlatonicSolids

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `x < 3` gives `x = 0 ∨ x = 1 ∨ x = 2`. -/
theorem lt_three_cases {x : PTm n} (h : Γ ⊢[PRAAx] lt x (num 3)) :
    Γ ⊢[PRAAx] (x ≐ num 0) ⋎ ((x ≐ num 1) ⋎ (x ≐ num 2)) := by
  refine .orE (zero_or_succ x) (.orI₁ Prf.hyp0) ?_
  refine .orE (zero_or_succ (pred x)) ?_ ?_
  · exact .orI₂ (.orI₁ (Prf.hyp1.eqTrans (congrSucc Prf.hyp0)))
  refine .orE (zero_or_succ (pred (pred x))) ?_ ?_
  · exact .orI₂ (.orI₂ (hyp2.eqTrans (congrSucc (Prf.hyp1.eqTrans (congrSucc Prf.hyp0)))))
  · refine le_lt_absurd _ (a := num 3) (b := x) ?_ h.wk.wk.wk
    refine le_of_eq_add (d := pred (pred (pred x))) ?_
    refine hyp2.eqTrans ((congrSucc (Prf.hyp1.eqTrans (congrSucc Prf.hyp0))).eqTrans ?_)
    ipra_ring

/-- The five Schläfli symbols, as values of `p' = p − 3` and `q' = q − 3`. -/
def schlafli (a b : PTm n) : Fm PTm n :=
  ((a ≐ num 0) ⋏ (b ≐ num 0)) ⋎ (((a ≐ num 0) ⋏ (b ≐ num 1)) ⋎ (((a ≐ num 1) ⋏ (b ≐ num 0)) ⋎
    (((a ≐ num 0) ⋏ (b ≐ num 2)) ⋎ ((a ≐ num 2) ⋏ (b ≐ num 0)))))

/-- A case `a = c₁`, `b = c₂` with `c₁ c₂ + c₁ + c₂ ≥ 3` contradicts `ab + a + b < 3`. -/
private theorem exclude {Θ : List (Fm PTm n)} {a b : PTm n} (c₁ c₂ k : ℕ)
    (hk : c₁ * c₂ + c₁ + c₂ = 3 + k) (ha : Θ ⊢[PRAAx] a ≐ num c₁) (hb : Θ ⊢[PRAAx] b ≐ num c₂)
    (hs : Θ ⊢[PRAAx] lt (a * b + a + b) (num 3)) (φ : Fm PTm n) : Θ ⊢[PRAAx] φ := by
  refine le_lt_absurd φ (a := num 3) (b := num 3 + num k) (le_add_right _ _) ?_
  refine lt_congr ?_ (.eqRefl _) hs
  have e₁ := natEq ha
  have e₂ := natEq hb
  apply deriveNat
  ipra_simps
  rw [e₁, e₂]
  exact_mod_cast congrArg (fun m : ℕ => (m : Groth (Q Θ))) hk

/-- `ab + a + b < 3` gives the five cases. -/
theorem classify {a b : PTm n} (hs : Γ ⊢[PRAAx] lt (a * b + a + b) (num 3)) :
    Γ ⊢[PRAAx] schlafli a b := by
  have ha : Γ ⊢[PRAAx] lt a (num 3) :=
    lt_of_le_of_lt (le_of_eq_add (d := a * b + b) (by ipra_ring)) hs
  have hb : Γ ⊢[PRAAx] lt b (num 3) :=
    lt_of_le_of_lt (le_of_eq_add (d := a * b + a) (by ipra_ring)) hs
  unfold schlafli
  refine .orE (lt_three_cases ha) ?_ (.orE Prf.hyp0 ?_ ?_)
  · -- a = 0
    refine .orE (lt_three_cases hb.wk) ?_ (.orE Prf.hyp0 ?_ ?_)
    · exact .orI₁ (.andI Prf.hyp1 Prf.hyp0)
    · exact .orI₂ (.orI₁ (.andI hyp2 Prf.hyp0))
    · exact .orI₂ (.orI₂ (.orI₂ (.orI₁ (.andI hyp2 Prf.hyp0))))
  · -- a = 1
    refine .orE (lt_three_cases hb.wk.wk) ?_ (.orE Prf.hyp0 ?_ ?_)
    · exact .orI₂ (.orI₂ (.orI₁ (.andI Prf.hyp1 Prf.hyp0)))
    · exact exclude 1 1 0 rfl (.hyp (by simp)) Prf.hyp0 (hs.weaken (fun x hx => by simp [hx])) _
    · exact exclude 1 2 2 rfl (.hyp (by simp)) Prf.hyp0 (hs.weaken (fun x hx => by simp [hx])) _
  · -- a = 2
    refine .orE (lt_three_cases hb.wk.wk) ?_ (.orE Prf.hyp0 ?_ ?_)
    · exact .orI₂ (.orI₂ (.orI₂ (.orI₂ (.andI Prf.hyp1 Prf.hyp0))))
    · exact exclude 2 1 2 rfl (.hyp (by simp)) Prf.hyp0 (hs.weaken (fun x hx => by simp [hx])) _
    · exact exclude 2 2 5 rfl (.hyp (by simp)) Prf.hyp0 (hs.weaken (fun x hx => by simp [hx])) _

/-! ## The theorem -/

/-- Variables: `0 = V`, `1 = E`, `2 = F`, `3 = p'`, `4 = q'`, with `p = p' + 3`, `q = q' + 3`. -/
abbrev p : PTm 5 := var 3 + num 3
abbrev q : PTm 5 := var 4 + num 3

/-- `V − E + F = 2`. -/
abbrev euler : Fm PTm 5 := var 0 + var 2 ≐ var 1 + num 2
/-- `q V = 2E`. -/
abbrev vertexDegree : Fm PTm 5 := q * var 0 ≐ num 2 * var 1
/-- `p F = 2E`. -/
abbrev faceDegree : Fm PTm 5 := p * var 2 ≐ num 2 * var 1

/-- The Platonic classification. -/
abbrev platonicFormula : Fm PTm 5 :=
  euler ⟶ vertexDegree ⟶ faceDegree ⟶ schlafli (var 3) (var 4)

/-- The context of the three relations. -/
abbrev Δ : List (Fm PTm 5) := [faceDegree, vertexDegree, euler]

theorem platonic_solids : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 platonicFormula := by
  refine closeUniv 5 (.impI (.impI (.impI (classify ?_))))
  refine .orE (lt_or_le (var 3 * var 4 + var 3 + var 4) (num 3)) Prf.hyp0 ?_
  -- Otherwise p'q' + p' + q' = 3 + d, and E d + 2pq = 0, which is absurd.
  have w := eq_add_of_le (Prf.hyp0 : (le (num 3) (var 3 * var 4 + var 3 + var 4) :: Δ) ⊢[PRAAx] _)
  have e₁ := natEq (Γ := le (num 3) (var 3 * var 4 + var 3 + var 4) :: Δ) (.hyp (by simp) :
    _ ⊢[PRAAx] euler)
  have e₂ := natEq (Γ := le (num 3) (var 3 * var 4 + var 3 + var 4) :: Δ) (.hyp (by simp) :
    _ ⊢[PRAAx] vertexDegree)
  have e₃ := natEq (Γ := le (num 3) (var 3 * var 4 + var 3 + var 4) :: Δ) (.hyp (by simp) :
    _ ⊢[PRAAx] faceDegree)
  have e₄ := natEq w
  refine .botE _ (succ_ne_zero (a := var 1 * monus (var 3 * var 4 + var 3 + var 4) (num 3) +
    num 2 * (var 3 * var 4 + num 3 * var 3 + num 3 * var 4) + num 17) (deriveNat ?_))
  ipra_simps
  linear_combination (-((V _ 3 + 3) * (V _ 4 + 3))) * e₁ + (V _ 3 + 3) * e₂ +
    (V _ 4 + 3) * e₃ - V _ 1 * e₄

end LeanProofs.IPRA.Geometry.PlatonicSolids
