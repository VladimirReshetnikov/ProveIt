import IPRADerivations.Algebra.AdjugateInverse
import Mathlib.Data.Fin.SuccPred
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi

/-!
# The cross-polytope cycle and the antipodal action

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/07_spheres.tex`, Lemma S01
(`lem:sphere-cycle`): for `d = n + 1`, the chain
`z_n = ∑_{ε ∈ {±1}^d} (∏_i ε_i) [ε₀ e₀, …, ε_{d−1} e_{d−1}]` of the boundary complex of the cross-polytope satisfies
`∂ z_n = 0`; for the antipodal vertex map `A`, `A_# z_n = (−1)^{n+1} z_n`; and `z_n ≠ 0`.

Vertices are pairs `(sign, index)`; the facet of a sign vector `ε` is the tuple `i ↦ (ε_i, i)` (`facet`), with
coefficient `∏_i sgn(ε_i)` (`coef`). As in `Topology/BoundarySquare`, chains are evaluated against an arbitrary
additive `φ`:

* `boundary_zero`: `∑_ε coef(ε) ∑_j (−1)^j φ(face_j(facet ε)) = 0` ("Fix a boundary face obtained by deleting
  coordinate `j`. It occurs for the two choices `ε_j = 1, −1`. Their boundary signs are both `(−1)^j`, whereas
  their coefficient products have opposite signs"), by the involution `flip j` (`flip_flip`, `flip_ne`,
  `face_flip`, `coef_flip`);
* `antipodal`: `∑_ε coef(ε) φ(A ∘ facet ε) = (−1)^{n+1} ∑_ε coef(ε) φ(facet ε)`;
* `top_coef`: the coefficient of `[e₀, …, e_n]` in `z_n` is `1`.
-/

namespace LeanProofs.IPRA.Topology.SphereCycle

variable {M : Type*} [AddCommGroup M] {n : ℕ}

/-- The vertex `±e_i`. -/
abbrev Vtx (d : ℕ) := Bool × Fin d

/-- The facet `[ε₀ e₀, …, ε_n e_n]`. -/
def facet (ε : Fin (n + 1) → Bool) : Fin (n + 1) → Vtx (n + 1) := fun i => (ε i, i)

/-- The sign `±1`. -/
def sgn (b : Bool) : ℤ := if b then 1 else -1

/-- The coefficient `∏_i ε_i`. -/
def coef (ε : Fin (n + 1) → Bool) : ℤ := ∏ i, sgn (ε i)

/-- Flip the sign in coordinate `j`. -/
def flip (j : Fin (n + 1)) (ε : Fin (n + 1) → Bool) : Fin (n + 1) → Bool := Function.update ε j (!ε j)

/-- The antipodal vertex map. -/
def anti (v : Vtx (n + 1)) : Vtx (n + 1) := (!v.1, v.2)

theorem sgn_not (b : Bool) : sgn (!b) = -sgn b := by cases b <;> simp [sgn]

theorem flip_flip (j : Fin (n + 1)) (ε : Fin (n + 1) → Bool) : flip j (flip j ε) = ε := by
  funext i
  by_cases h : i = j
  · subst h; simp [flip]
  · simp [flip, Function.update_apply, h]

theorem flip_ne (j : Fin (n + 1)) (ε : Fin (n + 1) → Bool) : flip j ε ≠ ε := fun h => by
  have := congrFun h j
  simp [flip] at this

theorem face_flip (j : Fin (n + 1)) (ε : Fin (n + 1) → Bool) :
    facet (flip j ε) ∘ j.succAbove = facet ε ∘ j.succAbove := by
  funext k
  simp [facet, flip, Function.update_apply, Fin.succAbove_ne]

theorem coef_flip (j : Fin (n + 1)) (ε : Fin (n + 1) → Bool) : coef (flip j ε) = -coef ε := by
  unfold coef
  rw [Fin.prod_univ_succAbove _ j, Fin.prod_univ_succAbove (fun i => sgn (ε i)) j]
  simp only [flip, Function.update_apply, Fin.succAbove_ne, if_false, if_true, sgn_not]
  ring

/-- S01: `∂ z_n = 0`. -/
theorem boundary_zero (φ : (Fin n → Vtx (n + 1)) → M) :
    ∑ ε : Fin (n + 1) → Bool, coef ε • ∑ j : Fin (n + 1), ((-1 : ℤ) ^ j.val) • φ (facet ε ∘ j.succAbove) = 0 := by
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  refine Finset.sum_involution (fun ε _ => flip j ε) ?_ ?_ ?_ ?_
  · intro ε _
    simp only [face_flip, coef_flip, neg_smul, add_neg_cancel]
  · intro ε _ _
    exact flip_ne j ε
  · intro ε _
    exact Finset.mem_univ _
  · intro ε _
    exact flip_flip j ε

theorem anti_facet (ε : Fin (n + 1) → Bool) : anti ∘ facet ε = facet fun i => !ε i := by
  funext i; rfl

theorem coef_not (ε : Fin (n + 1) → Bool) : coef (fun i => !ε i) = (-1) ^ (n + 1) * coef ε := by
  unfold coef
  simp only [sgn_not, Finset.prod_neg, Finset.card_univ, Fintype.card_fin]

/-- S01: `A_# z_n = (−1)^{n+1} z_n`. -/
theorem antipodal (φ : (Fin (n + 1) → Vtx (n + 1)) → M) :
    ∑ ε : Fin (n + 1) → Bool, coef ε • φ (anti ∘ facet ε) =
      ((-1 : ℤ) ^ (n + 1)) • ∑ ε : Fin (n + 1) → Bool, coef ε • φ (facet ε) := by
  have hinv : Function.Involutive fun ε : Fin (n + 1) → Bool => fun i => !ε i := fun ε => by
    funext i; simp
  rw [Finset.smul_sum]
  refine Fintype.sum_bijective (fun ε i => !ε i) hinv.bijective _ _ fun ε => ?_
  beta_reduce
  rw [anti_facet, ← mul_smul, coef_not, ← _root_.mul_assoc, ← _root_.pow_add, ← _root_.two_mul, _root_.pow_mul]
  simp

/-- `z_n ≠ 0`: the coefficient of `[e₀, …, e_n]` is `1`. -/
theorem top_coef :
    ∑ ε : Fin (n + 1) → Bool, (if facet ε = facet (fun _ => true) then coef ε else 0) = 1 := by
  have hinj : ∀ ε : Fin (n + 1) → Bool, facet ε = facet (fun _ => true) ↔ ε = fun _ => true := fun ε => by
    constructor
    · intro h; funext i; exact congrArg Prod.fst (congrFun h i)
    · rintro rfl; rfl
  simp only [hinj]
  rw [Finset.sum_ite_eq']
  simp [coef, sgn]

end LeanProofs.IPRA.Topology.SphereCycle
