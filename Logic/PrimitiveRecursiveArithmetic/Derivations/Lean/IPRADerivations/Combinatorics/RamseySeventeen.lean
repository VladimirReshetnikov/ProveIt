import IPRADerivations.Combinatorics.Turan
import IPRADerivations.Core.CertificateTactics

/-!
# `R(3, 3, 3) ≤ 17`

Packets: `combinatorics/ramsey_ipra` (the three-colour triangle number; the lower bound `R(3, 3, 3) > 16` is
`Combinatorics/RamseySixteen`) and `combinatorics/Combinatorics-iPRA`, `graphs.tex`, result 32 ("Finite
multicolor hypergraph Ramsey theorem", its first nontrivial instance).

A three-colouring of the pairs of `Fin 17` is a family `C c u w` (`c : Fin 3`) of integer terms: symmetric bit
matrices with zero diagonal and `C 0 u w + C 1 u w + C 2 u w = 1` for `u ≠ w`. As an iPRA derivation:

* `ramsey333`: if every colour is triangle-free (`C c u v · C c v w · C c u w = 0`), the hypotheses are
  contradictory. So every three-colouring of `K_17` has a monochromatic triangle.

The classical proof takes six neighbours of a vertex in one colour and applies `R(3, 3) = 6` to them, which
would need a case distinction over the six-element subsets. Here the subset is kept as a bit vector and the
distinction disappears:

* `goodman_support` (in a commutative ring): for a bit vector `x` with `M = ∑ x_u`, the complete graph
  `jm x` on its support, and a graph `r` on the support with degrees `ρ_u`,
  `T(jm − r) + T(r) = M (M − 1)(M − 2) − 3 ∑_u ρ_u (M − 1 − ρ_u)`, where `T` counts ordered triangles
  (Goodman's identity; the seven mixed triple sums are evaluated through the two-step path counts
  `path_jj`, `path_jr`);
* `square_sum`: `∑_u (x_u (M − 1 − 2 ρ_u))² = M (M − 1)² − 4 ∑_u ρ_u (M − 1 − ρ_u)`;
* `big_neighbourhood_absurd`: if the neighbourhood of `v₀` in colour `a` has no monochromatic triangle in the
  other two colours, then `M (M − 1)(M − 5) + 3 ∑ (…)² = 0`, so `M ≥ 6` is contradictory;
* `neighbourhood_small`: hence `M ≤ 5` (strict totality of integer terms, `Combinatorics/Turan.zlt_or_zle`);
* the three colour degrees of a vertex sum to `16 > 5 + 5 + 5`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.RamseySeventeen

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.EuclideanSpace (sum_mul_sum_eq)
open LeanProofs.IPRA.Combinatorics.Turan (zlt_or_zle)
open Syn
open scoped Fm

/-! ## Goodman's identity on a support -/

section Ring

variable {R : Type*} [CommRing R] {k : ℕ}

/-- The complete graph on the support of `x`. -/
def jm (x : Fin k → R) (u w : Fin k) : R := x u * x w - if u = w then x u else 0

theorem jm_symm (x : Fin k → R) (u w : Fin k) : jm x u w = jm x w u := by
  unfold jm
  rcases _root_.eq_or_ne u w with rfl | h
  · rfl
  · rw [if_neg h, if_neg (Ne.symm h)]
    ring

theorem swap23 (F : Fin k → Fin k → Fin k → R) :
    ∑ u, ∑ v, ∑ w, F u v w = ∑ u, ∑ w, ∑ v, F u v w :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem rot3 (F : Fin k → Fin k → Fin k → R) :
    ∑ u, ∑ v, ∑ w, F u v w = ∑ v, ∑ w, ∑ u, F u v w :=
  Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm)

variable (x : Fin k → R) (r : Fin k → Fin k → R) (M : R) (ρ : Fin k → R)

/-- Two-step paths in the complete graph on the support. -/
theorem path_jj (hx : ∀ v, x v * x v = x v) (hM : ∑ v, x v = M) (u w : Fin k) :
    ∑ v, jm x u v * jm x v w = x u * x w * (M - 2) + (if u = w then x u else 0) := by
  have p : ∀ v, jm x u v * jm x v w =
      x u * x w * x v - (if v = w then x u * x w else 0) - (if u = v then x u * x w else 0) +
        (if u = v then (if v = w then x u else 0) else 0) := by
    intro v
    unfold jm
    rcases _root_.eq_or_ne u v with rfl | h1
    · rcases _root_.eq_or_ne u w with rfl | h2
      · simp only [↓reduceIte]
        linear_combination ((x u - 1) ^ 2) * hx u
      · simp only [h2, ↓reduceIte]
        linear_combination (x w * (x u - 1)) * hx u
    · rcases _root_.eq_or_ne v w with rfl | h2
      · simp only [h1, ↓reduceIte]
        linear_combination (x u * (x v - 1)) * hx v
      · simp only [h1, h2, ↓reduceIte]
        linear_combination (x u * x w) * hx v
  rw [Finset.sum_congr rfl fun v _ => p v, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, hM]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- A step in the complete graph followed by a step in `r`. -/
theorem path_jr (hx : ∀ v, x v * x v = x v) (hs : ∀ u w, r u w = r w u)
    (hsup : ∀ u w, r u w * x u = r u w) (hρ : ∀ u, ∑ w, r u w = ρ u) (u w : Fin k) :
    ∑ v, jm x u v * r v w = x u * ρ w - r u w := by
  have q : ∀ v, jm x u v * r v w = x u * r w v - (if u = v then r u w else 0) := by
    intro v
    unfold jm
    rcases _root_.eq_or_ne u v with rfl | h1
    · simp only [↓reduceIte]
      linear_combination r u w * hx u - x u * hs w u - hsup u w
    · simp only [h1, ↓reduceIte]
      linear_combination x u * hsup v w + x u * hs v w
  rw [Finset.sum_congr rfl fun v _ => q v, Finset.sum_sub_distrib, ← Finset.mul_sum, hρ w,
    Finset.sum_ite_eq, if_pos (Finset.mem_univ u)]

theorem sum_xx (hM : ∑ v, x v = M) : ∑ u, ∑ w, x u * x w = M * M := by
  rw [sum_mul_sum_eq, hM]

theorem sum_e (hM : ∑ v, x v = M) : ∑ u, ∑ w, (if u = w then x u else 0) = M := by
  rw [← hM]
  exact Finset.sum_congr rfl fun u _ => by rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ u)]

theorem sum_xr (hs : ∀ u w, r u w = r w u) (hsup : ∀ u w, r u w * x u = r u w)
    (hρ : ∀ u, ∑ w, r u w = ρ u) : ∑ u, ∑ w, x u * x w * r u w = ∑ u, ρ u := by
  have hcol : ∀ u w, r u w * x w = r u w := fun u w => by rw [hs u w, hsup w u]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← hρ u]
  exact Finset.sum_congr rfl fun w _ => by linear_combination x w * hsup u w + hcol u w

theorem sum_er (hdiag : ∀ u, r u u = 0) : ∑ u, ∑ w, (if u = w then x u else 0) * r u w = 0 := by
  refine Finset.sum_eq_zero fun u _ => ?_
  have e : ∀ w, (if u = w then x u else 0) * r u w = if u = w then x u * r u w else 0 := by
    intro w
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun w _ => e w, Finset.sum_ite_eq, if_pos (Finset.mem_univ u), hdiag u]
  ring

/-- The path counts against the complete graph. -/
theorem pair_j (hx : ∀ v, x v * x v = x v) (hM : ∑ v, x v = M) :
    ∑ u, ∑ w, (x u * x w * (M - 2) + (if u = w then x u else 0)) * jm x u w = M * (M - 1) * (M - 2) := by
  have a0 : ∀ u w, (x u * x w * (M - 2) + (if u = w then x u else 0)) * jm x u w =
      (M - 2) * (x u * x w) - (M - 2) * (if u = w then x u else 0) := by
    intro u w
    unfold jm
    rcases _root_.eq_or_ne u w with rfl | h
    · simp only [↓reduceIte]
      linear_combination (x u * x u * (M - 2) + x u - (M - 2)) * hx u
    · simp only [h, ↓reduceIte]
      linear_combination ((M - 2) * (x w * x w)) * hx u + ((M - 2) * x u) * hx w
  have hsum : ∑ u, ∑ w, ((M - 2) * (x u * x w) - (M - 2) * (if u = w then x u else 0)) =
      (M - 2) * ∑ u, ∑ w, x u * x w - (M - 2) * ∑ u, ∑ w, (if u = w then x u else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => a0 u w, hsum, sum_xx x M hM,
    sum_e x M hM]
  ring

/-- The path counts against `r`. -/
theorem pair_r (hs : ∀ u w, r u w = r w u) (hsup : ∀ u w, r u w * x u = r u w)
    (hdiag : ∀ u, r u u = 0) (hρ : ∀ u, ∑ w, r u w = ρ u) :
    ∑ u, ∑ w, (x u * x w * (M - 2) + (if u = w then x u else 0)) * r u w = (M - 2) * ∑ u, ρ u := by
  have e1 : ∀ u w, (x u * x w * (M - 2) + (if u = w then x u else 0)) * r u w =
      (M - 2) * (x u * x w * r u w) + (if u = w then x u else 0) * r u w := fun u w => by ring
  have h : ∑ u, ∑ w, ((M - 2) * (x u * x w * r u w) + (if u = w then x u else 0) * r u w) =
      (M - 2) * ∑ u, ∑ w, x u * x w * r u w + ∑ u, ∑ w, (if u = w then x u else 0) * r u w := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => e1 u w, h, sum_xr x r ρ hs hsup hρ,
    sum_er x r hdiag]
  ring

/-- The mixed path counts against `r`. -/
theorem pair_rr (hs : ∀ u w, r u w = r w u) (hsup : ∀ u w, r u w * x u = r u w)
    (hbit : ∀ u w, r u w * r u w = r u w) (hρ : ∀ u, ∑ w, r u w = ρ u) :
    ∑ u, ∑ w, (x u * ρ w - r u w) * r u w = ∑ u, ρ u ^ 2 - ∑ u, ρ u := by
  have b1 : ∀ u w, (x u * ρ w - r u w) * r u w = ρ w * r w u - r u w := fun u w => by
    linear_combination ρ w * hsup u w + ρ w * hs u w - hbit u w
  have h1 : ∑ u, ∑ w, ρ w * r w u = ∑ u, ρ u ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Finset.mul_sum, hρ w]
    ring
  have h2 : ∑ u, ∑ w, r u w = ∑ u, ρ u := Finset.sum_congr rfl fun u _ => hρ u
  have h : ∑ u, ∑ w, (ρ w * r w u - r u w) = ∑ u, ∑ w, ρ w * r w u - ∑ u, ∑ w, r u w := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun u _ => by rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => b1 u w, h, h1, h2]

/-! The seven mixed triple sums. -/

theorem t_jjj (hx : ∀ v, x v * x v = x v) (hM : ∑ v, x v = M) :
    ∑ u, ∑ v, ∑ w, jm x u v * jm x v w * jm x u w = M * (M - 1) * (M - 2) := by
  have e : ∀ u w, ∑ v, jm x u v * jm x v w * jm x u w =
      (x u * x w * (M - 2) + (if u = w then x u else 0)) * jm x u w := fun u w => by
    rw [← Finset.sum_mul, path_jj x M hx hM u w]
  exact (swap23 _).trans ((Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => e u w).trans
    (pair_j x M hx hM))

theorem t_jjr (hx : ∀ v, x v * x v = x v) (hM : ∑ v, x v = M) (hs : ∀ u w, r u w = r w u)
    (hsup : ∀ u w, r u w * x u = r u w) (hdiag : ∀ u, r u u = 0) (hρ : ∀ u, ∑ w, r u w = ρ u) :
    ∑ u, ∑ v, ∑ w, jm x u v * jm x v w * r u w = (M - 2) * ∑ u, ρ u := by
  have e : ∀ u w, ∑ v, jm x u v * jm x v w * r u w =
      (x u * x w * (M - 2) + (if u = w then x u else 0)) * r u w := fun u w => by
    rw [← Finset.sum_mul, path_jj x M hx hM u w]
  exact (swap23 _).trans ((Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => e u w).trans
    (pair_r x r M ρ hs hsup hdiag hρ))

theorem t_jrj (hx : ∀ v, x v * x v = x v) (hM : ∑ v, x v = M) (hs : ∀ u w, r u w = r w u)
    (hsup : ∀ u w, r u w * x u = r u w) (hdiag : ∀ u, r u u = 0) (hρ : ∀ u, ∑ w, r u w = ρ u) :
    ∑ u, ∑ v, ∑ w, jm x u v * r v w * jm x u w = (M - 2) * ∑ u, ρ u := by
  have e : ∀ v w, ∑ u, jm x u v * r v w * jm x u w =
      (x v * x w * (M - 2) + (if v = w then x v else 0)) * r v w := fun v w => by
    have t : ∀ u, jm x u v * r v w * jm x u w = jm x v u * jm x u w * r v w := fun u => by
      rw [jm_symm x u v]
      ring
    rw [Finset.sum_congr rfl fun u _ => t u, ← Finset.sum_mul, path_jj x M hx hM v w]
  exact (rot3 _).trans ((Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => e v w).trans
    (pair_r x r M ρ hs hsup hdiag hρ))

theorem t_rjj (hx : ∀ v, x v * x v = x v) (hM : ∑ v, x v = M) (hs : ∀ u w, r u w = r w u)
    (hsup : ∀ u w, r u w * x u = r u w) (hdiag : ∀ u, r u u = 0) (hρ : ∀ u, ∑ w, r u w = ρ u) :
    ∑ u, ∑ v, ∑ w, r u v * jm x v w * jm x u w = (M - 2) * ∑ u, ρ u := by
  have e : ∀ u v, ∑ w, r u v * jm x v w * jm x u w =
      (x v * x u * (M - 2) + (if v = u then x v else 0)) * r v u := fun u v => by
    have t : ∀ w, r u v * jm x v w * jm x u w = jm x v w * jm x w u * r v u := fun w => by
      rw [jm_symm x u w, hs u v]
      ring
    rw [Finset.sum_congr rfl fun w _ => t w, ← Finset.sum_mul, path_jj x M hx hM v u]
  exact (Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => e u v).trans
    (Finset.sum_comm.trans (pair_r x r M ρ hs hsup hdiag hρ))

theorem t_jrr (hx : ∀ v, x v * x v = x v) (hs : ∀ u w, r u w = r w u)
    (hsup : ∀ u w, r u w * x u = r u w) (hbit : ∀ u w, r u w * r u w = r u w)
    (hρ : ∀ u, ∑ w, r u w = ρ u) :
    ∑ u, ∑ v, ∑ w, jm x u v * r v w * r u w = ∑ u, ρ u ^ 2 - ∑ u, ρ u := by
  have e : ∀ u w, ∑ v, jm x u v * r v w * r u w = (x u * ρ w - r u w) * r u w := fun u w => by
    rw [← Finset.sum_mul, path_jr x r ρ hx hs hsup hρ u w]
  exact (swap23 _).trans ((Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => e u w).trans
    (pair_rr x r ρ hs hsup hbit hρ))

theorem t_rjr (hx : ∀ v, x v * x v = x v) (hs : ∀ u w, r u w = r w u)
    (hsup : ∀ u w, r u w * x u = r u w) (hbit : ∀ u w, r u w * r u w = r u w)
    (hρ : ∀ u, ∑ w, r u w = ρ u) :
    ∑ u, ∑ v, ∑ w, r u v * jm x v w * r u w = ∑ u, ρ u ^ 2 - ∑ u, ρ u := by
  have e : ∀ u v, ∑ w, r u v * jm x v w * r u w = (x v * ρ u - r v u) * r v u := fun u v => by
    have t : ∀ w, r u v * jm x v w * r u w = jm x v w * r w u * r v u := fun w => by
      rw [hs u w, hs u v]
      ring
    rw [Finset.sum_congr rfl fun w _ => t w, ← Finset.sum_mul, path_jr x r ρ hx hs hsup hρ v u]
  exact (Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => e u v).trans
    (Finset.sum_comm.trans (pair_rr x r ρ hs hsup hbit hρ))

theorem t_rrj (hx : ∀ v, x v * x v = x v) (hs : ∀ u w, r u w = r w u)
    (hsup : ∀ u w, r u w * x u = r u w) (hbit : ∀ u w, r u w * r u w = r u w)
    (hρ : ∀ u, ∑ w, r u w = ρ u) :
    ∑ u, ∑ v, ∑ w, r u v * r v w * jm x u w = ∑ u, ρ u ^ 2 - ∑ u, ρ u := by
  have e : ∀ v w, ∑ u, r u v * r v w * jm x u w = (x w * ρ v - r w v) * r w v := fun v w => by
    have t : ∀ u, r u v * r v w * jm x u w = jm x w u * r u v * r w v := fun u => by
      rw [jm_symm x u w, hs v w]
      ring
    rw [Finset.sum_congr rfl fun u _ => t u, ← Finset.sum_mul, path_jr x r ρ hx hs hsup hρ w v]
  exact (rot3 _).trans ((Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => e v w).trans
    (Finset.sum_comm.trans (pair_rr x r ρ hs hsup hbit hρ)))

/-- Goodman's identity on a support: the ordered triangles of `r` and of its complement in the complete graph
on the support. -/
theorem goodman_support (hx : ∀ v, x v * x v = x v) (hM : ∑ v, x v = M) (hs : ∀ u w, r u w = r w u)
    (hsup : ∀ u w, r u w * x u = r u w) (hdiag : ∀ u, r u u = 0)
    (hbit : ∀ u w, r u w * r u w = r u w) (hρ : ∀ u, ∑ w, r u w = ρ u) :
    ∑ u, ∑ v, ∑ w, (jm x u v - r u v) * (jm x v w - r v w) * (jm x u w - r u w) +
        ∑ u, ∑ v, ∑ w, r u v * r v w * r u w =
      M * (M - 1) * (M - 2) - 3 * ((M - 1) * ∑ u, ρ u - ∑ u, ρ u ^ 2) := by
  have p : ∀ u v w, (jm x u v - r u v) * (jm x v w - r v w) * (jm x u w - r u w) =
      jm x u v * jm x v w * jm x u w - jm x u v * jm x v w * r u w - jm x u v * r v w * jm x u w -
        r u v * jm x v w * jm x u w + jm x u v * r v w * r u w + r u v * jm x v w * r u w +
        r u v * r v w * jm x u w - r u v * r v w * r u w := fun u v w => by ring
  have h : ∑ u, ∑ v, ∑ w, (jm x u v - r u v) * (jm x v w - r v w) * (jm x u w - r u w) =
      ∑ u, ∑ v, ∑ w, jm x u v * jm x v w * jm x u w - ∑ u, ∑ v, ∑ w, jm x u v * jm x v w * r u w -
        ∑ u, ∑ v, ∑ w, jm x u v * r v w * jm x u w - ∑ u, ∑ v, ∑ w, r u v * jm x v w * jm x u w +
        ∑ u, ∑ v, ∑ w, jm x u v * r v w * r u w + ∑ u, ∑ v, ∑ w, r u v * jm x v w * r u w +
        ∑ u, ∑ v, ∑ w, r u v * r v w * jm x u w - ∑ u, ∑ v, ∑ w, r u v * r v w * r u w := by
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ =>
      Finset.sum_congr rfl fun w _ => p u v w
  rw [h, t_jjj x M hx hM, t_jjr x r M ρ hx hM hs hsup hdiag hρ, t_jrj x r M ρ hx hM hs hsup hdiag hρ,
    t_rjj x r M ρ hx hM hs hsup hdiag hρ, t_jrr x r ρ hx hs hsup hbit hρ, t_rjr x r ρ hx hs hsup hbit hρ,
    t_rrj x r ρ hx hs hsup hbit hρ]
  ring

/-- `∑ (x_u (M − 1 − 2 ρ_u))² = M (M − 1)² − 4 ((M − 1) ∑ ρ_u − ∑ ρ_u²)`. -/
theorem square_sum (hx : ∀ v, x v * x v = x v) (hM : ∑ v, x v = M) (hxρ : ∀ u, ρ u * x u = ρ u) :
    ∑ u, (x u * (M - 1 - 2 * ρ u)) ^ 2 =
      M * (M - 1) ^ 2 - 4 * ((M - 1) * ∑ u, ρ u - ∑ u, ρ u ^ 2) := by
  have p : ∀ u, (x u * (M - 1 - 2 * ρ u)) ^ 2 =
      x u * (M - 1) ^ 2 - 4 * (M - 1) * ρ u + 4 * ρ u ^ 2 := fun u => by
    linear_combination ((M - 1) ^ 2) * hx u +
      (-4 * (M - 1) * (x u + 1) + 4 * (x u * ρ u + ρ u)) * hxρ u
  have h : ∑ u, (x u * (M - 1) ^ 2 - 4 * (M - 1) * ρ u + 4 * ρ u ^ 2) =
      (∑ u, x u) * (M - 1) ^ 2 - 4 * (M - 1) * ∑ u, ρ u + 4 * ∑ u, ρ u ^ 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      ← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun u _ => p u, h, hM]
  ring

end Ring

/-! ## A monochromatic neighbourhood has at most five vertices -/

variable {n k : ℕ}

/-- The neighbourhood of `v₀` in colour `a`, as a vector of values. -/
def nbX (Γ : List (Fm PTm n)) (a : Fin k → Fin k → ZT n) (v₀ : Fin k) : Fin k → Groth (Q Γ) :=
  fun u => ZT.toZ Γ (a v₀ u)

/-- The colour `p` restricted to that neighbourhood. -/
def nbR (Γ : List (Fm PTm n)) (a p : Fin k → Fin k → ZT n) (v₀ : Fin k) : Fin k → Fin k → Groth (Q Γ) :=
  fun u w => ZT.toZ Γ (p u w) * (nbX Γ a v₀ u * nbX Γ a v₀ w)

variable {Γ : List (Fm PTm n)}

/-- A neighbourhood of six or more vertices in colour `a` without a triangle of `a` through `v₀` and without
triangles of the other two colours is contradictory. -/
theorem big_neighbourhood_absurd (a p q : Fin k → Fin k → ZT n) (v₀ : Fin k)
    (ha_bit : ∀ u, Γ ⊢[PRAAx] ZT.eq (a v₀ u * a v₀ u) (a v₀ u))
    (hp_sym : ∀ u w, Γ ⊢[PRAAx] ZT.eq (p u w) (p w u))
    (hp_bit : ∀ u w, Γ ⊢[PRAAx] ZT.eq (p u w * p u w) (p u w))
    (hp_diag : ∀ u, Γ ⊢[PRAAx] ZT.eq (p u u) (ZT.natLit 0))
    (hq_diag : ∀ u, Γ ⊢[PRAAx] ZT.eq (q u u) (ZT.natLit 0))
    (hpart : ∀ u w, u ≠ w → (Γ ⊢[PRAAx] ZT.eq (a u w + p u w + q u w) (ZT.natLit 1)))
    (ha_tri : ∀ u w, Γ ⊢[PRAAx] ZT.eq (a v₀ u * a u w * a v₀ w) (ZT.natLit 0))
    (hp_tri : ∀ u v w, Γ ⊢[PRAAx] ZT.eq (p u v * p v w * p u w) (ZT.natLit 0))
    (hq_tri : ∀ u v w, Γ ⊢[PRAAx] ZT.eq (q u v * q v w * q u w) (ZT.natLit 0))
    (h6 : Γ ⊢[PRAAx] zle (ZT.natLit 5 + ZT.natLit 1) (ZT.sumFin fun u => a v₀ u)) (φ : Fm PTm n) :
    Γ ⊢[PRAAx] φ := by
  -- the hypotheses as ring equations
  have hx : ∀ u, nbX Γ a v₀ u * nbX Γ a v₀ u = nbX Γ a v₀ u := fun u => by
    have e := ZT.toZ_eq (ha_bit u)
    simpa only [nbX, ZT.toZ_mul] using e
  have ps : ∀ u w, ZT.toZ Γ (p u w) = ZT.toZ Γ (p w u) := fun u w => ZT.toZ_eq (hp_sym u w)
  have pb : ∀ u w, ZT.toZ Γ (p u w) * ZT.toZ Γ (p u w) = ZT.toZ Γ (p u w) := fun u w => by
    have e := ZT.toZ_eq (hp_bit u w)
    simpa only [ZT.toZ_mul] using e
  have pd : ∀ u, ZT.toZ Γ (p u u) = 0 := fun u => by
    have e := ZT.toZ_eq (hp_diag u)
    simpa only [ZT.toZ_natLit, Nat.cast_zero] using e
  have qd : ∀ u, ZT.toZ Γ (q u u) = 0 := fun u => by
    have e := ZT.toZ_eq (hq_diag u)
    simpa only [ZT.toZ_natLit, Nat.cast_zero] using e
  have part : ∀ u w, u ≠ w → ZT.toZ Γ (a u w) + ZT.toZ Γ (p u w) + ZT.toZ Γ (q u w) = 1 :=
    fun u w h => by
      have e := ZT.toZ_eq (hpart u w h)
      simpa only [ZT.toZ_add, ZT.toZ_natLit, Nat.cast_one] using e
  have atri : ∀ u w, nbX Γ a v₀ u * ZT.toZ Γ (a u w) * nbX Γ a v₀ w = 0 := fun u w => by
    have e := ZT.toZ_eq (ha_tri u w)
    simpa only [nbX, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_zero] using e
  have ptri : ∀ u v w, ZT.toZ Γ (p u v) * ZT.toZ Γ (p v w) * ZT.toZ Γ (p u w) = 0 := fun u v w => by
    have e := ZT.toZ_eq (hp_tri u v w)
    simpa only [ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_zero] using e
  have qtri : ∀ u v w, ZT.toZ Γ (q u v) * ZT.toZ Γ (q v w) * ZT.toZ Γ (q u w) = 0 := fun u v w => by
    have e := ZT.toZ_eq (hq_tri u v w)
    simpa only [ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_zero] using e
  -- the graph `p` on the neighbourhood
  have hs : ∀ u w, nbR Γ a p v₀ u w = nbR Γ a p v₀ w u := fun u w => by
    unfold nbR
    rw [ps u w]
    ring
  have hsup : ∀ u w, nbR Γ a p v₀ u w * nbX Γ a v₀ u = nbR Γ a p v₀ u w := fun u w => by
    unfold nbR
    linear_combination (ZT.toZ Γ (p u w) * nbX Γ a v₀ w) * hx u
  have hdiag : ∀ u, nbR Γ a p v₀ u u = 0 := fun u => by
    unfold nbR
    rw [pd u]
    ring
  have hbit : ∀ u w, nbR Γ a p v₀ u w * nbR Γ a p v₀ u w = nbR Γ a p v₀ u w := fun u w => by
    unfold nbR
    linear_combination
      (nbX Γ a v₀ u * nbX Γ a v₀ u * (nbX Γ a v₀ w * nbX Γ a v₀ w)) * pb u w +
        (ZT.toZ Γ (p u w) * (nbX Γ a v₀ w * nbX Γ a v₀ w)) * hx u +
        (ZT.toZ Γ (p u w) * nbX Γ a v₀ u) * hx w
  have hB : ∀ u w, jm (nbX Γ a v₀) u w - nbR Γ a p v₀ u w =
      ZT.toZ Γ (q u w) * (nbX Γ a v₀ u * nbX Γ a v₀ w) := fun u w => by
    unfold jm nbR
    rcases _root_.eq_or_ne u w with rfl | h
    · simp only [↓reduceIte]
      linear_combination hx u - (nbX Γ a v₀ u * nbX Γ a v₀ u) * pd u -
        (nbX Γ a v₀ u * nbX Γ a v₀ u) * qd u
    · simp only [h, ↓reduceIte]
      linear_combination atri u w - (nbX Γ a v₀ u * nbX Γ a v₀ w) * part u w h
  have hxρ : ∀ u, (∑ w, nbR Γ a p v₀ u w) * nbX Γ a v₀ u = ∑ w, nbR Γ a p v₀ u w := fun u => by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun w _ => hsup u w
  -- both colours on the neighbourhood are triangle-free
  have TR0 : ∑ u, ∑ v, ∑ w, nbR Γ a p v₀ u v * nbR Γ a p v₀ v w * nbR Γ a p v₀ u w = 0 :=
    Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => Finset.sum_eq_zero fun w _ => by
      unfold nbR
      linear_combination (nbX Γ a v₀ u * nbX Γ a v₀ v * (nbX Γ a v₀ v * nbX Γ a v₀ w) *
        (nbX Γ a v₀ u * nbX Γ a v₀ w)) * ptri u v w
  have TB0 : ∑ u, ∑ v, ∑ w, (jm (nbX Γ a v₀) u v - nbR Γ a p v₀ u v) *
      (jm (nbX Γ a v₀) v w - nbR Γ a p v₀ v w) * (jm (nbX Γ a v₀) u w - nbR Γ a p v₀ u w) = 0 :=
    Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => Finset.sum_eq_zero fun w _ => by
      rw [hB u v, hB v w, hB u w]
      linear_combination (nbX Γ a v₀ u * nbX Γ a v₀ v * (nbX Γ a v₀ v * nbX Γ a v₀ w) *
        (nbX Γ a v₀ u * nbX Γ a v₀ w)) * qtri u v w
  have G0 := goodman_support (nbX Γ a v₀) (nbR Γ a p v₀) (∑ u, nbX Γ a v₀ u)
    (fun u => ∑ w, nbR Γ a p v₀ u w) hx rfl hs hsup hdiag hbit (fun _ => rfl)
  rw [TB0, TR0] at G0
  have SQ := square_sum (nbX Γ a v₀) (∑ u, nbX Γ a v₀ u) (fun u => ∑ w, nbR Γ a p v₀ u w) hx rfl hxρ
  simp only [nbX, nbR] at G0 SQ
  -- the contradiction
  refine false_of_comb (3 * ∑ u, ZT.toZ Γ (a v₀ u * ((ZT.sumFin fun u => a v₀ u) - ZT.natLit 1 -
        ZT.natLit 2 * ZT.sumFin fun w => p u w * (a v₀ u * a v₀ w))) ^ 2 +
      (zsl h6 ^ 3 + 12 * zsl h6 ^ 2 + 41 * zsl h6 + 29)) ?_
    (nn_add (nn_mul (nn_ofNat 3) (nn_sum _ _ fun u _ => nn_zsq _))
      (nn_add (nn_add (nn_add (nn_pow (nn_zsl _) 3) (nn_mul (nn_ofNat 12) (nn_pow (nn_zsl _) 2)))
        (nn_mul (nn_ofNat 41) (nn_zsl _))) (nn_ofNat 29))) φ
  simp only [zsl_def, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit, ZT.toZ_sumFin, Nat.cast_ofNat,
    Nat.cast_one]
  linear_combination 3 * SQ - 4 * G0

/-- The neighbourhood of `v₀` in colour `a` has at most five vertices. -/
theorem neighbourhood_small (a p q : Fin k → Fin k → ZT n) (v₀ : Fin k)
    (ha_bit : ∀ u, Γ ⊢[PRAAx] ZT.eq (a v₀ u * a v₀ u) (a v₀ u))
    (hp_sym : ∀ u w, Γ ⊢[PRAAx] ZT.eq (p u w) (p w u))
    (hp_bit : ∀ u w, Γ ⊢[PRAAx] ZT.eq (p u w * p u w) (p u w))
    (hp_diag : ∀ u, Γ ⊢[PRAAx] ZT.eq (p u u) (ZT.natLit 0))
    (hq_diag : ∀ u, Γ ⊢[PRAAx] ZT.eq (q u u) (ZT.natLit 0))
    (hpart : ∀ u w, u ≠ w → (Γ ⊢[PRAAx] ZT.eq (a u w + p u w + q u w) (ZT.natLit 1)))
    (ha_tri : ∀ u w, Γ ⊢[PRAAx] ZT.eq (a v₀ u * a u w * a v₀ w) (ZT.natLit 0))
    (hp_tri : ∀ u v w, Γ ⊢[PRAAx] ZT.eq (p u v * p v w * p u w) (ZT.natLit 0))
    (hq_tri : ∀ u v w, Γ ⊢[PRAAx] ZT.eq (q u v * q v w * q u w) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] zle (ZT.sumFin fun u => a v₀ u) (ZT.natLit 5) := by
  refine .orE (zlt_or_zle (ZT.sumFin fun u => a v₀ u) (ZT.natLit 5)) ?_ Prf.hyp0
  exact big_neighbourhood_absurd a p q v₀ (fun u => (ha_bit u).wk) (fun u w => (hp_sym u w).wk)
    (fun u w => (hp_bit u w).wk) (fun u => (hp_diag u).wk) (fun u => (hq_diag u).wk)
    (fun u w h => (hpart u w h).wk) (fun u w => (ha_tri u w).wk) (fun u v w => (hp_tri u v w).wk)
    (fun u v w => (hq_tri u v w).wk) Prf.hyp0 _

/-! ## The theorem -/

/-- `R(3, 3, 3) ≤ 17`: a three-colouring of the pairs of `Fin 17` in which every colour is triangle-free is
contradictory. -/
theorem ramsey333 (C : Fin 3 → Fin 17 → Fin 17 → ZT n)
    (hsym : ∀ c u w, Γ ⊢[PRAAx] ZT.eq (C c u w) (C c w u))
    (hbit : ∀ c u w, Γ ⊢[PRAAx] ZT.eq (C c u w * C c u w) (C c u w))
    (hdiag : ∀ c u, Γ ⊢[PRAAx] ZT.eq (C c u u) (ZT.natLit 0))
    (hpart : ∀ u w, u ≠ w → (Γ ⊢[PRAAx] ZT.eq (C 0 u w + C 1 u w + C 2 u w) (ZT.natLit 1)))
    (htri : ∀ c u v w, Γ ⊢[PRAAx] ZT.eq (C c u v * C c v w * C c u w) (ZT.natLit 0))
    (φ : Fm PTm n) : Γ ⊢[PRAAx] φ := by
  have part1 : ∀ u w, u ≠ w → (Γ ⊢[PRAAx] ZT.eq (C 1 u w + C 0 u w + C 2 u w) (ZT.natLit 1)) :=
    fun u w h => by
      have e := ZT.toZ_eq (hpart u w h)
      apply ZT.derive
      simp only [ZT.toZ_add, ZT.toZ_natLit, Nat.cast_one] at e ⊢
      linear_combination e
  have part2 : ∀ u w, u ≠ w → (Γ ⊢[PRAAx] ZT.eq (C 2 u w + C 0 u w + C 1 u w) (ZT.natLit 1)) :=
    fun u w h => by
      have e := ZT.toZ_eq (hpart u w h)
      apply ZT.derive
      simp only [ZT.toZ_add, ZT.toZ_natLit, Nat.cast_one] at e ⊢
      linear_combination e
  have h0 := neighbourhood_small (C 0) (C 1) (C 2) 0 (fun u => hbit 0 0 u) (hsym 1) (hbit 1) (hdiag 1)
    (hdiag 2) hpart (fun u w => htri 0 0 u w) (htri 1) (htri 2)
  have h1 := neighbourhood_small (C 1) (C 0) (C 2) 0 (fun u => hbit 1 0 u) (hsym 0) (hbit 0) (hdiag 0)
    (hdiag 2) part1 (fun u w => htri 1 0 u w) (htri 0) (htri 2)
  have h2 := neighbourhood_small (C 2) (C 0) (C 1) 0 (fun u => hbit 2 0 u) (hsym 0) (hbit 0) (hdiag 0)
    (hdiag 1) part2 (fun u w => htri 2 0 u w) (htri 0) (htri 1)
  -- the three colour degrees of the vertex `0` sum to sixteen
  have d : ∀ c : Fin 3, ZT.toZ Γ (C c 0 0) = 0 := fun c => by
    have e := ZT.toZ_eq (hdiag c 0)
    simpa only [ZT.toZ_natLit, Nat.cast_zero] using e
  have pt : ∀ u : Fin 17, ZT.toZ Γ (C 0 0 u) + ZT.toZ Γ (C 1 0 u) + ZT.toZ Γ (C 2 0 u) =
      1 - (if (0 : Fin 17) = u then 1 else 0) := fun u => by
    rcases _root_.eq_or_ne (0 : Fin 17) u with rfl | h
    · rw [if_pos rfl, d 0, d 1, d 2]
      ring
    · rw [if_neg h]
      have e := ZT.toZ_eq (hpart 0 u h)
      simp only [ZT.toZ_add, ZT.toZ_natLit, Nat.cast_one] at e
      linear_combination e
  have E16 : ∑ u, ZT.toZ Γ (C 0 0 u) + ∑ u, ZT.toZ Γ (C 1 0 u) + ∑ u, ZT.toZ Γ (C 2 0 u) = 16 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_congr rfl fun u _ => pt u,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.sum_ite_eq,
      if_pos (Finset.mem_univ 0), nsmul_eq_mul]
    norm_num
  ipra_absurd (zsl h0 + zsl h1 + zsl h2) with -E16

end LeanProofs.IPRA.Combinatorics.RamseySeventeen
