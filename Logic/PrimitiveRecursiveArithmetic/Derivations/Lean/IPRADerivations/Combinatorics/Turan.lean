import IPRADerivations.Geometry.EuclideanSpace
import IPRADerivations.Core.CertificateTactics

/-!
# Turán's bound for every number of parts

Packet: `combinatorics/Combinatorics-iPRA`, `graphs.tex`, result 20 (`thm:graph-turan`), and
`combinatorics/graph-ipra`, `tex/color.tex`, Theorem 14.1 (`co:turan`): "A graph on `n` vertices containing no
`(r + 1)`-clique has at most `t_r(n)` edges", in the form "`t_r(n) ≤ (1 − 1/r) n²/2`" recorded there for later
use: `r · 2e ≤ (r − 1) n²`.

The graph has vertex set `Fin k` and a symmetric matrix `A u v` of integer terms that are bits
(`A_{uv}² = A_{uv}`); a vertex set is a bit vector `x` carrying the graph (`A_{uv} x_u = A_{uv}`). Clique-freeness
is expressed through neighbourhoods: `nb A u` is the graph induced on the neighbours of `u`,
`(nb A u)_{vw} = A_{vw} A_{uv} A_{uw}`, and

* `Free Γ 0 A`: every `A_{vw}` is derivably `0` (no `K_2`);
* `Free Γ (ρ + 1) A`: every `nb A u` satisfies `Free Γ ρ` (no `K_{ρ+3}`: a clique through `u` is a clique of
  one vertex less among the neighbours of `u`).

As iPRA derivations, by induction on `ρ` in the metatheory:

* `turan`: `Free Γ ρ A` gives `(ρ + 1) E ≤ ρ N²` for `E = ∑_{u,v} A_{uv}` (twice the number of edges) and
  `N = ∑_v x_v`;
* `turan_all`: with all `k` vertices, `(ρ + 1) E ≤ ρ k²`; for `ρ = 1` this is Mantel's theorem `4e ≤ k²`,
  without the factor `E` of `Combinatorics/Mantel.mantel`.

The argument is not the packet's (which replaces the graph by a complete multipartite graph through a vertex of
maximal degree); it is a counting argument that needs no choice of a vertex. Summing the induction hypothesis
`(ρ + 1) E_u ≤ ρ d_u²` over all `u`, adding `ρ + 1` times the common-neighbour inequalities
`A_{uv} (N − d_u − d_v + c_{uv}) ≥ 0` (each a square, by the bit identities; `common_sum`) and `ρ + 2` times the
Cauchy–Schwarz slack `N ∑ d_u² − E² ≥ 0` gives the cleared bound `(ρ + 2) E² ≤ (ρ + 1) N² E` (`turan_cert`);
the factor `E` is then cancelled by `zle_of_mul_self`, a decidable case distinction on integer terms.

Not derived: the exact Turán number `t_r(n)`, the extremal graphs, and the witness of an `(r + 1)`-clique above
the bound.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.Turan

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.EuclideanSpace (cauchy_schwarz)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

variable {n k : ℕ} {Γ : List (Fm PTm n)}

/-! ## Identities in a commutative ring -/

section Ring

variable {R : Type*} [CommRing R]

/-- For bits `A₁, b, c ≤ X`: `(A₁ (X − b)(X − c))² = A₁ (X − b − c + b c)`. -/
theorem bit_square {A1 b c X : R} (hA : A1 * A1 = A1) (hb : b * b = b) (hc : c * c = c)
    (hX : X * X = X) (hbX : b * X = b) (hcX : c * X = c) :
    (A1 * ((X - b) * (X - c))) ^ 2 = A1 * X - A1 * b - A1 * c + A1 * (b * c) := by
  have e1 : (X - b) ^ 2 = X - b := by linear_combination hX + hb - 2 * hbX
  have e2 : (X - c) ^ 2 = X - c := by linear_combination hX + hc - 2 * hcX
  have e3 : (X - b) * (X - c) = X - c - b + b * c := by linear_combination hX - hcX - hbX
  calc (A1 * ((X - b) * (X - c))) ^ 2 = A1 * A1 * ((X - b) ^ 2 * (X - c) ^ 2) := by ring
    _ = A1 * ((X - b) * (X - c)) := by rw [hA, e1, e2]
    _ = A1 * X - A1 * b - A1 * c + A1 * (b * c) := by rw [e3]; ring

variable (a : Fin k → Fin k → R) (x : Fin k → R)

theorem triple_one : ∑ u, ∑ v, ∑ w, a u v * x w = (∑ u, ∑ v, a u v) * ∑ w, x w := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun v _ => (Finset.mul_sum _ _ _).symm

theorem triple_two : ∑ u, ∑ v, ∑ w, a u v * a u w = ∑ u, (∑ v, a u v) ^ 2 := by
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [sq, Finset.sum_mul]
  exact Finset.sum_congr rfl fun v _ => (Finset.mul_sum _ _ _).symm

theorem triple_three (hs : ∀ v w, a v w = a w v) :
    ∑ u, ∑ v, ∑ w, a u v * a v w = ∑ v, (∑ w, a v w) ^ 2 := by
  have e : ∀ u v, ∑ w, a u v * a v w = a u v * ∑ w, a v w := fun u v => (Finset.mul_sum _ _ _).symm
  have h : ∑ u, ∑ v, ∑ w, a u v * a v w = ∑ u, ∑ v, a u v * ∑ w, a v w :=
    Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => e u v
  rw [h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Finset.sum_mul, Finset.sum_congr rfl fun u _ => hs u v]
  ring

theorem triple_four :
    ∑ u, ∑ v, ∑ w, a u v * (a u w * a v w) = ∑ u, ∑ v, ∑ w, a v w * (a u v * a u w) :=
  Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => by ring

/-- The common-neighbour squares sum to `E N − 2 ∑ d_u² + T`. -/
theorem common_sum (hs : ∀ v w, a v w = a w v) (hb : ∀ u v, a u v * a u v = a u v)
    (hx : ∀ v, x v * x v = x v) (hsup : ∀ u v, a u v * x u = a u v) :
    ∑ u, ∑ v, ∑ w, (a u v * ((x w - a u w) * (x w - a v w))) ^ 2 =
      (∑ u, ∑ v, a u v) * (∑ w, x w) - 2 * ∑ u, (∑ v, a u v) ^ 2 +
        ∑ u, ∑ v, ∑ w, a v w * (a u v * a u w) := by
  have hcol : ∀ u v, a u v * x v = a u v := fun u v => by rw [hs u v, hsup v u]
  have p : ∀ u v w, (a u v * ((x w - a u w) * (x w - a v w))) ^ 2 =
      a u v * x w - a u v * a u w - a u v * a v w + a u v * (a u w * a v w) := fun u v w =>
    bit_square (hb u v) (hb u w) (hb v w) (hx w) (hcol u w) (hcol v w)
  have h : ∑ u, ∑ v, ∑ w, (a u v * ((x w - a u w) * (x w - a v w))) ^ 2 =
      ∑ u, ∑ v, ∑ w, a u v * x w - ∑ u, ∑ v, ∑ w, a u v * a u w - ∑ u, ∑ v, ∑ w, a u v * a v w +
        ∑ u, ∑ v, ∑ w, a u v * (a u w * a v w) := by
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ =>
      Finset.sum_congr rfl fun w _ => p u v w
  rw [h, triple_one, triple_two, triple_three a hs, triple_four]
  ring

theorem weight_sum (hsup : ∀ u v, a u v * x u = a u v) :
    ∑ u, x u * ∑ v, a u v = ∑ u, ∑ v, a u v := by
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => by rw [_root_.mul_comm, hsup u v]

theorem sq_sum (hx : ∀ v, x v * x v = x v) : ∑ u, x u ^ 2 = ∑ u, x u :=
  Finset.sum_congr rfl fun u _ => by rw [sq, hx u]

/-- The certificate of the induction step. -/
theorem turan_cert (ρ : ℕ) (hs : ∀ v w, a v w = a w v) (hb : ∀ u v, a u v * a u v = a u v)
    (hx : ∀ v, x v * x v = x v) (hsup : ∀ u v, a u v * x u = a u v) :
    ((ρ + 1 : ℕ) : R) * (∑ u, x u) ^ 2 * (∑ u, ∑ v, a u v) -
        ((ρ + 2 : ℕ) : R) * ((∑ u, ∑ v, a u v) * (∑ u, ∑ v, a u v)) =
      (∑ u, x u ^ 2) *
          (∑ u, ((ρ : R) * (∑ v, a u v) ^ 2 - ((ρ + 1 : ℕ) : R) * ∑ v, ∑ w, a v w * (a u v * a u w)) +
            ((ρ + 1 : ℕ) : R) * ∑ u, ∑ v, ∑ w, (a u v * ((x w - a u w) * (x w - a v w))) ^ 2) +
        ((ρ + 2 : ℕ) : R) *
          ((∑ u, x u ^ 2) * (∑ u, (∑ v, a u v) ^ 2) - (∑ u, x u * ∑ v, a u v) ^ 2) := by
  have hS : ∑ u, ((ρ : R) * (∑ v, a u v) ^ 2 - ((ρ + 1 : ℕ) : R) * ∑ v, ∑ w, a v w * (a u v * a u w)) =
      (ρ : R) * ∑ u, (∑ v, a u v) ^ 2 - ((ρ + 1 : ℕ) : R) * ∑ u, ∑ v, ∑ w, a v w * (a u v * a u w) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hS, common_sum a x hs hb hx hsup, weight_sum a x hsup, sq_sum x hx]
  push_cast
  ring

end Ring

/-! ## Order lemmas for integer terms -/

/-- Strict totality for integer terms: `v + 1 ≤ u` or `u ≤ v`. -/
theorem zlt_or_zle (u v : ZT n) : Γ ⊢[PRAAx] zle (v + ZT.natLit 1) u ⋎ zle u v := by
  refine .orE (lt_or_le (v.pos + u.neg) (u.pos + v.neg)) ?_ (.orI₂ Prf.hyp0)
  have hlt : (lt (v.pos + u.neg) (u.pos + v.neg) :: Γ) ⊢[PRAAx] le (succ (v.pos + u.neg)) (u.pos + v.neg) :=
    Prf.hyp0
  refine .orI₁ (zle_of_comb (sl hlt) ?_ (nn_sl _))
  simp only [sl_def, ZT.toZ_add, ZT.toZ_natLit, Nat.cast_one, Q.mk_add, Q.mk_succ, map_add, map_one]
  simp only [toZ_def]
  ring

/-- Cancelling a factor: `c e² ≤ b e` and `0 ≤ b` give `c e ≤ b`. -/
theorem zle_of_mul_self (c : ℕ) {e b : ZT n} (hb : Γ ⊢[PRAAx] zle (ZT.natLit 0) b)
    (h : Γ ⊢[PRAAx] zle (ZT.natLit c * (e * e)) (b * e)) : Γ ⊢[PRAAx] zle (ZT.natLit c * e) b := by
  refine .orE (zlt_or_zle (ZT.natLit c * e) b) ?_ Prf.hyp0
  have hlt : (zle (b + ZT.natLit 1) (ZT.natLit c * e) :: Γ) ⊢[PRAAx]
      zle (b + ZT.natLit 1) (ZT.natLit c * e) := Prf.hyp0
  have hb1 := hb.wk (ψ := zle (b + ZT.natLit 1) (ZT.natLit c * e))
  have h1 := h.wk (ψ := zle (b + ZT.natLit 1) (ZT.natLit c * e))
  refine false_of_comb ((c : Groth (Q _)) * zsl h1 + zsl hlt * zsl hlt + zsl hlt * zsl hb1 +
      2 * zsl hlt + zsl hb1) ?_
    (nn_add (nn_add (nn_add (nn_add (nn_mul (nn_natCast c) (nn_zsl _)) (nn_mul (nn_zsl _) (nn_zsl _)))
      (nn_mul (nn_zsl _) (nn_zsl _))) (nn_mul (nn_ofNat 2) (nn_zsl _))) (nn_zsl _)) _
  zsimp
  ring

/-! ## Neighbourhood graphs and clique-freeness -/

/-- The graph induced on the neighbours of `u`: `A_{vw} A_{uv} A_{uw}`. -/
def nb (A : Fin k → Fin k → ZT n) (u : Fin k) : Fin k → Fin k → ZT n :=
  fun v w => A v w * (A u v * A u w)

/-- `Free Γ ρ A`: the graph `A` has no clique on `ρ + 2` vertices. -/
def Free (Γ : List (Fm PTm n)) : ℕ → (Fin k → Fin k → ZT n) → Prop
  | 0, A => ∀ v w, Γ ⊢[PRAAx] ZT.eq (A v w) (ZT.natLit 0)
  | ρ + 1, A => ∀ u, Free Γ ρ (nb A u)

theorem nb_symm {A : Fin k → Fin k → ZT n} (hs : ∀ v w, Γ ⊢[PRAAx] ZT.eq (A v w) (A w v)) (u v w : Fin k) :
    Γ ⊢[PRAAx] ZT.eq (nb A u v w) (nb A u w v) := by
  have e := ZT.toZ_eq (hs v w)
  apply ZT.derive
  simp only [nb, ZT.toZ_mul]
  rw [e]
  ring

theorem nb_bit {A : Fin k → Fin k → ZT n} (hb : ∀ v w, Γ ⊢[PRAAx] ZT.eq (A v w * A v w) (A v w))
    (u v w : Fin k) : Γ ⊢[PRAAx] ZT.eq (nb A u v w * nb A u v w) (nb A u v w) := by
  ipra_lc [nb] (ZT.toZ Γ (A u v) * ZT.toZ Γ (A u v) * (ZT.toZ Γ (A u w) * ZT.toZ Γ (A u w))) * ZT.toZ_eq (hb v w) +
    (ZT.toZ Γ (A v w) * (ZT.toZ Γ (A u w) * ZT.toZ Γ (A u w))) * ZT.toZ_eq (hb u v) +
    (ZT.toZ Γ (A v w) * ZT.toZ Γ (A u v)) * ZT.toZ_eq (hb u w)

theorem nb_support {A : Fin k → Fin k → ZT n} (hb : ∀ v w, Γ ⊢[PRAAx] ZT.eq (A v w * A v w) (A v w))
    (u v w : Fin k) : Γ ⊢[PRAAx] ZT.eq (nb A u v w * A u v) (nb A u v w) := by
  ipra_lc [nb] (ZT.toZ Γ (A v w) * ZT.toZ Γ (A u w)) * ZT.toZ_eq (hb u v)

/-! ## Turán's bound -/

/-- A graph without a clique on `ρ + 2` vertices, carried by the vertex set `x`: `(ρ + 1) E ≤ ρ N²`. -/
theorem turan : ∀ (ρ : ℕ) (A : Fin k → Fin k → ZT n) (x : Fin k → ZT n),
    (∀ v w, Γ ⊢[PRAAx] ZT.eq (A v w) (A w v)) →
    (∀ v w, Γ ⊢[PRAAx] ZT.eq (A v w * A v w) (A v w)) →
    (∀ v, Γ ⊢[PRAAx] ZT.eq (x v * x v) (x v)) →
    (∀ u v, Γ ⊢[PRAAx] ZT.eq (A u v * x u) (A u v)) →
    Free Γ ρ A →
    (Γ ⊢[PRAAx] zle (ZT.natLit (ρ + 1) * ZT.sumFin fun u => ZT.sumFin fun v => A u v)
      (ZT.natLit ρ * ZT.sq (ZT.sumFin x)))
  | 0, A, x, _, _, _, _, hfree => by
    have hf : ∀ v w, Γ ⊢[PRAAx] ZT.eq (A v w) (ZT.natLit 0) := hfree
    have h0 : ∀ v w, ZT.toZ Γ (A v w) = 0 := fun v w => by
      have e := ZT.toZ_eq (hf v w)
      simpa only [ZT.toZ_natLit, Nat.cast_zero] using e
    refine zle_of_comb 0 ?_ nn_zero
    simp only [ZT.toZ_mul, ZT.toZ_sq, ZT.toZ_natLit, ZT.toZ_sumFin, h0, Finset.sum_const_zero,
      Nat.cast_zero]
    ring
  | ρ + 1, A, x, hs, hb, hx, hsup, hfree => by
    have hf : ∀ u, Free Γ ρ (nb A u) := hfree
    have hs1 : ∀ v w, ZT.toZ Γ (A v w) = ZT.toZ Γ (A w v) := fun v w => ZT.toZ_eq (hs v w)
    have hb1 : ∀ v w, ZT.toZ Γ (A v w) * ZT.toZ Γ (A v w) = ZT.toZ Γ (A v w) := fun v w => by
      have e := ZT.toZ_eq (hb v w)
      simpa only [ZT.toZ_mul] using e
    have hx1 : ∀ v, ZT.toZ Γ (x v) * ZT.toZ Γ (x v) = ZT.toZ Γ (x v) := fun v => by
      have e := ZT.toZ_eq (hx v)
      simpa only [ZT.toZ_mul] using e
    have hsup1 : ∀ u v, ZT.toZ Γ (A u v) * ZT.toZ Γ (x u) = ZT.toZ Γ (A u v) := fun u v => by
      have e := ZT.toZ_eq (hsup u v)
      simpa only [ZT.toZ_mul] using e
    have IH : ∀ u, Γ ⊢[PRAAx] zle
        (ZT.natLit (ρ + 1) * ZT.sumFin fun v => ZT.sumFin fun w => nb A u v w)
        (ZT.natLit ρ * ZT.sq (ZT.sumFin fun v => A u v)) := fun u =>
      turan ρ (nb A u) (fun v => A u v) (nb_symm hs u) (nb_bit hb u) (fun v => hb u v)
        (nb_support hb u) (hf u)
    have hcs := cauchy_schwarz (Γ := Γ) x (fun u => ZT.sumFin fun v => A u v)
    have L := turan_cert (fun u v => ZT.toZ Γ (A u v)) (fun v => ZT.toZ Γ (x v)) ρ hs1 hb1 hx1 hsup1
    beta_reduce at L
    have hcl : Γ ⊢[PRAAx] zle
        (ZT.natLit (ρ + 2) * ((ZT.sumFin fun u => ZT.sumFin fun v => A u v) *
          (ZT.sumFin fun u => ZT.sumFin fun v => A u v)))
        (ZT.natLit (ρ + 1) * ZT.sq (ZT.sumFin x) * (ZT.sumFin fun u => ZT.sumFin fun v => A u v)) := by
      refine zle_of_comb ((∑ u, ZT.toZ Γ (x u) ^ 2) *
          (∑ u, zsl (IH u) + ((ρ + 1 : ℕ) : Groth (Q Γ)) *
            ∑ u, ∑ v, ∑ w, ZT.toZ Γ (A u v * ((x w - A u w) * (x w - A v w))) ^ 2) +
          ((ρ + 2 : ℕ) : Groth (Q Γ)) * zsl hcs) ?_
        (nn_add (nn_mul (nn_sum _ _ fun u _ => nn_zsq _)
          (nn_add (nn_sum _ _ fun u _ => nn_zsl _)
            (nn_mul (nn_natCast _)
              (nn_sum _ _ fun u _ => nn_sum _ _ fun v _ => nn_sum _ _ fun w _ => nn_zsq _))))
          (nn_mul (nn_natCast _) (nn_zsl _)))
      simp only [nb, zsl_def, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_sq, ZT.toZ_natLit,
        ZT.toZ_sumFin]
      linear_combination L
    have hbn : Γ ⊢[PRAAx] zle (ZT.natLit 0) (ZT.natLit (ρ + 1) * ZT.sq (ZT.sumFin x)) := by
      ipra_zle (((ρ + 1 : ℕ) : Groth (Q Γ)) * ZT.toZ Γ (ZT.sumFin x) ^ 2)
    exact zle_of_mul_self (ρ + 2) hbn hcl

/-- Turán's bound on all `k` vertices: `(ρ + 1) E ≤ ρ k²` for a graph without a clique on `ρ + 2`
vertices. For `ρ = 1`: a triangle-free graph has `4e ≤ k²`. -/
theorem turan_all (ρ : ℕ) (A : Fin k → Fin k → ZT n)
    (hs : ∀ v w, Γ ⊢[PRAAx] ZT.eq (A v w) (A w v))
    (hb : ∀ v w, Γ ⊢[PRAAx] ZT.eq (A v w * A v w) (A v w)) (hfree : Free Γ ρ A) :
    Γ ⊢[PRAAx] zle (ZT.natLit (ρ + 1) * ZT.sumFin fun u => ZT.sumFin fun v => A u v)
      (ZT.natLit ρ * ZT.natLit (k * k)) := by
  have h := turan ρ A (fun _ => ZT.natLit 1) hs hb
    (fun _ => by apply ZT.derive; zsimp; ring) (fun u v => by apply ZT.derive; zsimp; ring) hfree
  refine zle_of_comb (zsl h) ?_ (nn_zsl _)
  zsimp
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, _root_.mul_one]
  push_cast
  ring

end LeanProofs.IPRA.Combinatorics.Turan
