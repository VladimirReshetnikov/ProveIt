import IPRADerivations.Core.IntCertificates

/-!
# Flows across cuts: the balance identity, weak duality and the optimality certificate

Packets: `combinatorics/graph-ipra`, `tex/flows.tex`, Theorem 11.1 (`fl:main`, "Integral max-flow min-cut"), and
`combinatorics/Combinatorics-iPRA`, `graphs.tex`, result 30. The network has vertex set `Fin k`; the flow `F u v`
and the capacity `c u v` are matrices of integer terms (parallel arcs added up), and a cut `U` is a vector `x`.
The balance equations are `out(v) − in(v) = κ e_v`, where `e` is the excess vector (`+1` at the source, `−1` at
the sink, `0` elsewhere) and `κ` the value. As iPRA derivations:

* `cut_balance`: "Summing the balance equations over any cut `U` cancels every internal arc, including loops,
  and gives `k + f(δ⁻(U)) = f(δ⁺(U))`", for every `x` with `∑_v x_v e_v = 1` (the cut contains the source and
  not the sink);
* `weak_duality`: "`... ≤ c(δ⁺(U))`": for `0 ≤ F ≤ c` and `0 ≤ x ≤ 1`, the value is at most the capacity of the
  cut;
* `saturated_cut`: "Every original arc leaving `S` is saturated ... Every entering arc carries zero ...
  Substitution in the displayed balance identity gives equality": then `κ = c(δ⁺(S))`, so by `weak_duality` the
  flow is maximal and the cut minimal.
* `matching_cover`: the weak duality of Theorem 12.1 (`fl:hall`, "Kőnig, Hall and the deficiency formula"): a
  matching is at most as large as a vertex cover. For the table of the `a` matching edges against the `b`
  vertices, in which every edge has an end in the cover (row sums at least one) and every vertex lies on at
  most one matching edge and only if it is in the cover (column sums at most the cover bit `w_j`),
  `a ≤ ∑_j w_j`.

Not derived: the augmenting-path algorithm that produces such a flow and cut (the residual search and its
termination), path extraction, and the Menger and König–Hall consequences.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.FlowCuts

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

variable {n k : ℕ} {Γ : List (Fm PTm n)}

/-! ## Identities in a commutative ring -/

section Ring

variable {R : Type*} [CommRing R] (F c : Fin k → Fin k → R) (x : Fin k → R)

/-- Summing the net outflows over a cut leaves the arcs across it. -/
theorem net_sum :
    ∑ v, x v * (∑ w, F v w - ∑ u, F u v) =
      ∑ u, ∑ v, F u v * (x u * (1 - x v)) - ∑ u, ∑ v, F u v * (x v * (1 - x u)) := by
  have hL1 : ∑ v, x v * ∑ w, F v w = ∑ u, ∑ v, F u v * x u := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  have hL2 : ∑ v, x v * ∑ u, F u v = ∑ u, ∑ v, F u v * x v := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring
  have e : ∑ v, x v * (∑ w, F v w - ∑ u, F u v) = ∑ v, x v * ∑ w, F v w - ∑ v, x v * ∑ u, F u v := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  have r : ∑ u, ∑ v, F u v * (x u * (1 - x v)) - ∑ u, ∑ v, F u v * (x v * (1 - x u)) =
      ∑ u, ∑ v, F u v * x u - ∑ u, ∑ v, F u v * x v := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [e, hL1, hL2, r]

/-- Splitting a sum of residual capacities. -/
theorem residual_sum (g : Fin k → Fin k → R) :
    ∑ u, ∑ v, (c u v - F u v) * g u v = ∑ u, ∑ v, c u v * g u v - ∑ u, ∑ v, F u v * g u v := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun v _ => by ring

end Ring

/-! ## The derivations -/

/-- The balance identity of a cut: `κ + f(δ⁻(U)) = f(δ⁺(U))`. -/
theorem cut_balance (F : Fin k → Fin k → ZT n) (x e : Fin k → ZT n) (κ : ZT n)
    (hbal : ∀ v, Γ ⊢[PRAAx] ZT.eq ((ZT.sumFin fun w => F v w) - ZT.sumFin fun u => F u v) (κ * e v))
    (hx : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun v => x v * e v) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] ZT.eq
      (κ + ZT.sumFin fun u => ZT.sumFin fun v => F u v * (x v * (ZT.natLit 1 - x u)))
      (ZT.sumFin fun u => ZT.sumFin fun v => F u v * (x u * (ZT.natLit 1 - x v))) := by
  have hbal1 : ∀ v, ∑ w, ZT.toZ Γ (F v w) - ∑ u, ZT.toZ Γ (F u v) = ZT.toZ Γ κ * ZT.toZ Γ (e v) :=
    fun v => by
      have h := ZT.toZ_eq (hbal v)
      simpa only [ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_sumFin] using h
  have hx1 : ∑ v, ZT.toZ Γ (x v) * ZT.toZ Γ (e v) = 1 := by
    have h := ZT.toZ_eq hx
    simpa only [ZT.toZ_mul, ZT.toZ_sumFin, ZT.toZ_natLit, Nat.cast_one] using h
  have t : ∀ v, ZT.toZ Γ (x v) * (∑ w, ZT.toZ Γ (F v w) - ∑ u, ZT.toZ Γ (F u v)) =
      ZT.toZ Γ κ * (ZT.toZ Γ (x v) * ZT.toZ Γ (e v)) := fun v => by
    rw [hbal1 v]
    ring
  have L := net_sum (fun u v => ZT.toZ Γ (F u v)) (fun v => ZT.toZ Γ (x v))
  beta_reduce at L
  rw [Finset.sum_congr rfl fun v _ => t v, ← Finset.mul_sum, hx1, _root_.mul_one] at L
  apply ZT.derive
  zsimp
  linear_combination L

/-- Weak duality: the value of a feasible flow is at most the capacity of every cut. -/
theorem weak_duality (F c : Fin k → Fin k → ZT n) (x e : Fin k → ZT n) (κ : ZT n)
    (hbal : ∀ v, Γ ⊢[PRAAx] ZT.eq ((ZT.sumFin fun w => F v w) - ZT.sumFin fun u => F u v) (κ * e v))
    (hx : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun v => x v * e v) (ZT.natLit 1))
    (hF0 : ∀ u v, Γ ⊢[PRAAx] zle (ZT.natLit 0) (F u v)) (hcap : ∀ u v, Γ ⊢[PRAAx] zle (F u v) (c u v))
    (hx0 : ∀ v, Γ ⊢[PRAAx] zle (ZT.natLit 0) (x v)) (hx1 : ∀ v, Γ ⊢[PRAAx] zle (x v) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] zle κ (ZT.sumFin fun u => ZT.sumFin fun v => c u v * (x u * (ZT.natLit 1 - x v))) := by
  have E := ZT.toZ_eq (cut_balance F x e κ hbal hx)
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_sumFin, ZT.toZ_natLit, Nat.cast_one] at E
  have S := residual_sum (fun u v => ZT.toZ Γ (F u v)) (fun u v => ZT.toZ Γ (c u v))
    (fun u v => ZT.toZ Γ (x u) * (1 - ZT.toZ Γ (x v)))
  beta_reduce at S
  refine zle_of_comb (∑ u, ∑ v, zsl (hcap u v) * (ZT.toZ Γ (x u) * zsl (hx1 v)) +
      ∑ u, ∑ v, ZT.toZ Γ (F u v) * (ZT.toZ Γ (x v) * zsl (hx1 u))) ?_
    (nn_add
      (nn_sum _ _ fun u _ => nn_sum _ _ fun v _ =>
        nn_mul (nn_zsl _) (nn_mul (nn_zle0 (hx0 u)) (nn_zsl _)))
      (nn_sum _ _ fun u _ => nn_sum _ _ fun v _ =>
        nn_mul (nn_zle0 (hF0 u v)) (nn_mul (nn_zle0 (hx0 v)) (nn_zsl _))))
  zsimp
  rw [S]
  linear_combination (-1 : Groth (Q Γ)) * E

/-- The optimality certificate: a cut whose leaving arcs are saturated and whose entering arcs are empty has
capacity equal to the value. -/
theorem saturated_cut (F c : Fin k → Fin k → ZT n) (x e : Fin k → ZT n) (κ : ZT n)
    (hbal : ∀ v, Γ ⊢[PRAAx] ZT.eq ((ZT.sumFin fun w => F v w) - ZT.sumFin fun u => F u v) (κ * e v))
    (hx : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun v => x v * e v) (ZT.natLit 1))
    (hsat : ∀ u v, Γ ⊢[PRAAx] ZT.eq (F u v * (x u * (ZT.natLit 1 - x v)))
      (c u v * (x u * (ZT.natLit 1 - x v))))
    (hempty : ∀ u v, Γ ⊢[PRAAx] ZT.eq (F u v * (x v * (ZT.natLit 1 - x u))) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq κ (ZT.sumFin fun u => ZT.sumFin fun v => c u v * (x u * (ZT.natLit 1 - x v))) := by
  have E := ZT.toZ_eq (cut_balance F x e κ hbal hx)
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_sumFin, ZT.toZ_natLit, Nat.cast_one] at E
  have hsat1 : ∀ u v, ZT.toZ Γ (F u v) * (ZT.toZ Γ (x u) * (1 - ZT.toZ Γ (x v))) =
      ZT.toZ Γ (c u v) * (ZT.toZ Γ (x u) * (1 - ZT.toZ Γ (x v))) := fun u v => by
    have h := ZT.toZ_eq (hsat u v)
    simpa only [ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_one] using h
  have hempty1 : ∀ u v, ZT.toZ Γ (F u v) * (ZT.toZ Γ (x v) * (1 - ZT.toZ Γ (x u))) = 0 := fun u v => by
    have h := ZT.toZ_eq (hempty u v)
    simpa only [ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_one, Nat.cast_zero] using h
  have hin : ∑ u, ∑ v, ZT.toZ Γ (F u v) * (ZT.toZ Γ (x v) * (1 - ZT.toZ Γ (x u))) = 0 :=
    Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => hempty1 u v
  have hout : ∑ u, ∑ v, ZT.toZ Γ (F u v) * (ZT.toZ Γ (x u) * (1 - ZT.toZ Γ (x v))) =
      ∑ u, ∑ v, ZT.toZ Γ (c u v) * (ZT.toZ Γ (x u) * (1 - ZT.toZ Γ (x v))) :=
    Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => hsat1 u v
  rw [hin, hout] at E
  apply ZT.derive
  zsimp
  linear_combination E

/-- A matching is at most as large as a vertex cover: rows of sum at least one and column sums bounded by
the cover bits give `a ≤ ∑ w_j`. -/
theorem matching_cover {a b : ℕ} (T : Fin a → Fin b → ZT n) (w : Fin b → ZT n)
    (hr : ∀ i, Γ ⊢[PRAAx] zle (ZT.natLit 1) (ZT.sumFin fun j => T i j))
    (hc : ∀ j, Γ ⊢[PRAAx] zle (ZT.sumFin fun i => T i j) (w j)) :
    Γ ⊢[PRAAx] zle (ZT.natLit a) (ZT.sumFin w) := by
  have hsw : ∑ i, ∑ j, ZT.toZ Γ (T i j) = ∑ j, ∑ i, ZT.toZ Γ (T i j) := Finset.sum_comm
  refine zle_of_comb (∑ i, zsl (hr i) + ∑ j, zsl (hc j)) ?_
    (nn_add (nn_sum _ _ fun i _ => nn_zsl _) (nn_sum _ _ fun j _ => nn_zsl _))
  zsimp
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    _root_.mul_one]
  linear_combination (-1 : Groth (Q Γ)) * hsw

end LeanProofs.IPRA.Combinatorics.FlowCuts
