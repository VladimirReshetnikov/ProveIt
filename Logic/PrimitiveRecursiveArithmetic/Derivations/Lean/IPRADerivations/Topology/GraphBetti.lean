import IPRADerivations.Topology.RationalHomology
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Graph Betti numbers

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/05_algebraic.tex`, Theorem A07
(`thm:graph-betti`), for a finite loopless graph with `v` vertices and `e` oriented edges `src i → tgt i`, its
`c` connected components (`graph`, `SimpleGraph.ConnectedComponent`), and the boundary (incidence) matrix
"assign to `u → w` the boundary `w − u`" (`incidence`):

* `transpose_apply`, `mem_ker_transpose`: the transposed boundary sends `φ` to `φ(tgt i) − φ(src i)`, so its
  kernel consists of the edge-invariant functions;
* `const_of_reachable`, `ker_equiv`: the edge-invariant functions are exactly the functions on the components,
  `ker Dᵀ ≅ ℚ^c`;
* `rank_incidence`: "Thus the boundary rank is `v − c`";
* `graph_betti`: `b_0 = c`, `b_1 = e − v + c` (via A02 of `Topology/RationalHomology`), and `χ = v − e`.
-/

namespace LeanProofs.IPRA.Topology.GraphBetti

open Module Matrix LeanProofs.IPRA.Topology.RationalHomology

variable {v e : ℕ} (src tgt : Fin e → Fin v)

/-- The underlying simple graph. -/
def graph : SimpleGraph (Fin v) where
  Adj a b := a ≠ b ∧ ∃ i, (src i = a ∧ tgt i = b) ∨ (src i = b ∧ tgt i = a)
  symm := ⟨fun _ _ ⟨h, i, hi⟩ => ⟨h.symm, i, hi.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The boundary matrix: column `i` is `tgt i − src i`. -/
def incidence : Matrix (Fin v) (Fin e) ℚ :=
  fun a i => (if tgt i = a then 1 else 0) - (if src i = a then 1 else 0)

theorem transpose_apply (φ : Fin v → ℚ) (i : Fin e) :
    ((incidence src tgt)ᵀ *ᵥ φ) i = φ (tgt i) - φ (src i) := by
  simp [incidence, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, ite_mul]

theorem mem_ker_transpose (φ : Fin v → ℚ) :
    φ ∈ LinearMap.ker (incidence src tgt)ᵀ.mulVecLin ↔ ∀ i, φ (tgt i) = φ (src i) := by
  rw [LinearMap.mem_ker, funext_iff]
  simp only [Matrix.mulVecLin_apply, transpose_apply, Pi.zero_apply, sub_eq_zero]

/-- An edge-invariant function is constant along walks. -/
theorem const_of_reachable {φ : Fin v → ℚ} (hφ : ∀ i, φ (tgt i) = φ (src i)) {a b : Fin v}
    (h : (graph src tgt).Reachable a b) : φ a = φ b := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons hadj _ ih =>
    obtain ⟨_, i, hi⟩ := hadj
    rcases hi with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [← ih, ← h₁, ← h₂, hφ i]
    · rw [← ih, ← h₁, ← h₂, hφ i]

open scoped Classical in
/-- `ker Dᵀ ≅ ℚ^c`. -/
theorem finrank_ker (hloop : ∀ i, src i ≠ tgt i) :
    finrank ℚ (LinearMap.ker (incidence src tgt)ᵀ.mulVecLin) =
      Fintype.card (graph src tgt).ConnectedComponent := by
  let Ψ : ((graph src tgt).ConnectedComponent → ℚ) →ₗ[ℚ] LinearMap.ker (incidence src tgt)ᵀ.mulVecLin :=
    LinearMap.codRestrict _ (LinearMap.funLeft ℚ ℚ (graph src tgt).connectedComponentMk) fun g => by
      rw [mem_ker_transpose]
      intro i
      simp only [LinearMap.funLeft_apply]
      rw [SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        (show (graph src tgt).Adj (src i) (tgt i) from ⟨hloop i, i, Or.inl ⟨rfl, rfl⟩⟩)]
  have hinj : Function.Injective Ψ := by
    intro g g' h
    funext C
    induction C using SimpleGraph.ConnectedComponent.ind with
    | h a => exact congrArg (fun x => x.1 a) h
  have hsurj : Function.Surjective Ψ := by
    intro φ
    refine ⟨fun C => φ.1 (Quot.out C), Subtype.ext (funext fun a => ?_)⟩
    have hφ := (mem_ker_transpose src tgt φ.1).mp φ.2
    show φ.1 (Quot.out ((graph src tgt).connectedComponentMk a)) = φ.1 a
    exact const_of_reachable src tgt hφ
      (SimpleGraph.ConnectedComponent.exact (Quot.out_eq ((graph src tgt).connectedComponentMk a)))
  rw [← (LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_fintype_fun_eq_card]

open scoped Classical in
/-- "Thus the boundary rank is `v − c`". -/
theorem rank_incidence (hloop : ∀ i, src i ≠ tgt i) :
    (incidence src tgt).rank + Fintype.card (graph src tgt).ConnectedComponent = v := by
  rw [← Matrix.rank_transpose, ← finrank_ker src tgt hloop, Matrix.rank]
  have := LinearMap.finrank_range_add_finrank_ker (incidence src tgt)ᵀ.mulVecLin
  rw [Module.finrank_fin_fun] at this
  exact this

open scoped Classical in
/-- A07: `b_0 = c`, `b_1 + v = e + c` (that is, `b_1 = e − v + c`), and `χ = b_0 − b_1 = v − e`. -/
theorem graph_betti (hloop : ∀ i, src i ≠ tgt i) :
    finrank ℚ (Hom (0 : (Fin v → ℚ) →ₗ[ℚ] (Fin 0 → ℚ)) (incidence src tgt).mulVecLin) =
        Fintype.card (graph src tgt).ConnectedComponent ∧
      finrank ℚ (Hom (incidence src tgt).mulVecLin (0 : (Fin 0 → ℚ) →ₗ[ℚ] (Fin e → ℚ))) + v =
        e + Fintype.card (graph src tgt).ConnectedComponent ∧
      (finrank ℚ (Hom (0 : (Fin v → ℚ) →ₗ[ℚ] (Fin 0 → ℚ)) (incidence src tgt).mulVecLin) : ℤ) -
        finrank ℚ (Hom (incidence src tgt).mulVecLin (0 : (Fin 0 → ℚ) →ₗ[ℚ] (Fin e → ℚ))) = v - e := by
  have hr := rank_incidence src tgt hloop
  have h₀ := betti (d₁ := (0 : (Fin v → ℚ) →ₗ[ℚ] (Fin 0 → ℚ))) (d₂ := (incidence src tgt).mulVecLin) (by simp)
  have h₁ := betti (d₁ := (incidence src tgt).mulVecLin) (d₂ := (0 : (Fin 0 → ℚ) →ₗ[ℚ] (Fin e → ℚ))) (by simp)
  rw [frz, Module.finrank_fin_fun] at h₀
  rw [frz, Module.finrank_fin_fun] at h₁
  rw [Matrix.rank] at hr
  refine ⟨by omega, by omega, by omega⟩

end LeanProofs.IPRA.Topology.GraphBetti
