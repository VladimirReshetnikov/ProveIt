import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Rational homology: Betti numbers, invariance under chain-homotopy equivalence, collapses, polygon genera

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/05_algebraic.tex`, over any field `K` (in
the packet `ℚ`), for a chain complex around degree `k`: `X₂ --d₂--> X₁ --d₁--> X₀` with `d₁ ∘ d₂ = 0`, and
`H = ker d₁ / im d₂` (`Hom`):

* A02 (`prop:effective-homology`): `b_k = c_k − r_k − r_{k+1}` (`betti`), so `r_k + r_{k+1} ≤ c_k`
  (`rank_bound`), and a coordinate isomorphism `H_k ≅ K^{b_k}` (`normal_form`);
* A04 (`thm:chain-homotopy`), the rank count: chain maps `f`, `g` with supplied homotopies
  `g f = 1 + ∂h + h∂` and `f g = 1 + ∂h' + h'∂` induce mutually inverse maps on homology (`induced`,
  `induced_comp`), so the Betti numbers agree (`betti_eq`);
* A05 (`prop:collapse`), the Betti half: the collapse certificates `ri = 1` and `ir = 1 − ∂h − h∂` give equal
  Betti numbers (`collapse_betti`);
* A08 (`prop:polygon-genus`): "the coefficient of an edge in `D_2` is its signed number of traversals in the
  attaching word": `0` for the commutator word `∏ aᵢ bᵢ aᵢ⁻¹ bᵢ⁻¹` (`comm_coeff`) and `2` for the square word
  `a₁² ⋯ a_h²` (`square_coeff`); with `D_1 = 0` this gives `(b_0, b_1, b_2) = (1, 2g, 1)` (`orientable_betti`)
  and `(1, h − 1, 0)` (`nonorientable_betti`), so `χ = 2 − 2g` and `χ = 2 − h`.
-/

namespace LeanProofs.IPRA.Topology.RationalHomology

open Module

variable {K : Type*} [Field K]
variable {X₂ X₁ X₀ : Type*} [AddCommGroup X₂] [Module K X₂] [AddCommGroup X₁] [Module K X₁]
  [AddCommGroup X₀] [Module K X₀]

/-- `H = ker d₁ / im d₂`. -/
abbrev Hom (d₁ : X₁ →ₗ[K] X₀) (d₂ : X₂ →ₗ[K] X₁) : Type _ :=
  LinearMap.ker d₁ ⧸ (LinearMap.range d₂).comap (LinearMap.ker d₁).subtype

theorem range_le_ker {d₁ : X₁ →ₗ[K] X₀} {d₂ : X₂ →ₗ[K] X₁} (h : d₁ ∘ₗ d₂ = 0) :
    LinearMap.range d₂ ≤ LinearMap.ker d₁ := by
  rintro _ ⟨y, rfl⟩
  rw [LinearMap.mem_ker, ← LinearMap.comp_apply, h, LinearMap.zero_apply]

/-- A02: `b_k + r_k + r_{k+1} = c_k`. -/
theorem betti [FiniteDimensional K X₁] {d₁ : X₁ →ₗ[K] X₀} {d₂ : X₂ →ₗ[K] X₁} (h : d₁ ∘ₗ d₂ = 0) :
    finrank K (Hom d₁ d₂) + finrank K (LinearMap.range d₁) + finrank K (LinearMap.range d₂) = finrank K X₁ := by
  have e₁ : finrank K (Hom d₁ d₂) + finrank K ((LinearMap.range d₂).comap (LinearMap.ker d₁).subtype) =
      finrank K (LinearMap.ker d₁) :=
    Submodule.finrank_quotient_add_finrank ((LinearMap.range d₂).comap (LinearMap.ker d₁).subtype)
  have e₂ : finrank K ((LinearMap.range d₂).comap (LinearMap.ker d₁).subtype) = finrank K (LinearMap.range d₂) :=
    (Submodule.comapSubtypeEquivOfLe (range_le_ker h)).finrank_eq
  have e₃ : finrank K (LinearMap.range d₁) + finrank K (LinearMap.ker d₁) = finrank K X₁ :=
    LinearMap.finrank_range_add_finrank_ker d₁
  omega

/-- A02: `r_k + r_{k+1} ≤ c_k`. -/
theorem rank_bound [FiniteDimensional K X₁] {d₁ : X₁ →ₗ[K] X₀} {d₂ : X₂ →ₗ[K] X₁} (h : d₁ ∘ₗ d₂ = 0) :
    finrank K (LinearMap.range d₁) + finrank K (LinearMap.range d₂) ≤ finrank K X₁ := by
  have := betti h
  omega

/-- A02: the coordinate isomorphism `H_k ≅ K^{b_k}`. -/
theorem normal_form [FiniteDimensional K X₁] (d₁ : X₁ →ₗ[K] X₀) (d₂ : X₂ →ₗ[K] X₁) :
    Nonempty (Hom d₁ d₂ ≃ₗ[K] (Fin (finrank K (Hom d₁ d₂)) → K)) :=
  ⟨LinearEquiv.ofFinrankEq _ _ (by simp)⟩

/-! ## A04: the rank count -/

variable {Y₂ Y₁ Y₀ : Type*} [AddCommGroup Y₂] [Module K Y₂] [AddCommGroup Y₁] [Module K Y₁]
  [AddCommGroup Y₀] [Module K Y₀]
variable {d₁ : X₁ →ₗ[K] X₀} {d₂ : X₂ →ₗ[K] X₁} {e₁ : Y₁ →ₗ[K] Y₀} {e₂ : Y₂ →ₗ[K] Y₁}

/-- The cycle map of a chain map. -/
def cyc (f₁ : X₁ →ₗ[K] Y₁) (f₀ : X₀ →ₗ[K] Y₀) (c₁ : e₁ ∘ₗ f₁ = f₀ ∘ₗ d₁) :
    LinearMap.ker d₁ →ₗ[K] LinearMap.ker e₁ :=
  LinearMap.codRestrict (LinearMap.ker e₁) (f₁ ∘ₗ (LinearMap.ker d₁).subtype) fun x => by
    have := LinearMap.congr_fun c₁ x.1
    simp only [LinearMap.comp_apply] at this
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype, this, LinearMap.mem_ker.mp x.2,
      map_zero]

/-- The map induced on homology by a chain map. -/
def induced (f₂ : X₂ →ₗ[K] Y₂) (f₁ : X₁ →ₗ[K] Y₁) (f₀ : X₀ →ₗ[K] Y₀) (c₁ : e₁ ∘ₗ f₁ = f₀ ∘ₗ d₁)
    (c₂ : e₂ ∘ₗ f₂ = f₁ ∘ₗ d₂) : Hom d₁ d₂ →ₗ[K] Hom e₁ e₂ :=
  Submodule.mapQ _ _ (cyc f₁ f₀ c₁) fun x hx => by
    obtain ⟨y, hy⟩ := hx
    refine ⟨f₂ y, ?_⟩
    have := LinearMap.congr_fun c₂ y
    simp only [LinearMap.comp_apply] at this
    rw [this, hy]
    rfl

/-- A04: a supplied homotopy `g f = 1 + ∂h + h∂` makes the induced maps compose to the identity. -/
theorem induced_comp (f₂ : X₂ →ₗ[K] Y₂) (f₁ : X₁ →ₗ[K] Y₁) (f₀ : X₀ →ₗ[K] Y₀) (c₁ : e₁ ∘ₗ f₁ = f₀ ∘ₗ d₁)
    (c₂ : e₂ ∘ₗ f₂ = f₁ ∘ₗ d₂) (g₂ : Y₂ →ₗ[K] X₂) (g₁ : Y₁ →ₗ[K] X₁) (g₀ : Y₀ →ₗ[K] X₀)
    (c₁' : d₁ ∘ₗ g₁ = g₀ ∘ₗ e₁) (c₂' : d₂ ∘ₗ g₂ = g₁ ∘ₗ e₂) (h₁ : X₁ →ₗ[K] X₂) (h₀ : X₀ →ₗ[K] X₁)
    (hh : g₁ ∘ₗ f₁ = LinearMap.id + d₂ ∘ₗ h₁ + h₀ ∘ₗ d₁) :
    induced g₂ g₁ g₀ c₁' c₂' ∘ₗ induced f₂ f₁ f₀ c₁ c₂ = LinearMap.id := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, induced, Submodule.mapQ_apply, LinearMap.id_apply]
  rw [Submodule.Quotient.eq]
  refine ⟨h₁ x.1, ?_⟩
  have hx := LinearMap.mem_ker.mp x.2
  have := LinearMap.congr_fun hh x.1
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply, hx, map_zero, add_zero] at this
  simp only [Submodule.coe_subtype, Submodule.coe_sub, cyc, LinearMap.codRestrict_apply, LinearMap.comp_apply]
  rw [this]
  abel

/-- A04, the rank count: chain-homotopy inverse chain maps preserve the Betti number. -/
theorem betti_eq (f₂ : X₂ →ₗ[K] Y₂) (f₁ : X₁ →ₗ[K] Y₁) (f₀ : X₀ →ₗ[K] Y₀) (c₁ : e₁ ∘ₗ f₁ = f₀ ∘ₗ d₁)
    (c₂ : e₂ ∘ₗ f₂ = f₁ ∘ₗ d₂) (g₂ : Y₂ →ₗ[K] X₂) (g₁ : Y₁ →ₗ[K] X₁) (g₀ : Y₀ →ₗ[K] X₀)
    (c₁' : d₁ ∘ₗ g₁ = g₀ ∘ₗ e₁) (c₂' : d₂ ∘ₗ g₂ = g₁ ∘ₗ e₂) (h₁ : X₁ →ₗ[K] X₂) (h₀ : X₀ →ₗ[K] X₁)
    (hh : g₁ ∘ₗ f₁ = LinearMap.id + d₂ ∘ₗ h₁ + h₀ ∘ₗ d₁) (k₁ : Y₁ →ₗ[K] Y₂) (k₀ : Y₀ →ₗ[K] Y₁)
    (hk : f₁ ∘ₗ g₁ = LinearMap.id + e₂ ∘ₗ k₁ + k₀ ∘ₗ e₁) :
    finrank K (Hom d₁ d₂) = finrank K (Hom e₁ e₂) :=
  (LinearEquiv.ofLinear (induced f₂ f₁ f₀ c₁ c₂) (induced g₂ g₁ g₀ c₁' c₂')
    (induced_comp g₂ g₁ g₀ c₁' c₂' f₂ f₁ f₀ c₁ c₂ k₁ k₀ hk)
    (induced_comp f₂ f₁ f₀ c₁ c₂ g₂ g₁ g₀ c₁' c₂' h₁ h₀ hh)).finrank_eq

/-- A05, the Betti half: the collapse certificates `r i = 1` (on `K'`) and `i r = 1 − ∂h − h∂` (on `K`). -/
theorem collapse_betti (i₂ : Y₂ →ₗ[K] X₂) (i₁ : Y₁ →ₗ[K] X₁) (i₀ : Y₀ →ₗ[K] X₀) (c₁ : d₁ ∘ₗ i₁ = i₀ ∘ₗ e₁)
    (c₂ : d₂ ∘ₗ i₂ = i₁ ∘ₗ e₂) (r₂ : X₂ →ₗ[K] Y₂) (r₁ : X₁ →ₗ[K] Y₁) (r₀ : X₀ →ₗ[K] Y₀)
    (c₁' : e₁ ∘ₗ r₁ = r₀ ∘ₗ d₁) (c₂' : e₂ ∘ₗ r₂ = r₁ ∘ₗ d₂) (hri : r₁ ∘ₗ i₁ = LinearMap.id)
    (h₁ : X₁ →ₗ[K] X₂) (h₀ : X₀ →ₗ[K] X₁) (hir : i₁ ∘ₗ r₁ = LinearMap.id - d₂ ∘ₗ h₁ - h₀ ∘ₗ d₁) :
    finrank K (Hom e₁ e₂) = finrank K (Hom d₁ d₂) :=
  betti_eq i₂ i₁ i₀ c₁ c₂ r₂ r₁ r₀ c₁' c₂' 0 0
    (by rw [hri, LinearMap.comp_zero, LinearMap.zero_comp, add_zero, add_zero]) (-h₁) (-h₀)
    (by rw [hir, LinearMap.comp_neg, LinearMap.neg_comp, sub_eq_add_neg, sub_eq_add_neg])

/-! ## A08: polygon genera -/

/-- The signed number of traversals of edge `e` in a word of (edge, orientation) letters. -/
def coeff {m : ℕ} (w : List (Fin m × Bool)) (e : Fin m) : ℤ :=
  (w.map fun l => if l.1 = e then (if l.2 then 1 else -1) else 0).sum

theorem coeff_append {m : ℕ} (w w' : List (Fin m × Bool)) (e : Fin m) :
    coeff (w ++ w') e = coeff w e + coeff w' e := by
  simp [coeff, List.sum_append]

theorem coeff_flatMap {m : ℕ} {ι : Type*} (l : List ι) (f : ι → List (Fin m × Bool)) (e : Fin m) :
    coeff (l.flatMap f) e = (l.map fun i => coeff (f i) e).sum := by
  induction l with
  | nil => simp [coeff]
  | cons i l ih => rw [List.flatMap_cons, coeff_append, ih, List.map_cons, List.sum_cons]

/-- The commutator word `∏_{i<g} aᵢ bᵢ aᵢ⁻¹ bᵢ⁻¹` on the edges `aᵢ = 2i`, `bᵢ = 2i + 1`. -/
def commWord (g : ℕ) : List (Fin (2 * g) × Bool) :=
  (List.finRange g).flatMap fun i =>
    [(⟨2 * i.val, by omega⟩, true), (⟨2 * i.val + 1, by omega⟩, true), (⟨2 * i.val, by omega⟩, false),
      (⟨2 * i.val + 1, by omega⟩, false)]

/-- A08: every edge has coefficient `0` in the commutator word, so `D_2 = 0`. -/
theorem comm_coeff (g : ℕ) (e : Fin (2 * g)) : coeff (commWord g) e = 0 := by
  rw [commWord, coeff_flatMap]
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  simp only [coeff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  split_ifs <;> simp_all

/-- The square word `a₁² ⋯ a_h²`. -/
def squareWord (h : ℕ) : List (Fin h × Bool) := (List.finRange h).flatMap fun i => [(i, true), (i, true)]

/-- A08: every edge has coefficient `2` in the square word. -/
theorem square_coeff (h : ℕ) (e : Fin h) : coeff (squareWord h) e = 2 := by
  rw [squareWord, coeff_flatMap, ← Fin.sum_univ_def]
  have : ∀ i : Fin h, coeff [(i, true), (i, true)] e = if i = e then 2 else 0 := by
    intro i
    simp only [coeff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    split_ifs <;> norm_num
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The attaching-word columns. -/
def commVec (g : ℕ) : Fin (2 * g) → ℚ := fun e => (coeff (commWord g) e : ℚ)

def squareVec (h : ℕ) : Fin h → ℚ := fun e => (coeff (squareWord h) e : ℚ)

theorem frz {A B : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B] :
    finrank K (LinearMap.range (0 : A →ₗ[K] B)) = 0 := by
  rw [LinearMap.range_zero, finrank_bot]

theorem frs {A : Type*} [AddCommGroup A] [Module K A] (v : A) :
    finrank K (LinearMap.range (LinearMap.toSpanSingleton K A v)) = finrank K (K ∙ v) := by
  rw [LinearMap.range_toSpanSingleton]

/-- `b = (finrank of H₀, H₁, H₂)` for the one-vertex complex `K --D₂--> K^m --D₁ = 0--> K`. -/
theorem polygon_betti {m : ℕ} (v : Fin m → K) :
    finrank K (Hom (0 : K →ₗ[K] (Fin 0 → K)) (0 : (Fin m → K) →ₗ[K] K)) = 1 ∧
    finrank K (Hom (0 : (Fin m → K) →ₗ[K] K) (LinearMap.toSpanSingleton K _ v)) +
      finrank K (K ∙ v) = m ∧
    finrank K (Hom (LinearMap.toSpanSingleton K _ v) (0 : (Fin 0 → K) →ₗ[K] K)) + finrank K (K ∙ v) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · have := betti (d₁ := (0 : K →ₗ[K] (Fin 0 → K))) (d₂ := (0 : (Fin m → K) →ₗ[K] K)) (by simp)
    rw [frz, frz, add_zero, add_zero, Module.finrank_self] at this
    exact this
  · have := betti (d₁ := (0 : (Fin m → K) →ₗ[K] K)) (d₂ := LinearMap.toSpanSingleton K _ v) (by simp)
    rw [frz, add_zero, frs, Module.finrank_fin_fun] at this
    exact this
  · have := betti (d₁ := LinearMap.toSpanSingleton K _ v) (d₂ := (0 : (Fin 0 → K) →ₗ[K] K)) (by simp)
    rw [frz, add_zero, frs, Module.finrank_self] at this
    exact this

/-- A08, orientable: `(b_0, b_1, b_2) = (1, 2g, 1)`, `χ = 2 − 2g`. -/
theorem orientable_betti (g : ℕ) :
    finrank ℚ (Hom (0 : ℚ →ₗ[ℚ] (Fin 0 → ℚ)) (0 : (Fin (2 * g) → ℚ) →ₗ[ℚ] ℚ)) = 1 ∧
    finrank ℚ (Hom (0 : (Fin (2 * g) → ℚ) →ₗ[ℚ] ℚ) (LinearMap.toSpanSingleton ℚ _ (commVec g))) = 2 * g ∧
    finrank ℚ (Hom (LinearMap.toSpanSingleton ℚ _ (commVec g)) (0 : (Fin 0 → ℚ) →ₗ[ℚ] ℚ)) = 1 := by
  have hv : commVec g = 0 := funext fun e => by simp [commVec, comm_coeff]
  obtain ⟨h₀, h₁, h₂⟩ := polygon_betti (commVec g)
  rw [hv, Submodule.span_zero_singleton, finrank_bot, add_zero] at h₁ h₂
  rw [hv]
  exact ⟨h₀, h₁, h₂⟩

/-- A08, nonorientable: `(b_0, b_1, b_2) = (1, h − 1, 0)`, `χ = 2 − h`. -/
theorem nonorientable_betti (h : ℕ) (hh : 1 ≤ h) :
    finrank ℚ (Hom (0 : ℚ →ₗ[ℚ] (Fin 0 → ℚ)) (0 : (Fin h → ℚ) →ₗ[ℚ] ℚ)) = 1 ∧
    finrank ℚ (Hom (0 : (Fin h → ℚ) →ₗ[ℚ] ℚ) (LinearMap.toSpanSingleton ℚ _ (squareVec h))) = h - 1 ∧
    finrank ℚ (Hom (LinearMap.toSpanSingleton ℚ _ (squareVec h)) (0 : (Fin 0 → ℚ) →ₗ[ℚ] ℚ)) = 0 := by
  have hv : squareVec h ≠ 0 := fun e => by
    have := congrFun e ⟨0, hh⟩
    simp [squareVec, square_coeff] at this
  obtain ⟨h₀, h₁, h₂⟩ := polygon_betti (squareVec h)
  rw [finrank_span_singleton hv] at h₁ h₂
  exact ⟨h₀, by omega, by omega⟩

end LeanProofs.IPRA.Topology.RationalHomology
