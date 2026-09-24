/-
  THE COUNTABLE ANALOGUE OF THE FINITE-LABEL CLASSIFICATION (synthesis §15).

  For `λ = ω` the quotient `Q_λ` is `𝒫(ω)` modulo finite difference, and "definable"
  becomes "Baire measurable".  In that world the classification of admissible finite-label
  rules has a *different* answer from Theorem 12.12: a rule exists iff the group has a
  GLOBAL fixed label, not merely a fixed label for each single permutation.

  * `zero_one`: for a family `H` of homeomorphisms of a Baire space that is topologically
    transitive, every `H`-invariant Baire-measurable set is meagre or comeagre
    (generic ergodicity);
  * `generic_const`: an `H`-invariant map with Baire-measurable fibres into a finite set
    is constant on a comeagre set;
  * `fixed_label`: if moreover `f ∘ σ = ρ ∘ f` generically for a homeomorphism `σ`, then
    `ρ` fixes the generic value;
  * `Cantor.flip`, `Cantor.transitive`: finite changes act topologically transitively on
    `ι → Bool`;
  * `Cantor.global_fixed_point`: a finite-change-invariant, Baire-measurable labelling of
    `ι → Bool` that is generically equivariant for a group `Γ` acting on the index set and
    on the labels takes a generic value fixed by ALL of `Γ`.  With `ι = Fin m × ℕ` and `Γ`
    permuting the first coordinate this is the statement about `m`-tuples of subsets of
    `ω` modulo finite difference.

  Everything is proved; nothing is admitted.
-/
import Mathlib

open Set Filter Topology

namespace Cardinals.Countable

section Abstract

variable {X : Type*} [TopologicalSpace X]

/-- The family `H` of homeomorphisms is topologically transitive. -/
def TopTransitive (H : Set (X ≃ₜ X)) : Prop :=
  ∀ U V : Set X, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty → ∃ g ∈ H, ∃ x ∈ U, g x ∈ V

theorem residual_preimage (g : X ≃ₜ X) {s : Set X} (hs : s ∈ residual X) :
    g ⁻¹' s ∈ residual X :=
  tendsto_residual_of_isOpenMap g.continuous g.isOpenMap hs

variable [BaireSpace X]

/-- **Generic ergodicity (topological zero-one law).** -/
theorem zero_one (H : Set (X ≃ₜ X)) (htrans : TopTransitive H) (A : Set X)
    (hA : BaireMeasurableSet A) (hinv : ∀ g ∈ H, ∀ x, g x ∈ A ↔ x ∈ A) :
    A ∈ residual X ∨ Aᶜ ∈ residual X := by
  obtain ⟨U, hUo, hAU⟩ := hA.residualEq_isOpen
  obtain ⟨V, hVo, hAV⟩ := hA.compl.residualEq_isOpen
  have h1 : ∀ᶠ x in residual X, x ∈ A ↔ x ∈ U := hAU.mem_iff
  have h2 : ∀ᶠ x in residual X, x ∈ Aᶜ ↔ x ∈ V := hAV.mem_iff
  by_cases hU : U.Nonempty
  · by_cases hV : V.Nonempty
    · exfalso
      obtain ⟨g, hg, x, hxU, hxV⟩ := htrans U V hUo hU hVo hV
      have hR : {y | y ∈ A ↔ y ∈ U} ∩ g ⁻¹' {y | y ∈ Aᶜ ↔ y ∈ V} ∈ residual X :=
        inter_mem h1 (residual_preimage g h2)
      have hW : IsOpen (U ∩ g ⁻¹' V) := hUo.inter (hVo.preimage g.continuous)
      obtain ⟨y, ⟨hyU, hyV⟩, hy1, hy2⟩ :=
        (dense_of_mem_residual hR).inter_open_nonempty _ hW ⟨x, hxU, hxV⟩
      have hyA : y ∈ A := hy1.mpr hyU
      have hgy : g y ∈ Aᶜ := hy2.mpr hyV
      exact hgy ((hinv g hg y).mpr hyA)
    · left
      rw [not_nonempty_iff_eq_empty] at hV
      filter_upwards [h2] with x hx
      by_contra hxA
      have := hx.mp hxA
      rw [hV] at this
      exact this
  · right
    rw [not_nonempty_iff_eq_empty] at hU
    filter_upwards [h1] with x hx hxA
    have := hx.mp hxA
    rw [hU] at this
    exact this

variable [Nonempty X]

/-- An invariant Baire-measurable map into a finite set is generically constant. -/
theorem generic_const {F : Type*} [Finite F] (H : Set (X ≃ₜ X)) (htrans : TopTransitive H)
    (f : X → F) (hmeas : ∀ l, BaireMeasurableSet (f ⁻¹' {l}))
    (hinv : ∀ g ∈ H, ∀ x, f (g x) = f x) : ∃ l₀, ∀ᶠ x in residual X, f x = l₀ := by
  by_contra hcon
  have hcon' : ∀ l, ¬ ∀ᶠ x in residual X, f x = l := fun l h => hcon ⟨l, h⟩
  have hall : ∀ l, (f ⁻¹' {l})ᶜ ∈ residual X := by
    intro l
    rcases zero_one H htrans (f ⁻¹' {l}) (hmeas l)
      (fun g hg x => by simp only [mem_preimage, mem_singleton_iff, hinv g hg x]) with h | h
    · exact absurd h (hcon' l)
    · exact h
  have hinter : (⋂ l, (f ⁻¹' {l})ᶜ) ∈ residual X := (Filter.iInter_mem).mpr hall
  obtain ⟨x, hx⟩ := (dense_of_mem_residual hinter).nonempty
  exact (mem_iInter.mp hx (f x)) rfl

/-- If `f` is generically constant and generically `σ`-`ρ`-equivariant, `ρ` fixes the
generic value. -/
theorem fixed_label {F : Type*} (f : X → F) (l₀ : F) (hconst : ∀ᶠ x in residual X, f x = l₀)
    (σ : X ≃ₜ X) (ρ : F → F) (hequiv : ∀ᶠ x in residual X, f (σ x) = ρ (f x)) : ρ l₀ = l₀ := by
  have hR : {x | f x = l₀} ∩ σ ⁻¹' {x | f x = l₀} ∩ {x | f (σ x) = ρ (f x)} ∈ residual X :=
    inter_mem (inter_mem hconst (residual_preimage σ hconst)) hequiv
  obtain ⟨x, ⟨hx1, hx2⟩, hx3⟩ := (dense_of_mem_residual hR).nonempty
  have hx1' : f x = l₀ := hx1
  have hx2' : f (σ x) = l₀ := hx2
  have hx3' : f (σ x) = ρ (f x) := hx3
  rw [hx2', hx1'] at hx3'
  exact hx3'.symm

end Abstract

/-! ### Subsets of a countable set modulo finite difference -/

namespace Cantor

variable {ι : Type*}

/-- Flip the coordinates in the finite set `S`. -/
def flipFun [DecidableEq ι] (S : Finset ι) (x : ι → Bool) : ι → Bool :=
  fun k => if k ∈ S then !(x k) else x k

theorem flipFun_flipFun [DecidableEq ι] (S : Finset ι) (x : ι → Bool) :
    flipFun S (flipFun S x) = x := by
  funext k
  by_cases h : k ∈ S <;> simp [flipFun, h]

theorem continuous_flipFun [DecidableEq ι] (S : Finset ι) : Continuous (flipFun (ι := ι) S) := by
  refine continuous_pi (fun k => ?_)
  by_cases h : k ∈ S
  · simp only [flipFun, h, if_true]
    exact (continuous_of_discreteTopology (f := Bool.not)).comp (continuous_apply k)
  · simp only [flipFun, h, if_false]
    exact continuous_apply k

/-- A finite change, as a homeomorphism of the Cantor space `ι → Bool`. -/
def flip [DecidableEq ι] (S : Finset ι) : (ι → Bool) ≃ₜ (ι → Bool) where
  toFun := flipFun S
  invFun := flipFun S
  left_inv := flipFun_flipFun S
  right_inv := flipFun_flipFun S
  continuous_toFun := continuous_flipFun S
  continuous_invFun := continuous_flipFun S

/-- Reindexing by a permutation of the index set, as a homeomorphism. -/
def reindex (e : ι ≃ ι) : (ι → Bool) ≃ₜ (ι → Bool) where
  toFun := fun x => x ∘ e
  invFun := fun x => x ∘ e.symm
  left_inv := fun x => by funext k; simp
  right_inv := fun x => by funext k; simp
  continuous_toFun := continuous_pi fun k => continuous_apply (e k)
  continuous_invFun := continuous_pi fun k => continuous_apply (e.symm k)

/-- Finite changes act topologically transitively. -/
theorem transitive [DecidableEq ι] :
    TopTransitive (Set.range (flip (ι := ι))) := by
  intro U V hUo hU _ hV
  obtain ⟨x, hx⟩ := hU
  obtain ⟨y, hy⟩ := hV
  obtain ⟨I, u, hu, hIU⟩ := isOpen_pi_iff.mp hUo x hx
  -- `z` agrees with `x` on `I` and with `y` elsewhere
  let z : ι → Bool := fun k => if k ∈ I then x k else y k
  have hzU : z ∈ U := hIU (fun k hk => by
    have hk' : k ∈ I := hk
    simp only [z, hk', if_true]
    exact (hu k hk').2)
  let S : Finset ι := I.filter (fun k => x k ≠ y k)
  refine ⟨flip S, ⟨S, rfl⟩, z, hzU, ?_⟩
  have : flip S z = y := by
    funext k
    show flipFun S z k = y k
    by_cases hkI : k ∈ I
    · by_cases hxy : x k = y k
      · have hkS : k ∉ S := by simp [S, hxy]
        simp [flipFun, hkS, z, hkI, hxy]
      · have hkS : k ∈ S := by simp [S, hkI, hxy]
        simp only [flipFun, hkS, if_true, z, hkI]
        cases hx' : x k <;> cases hy' : y k <;> simp_all
    · have hkS : k ∉ S := by simp [S, hkI]
      simp [flipFun, hkS, z, hkI]
  rw [this]
  exact hy

/-- **The Baire-measurable classification needs a global fixed point.**

Let `f` label the points of `ι → Bool` by elements of a finite `Γ`-set `F`.  Suppose `f` has
Baire-measurable fibres, is invariant under finite changes, and is generically
equivariant: `f (x ∘ act γ) = γ • f x` for comeagre many `x`, for every `γ ∈ Γ`.  Then the
generic value of `f` is fixed by every element of `Γ`. -/
theorem global_fixed_point [DecidableEq ι] {F Γ : Type*} [Finite F] [Group Γ] [MulAction Γ F]
    (act : Γ → (ι ≃ ι)) (f : (ι → Bool) → F)
    (hmeas : ∀ l, BaireMeasurableSet (f ⁻¹' {l}))
    (hfin : ∀ (S : Finset ι) x, f (flipFun S x) = f x)
    (hequiv : ∀ γ : Γ, ∀ᶠ x in residual (ι → Bool), f (x ∘ act γ) = γ • f x) :
    ∃ l₀, (∀ᶠ x in residual (ι → Bool), f x = l₀) ∧ ∀ γ : Γ, γ • l₀ = l₀ := by
  obtain ⟨l₀, hl₀⟩ := generic_const (Set.range (flip (ι := ι))) transitive f hmeas
    (by rintro g ⟨S, rfl⟩ x; exact hfin S x)
  exact ⟨l₀, hl₀, fun γ => fixed_label f l₀ hl₀ (reindex (act γ)) (fun l => γ • l) (hequiv γ)⟩

end Cantor

/-! ### The two criteria differ -/

namespace Klein

/-- `a = (2 3)(4 5)`. -/
def a : Equiv.Perm (Fin 6) := Equiv.swap 2 3 * Equiv.swap 4 5
/-- `b = (0 1)(4 5)`. -/
def b : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 4 5

/-- The Klein four-group `{1, a, b, ab}` acting on six labels (three blocks of size two,
each non-identity element fixing exactly one block): every element fixes a label --
criterion `CF` of synthesis Theorem 12.12 -- but no label is fixed by all elements, so by
`Cantor.global_fixed_point` no Baire-measurable admissible rule exists. -/
theorem separation :
    (∃ l : Fin 6, a l = l) ∧ (∃ l : Fin 6, b l = l) ∧ (∃ l : Fin 6, (a * b) l = l) ∧
      ∀ l : Fin 6, a l ≠ l ∨ b l ≠ l := by
  refine ⟨⟨0, ?_⟩, ⟨2, ?_⟩, ⟨4, ?_⟩, fun l => ?_⟩
  · simp [a, Equiv.swap_apply_def]
  · simp [b, Equiv.swap_apply_def]
  · simp [a, b, Equiv.swap_apply_def]
  · fin_cases l <;> simp [a, b, Equiv.swap_apply_def]

theorem closed : a * a = 1 ∧ b * b = 1 ∧ a * b = b * a := by
  refine ⟨?_, ?_, ?_⟩ <;> ext l <;> fin_cases l <;> simp [a, b, Equiv.swap_apply_def]

end Klein

end Cardinals.Countable
