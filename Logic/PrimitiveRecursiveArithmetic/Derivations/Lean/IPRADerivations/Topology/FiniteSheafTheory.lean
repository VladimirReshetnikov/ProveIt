import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Finite sheaves: the canonical-cover test, restriction, stalkwise isomorphisms and subsheaves

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/05_algebraic.tex`, "Finite sheaves with
executable gluing", for arbitrary presheaf tables on a finite space (points `Fin k`, a family of opens closed
under intersection, and least neighbourhoods `N_x`):

* `sheaf_of_canonical`, `canonical_of_sheaf`, `canonical_iff_sheaf` (A11, `thm:canonical-sheaf`): a presheaf has
  unique gluing on every open cover iff it has unique gluing on the canonical covers `(N_x)_{x ∈ U}`
  ("select the least index `i(x)` with `x ∈ U_{i(x)}`, and put `t_x = s_{i(x)}|_{N_x}` … Canonical uniqueness on
  `U_i` therefore gives `s|_{U_i} = s_i`");
* `nbhd_within`, `restrict_sheaf` (A13): for an open `W`, the canonical neighbourhoods of the points of `W` lie
  in `W`, and the sheaf condition for opens of `W` is the sheaf condition of `F` ("Existence and uniqueness are
  inherited unchanged");
* `local_eq` (A14 for arbitrary sheaves): sections with equal restrictions to every `N_x` are equal;
* `stalk_inj`, `stalk_surj` (A15): a natural transformation of sheaves bijective on every `N_x` is injective and
  surjective on every open;
* `sub_sheaf`, `equalizer_local`, `equalizer_stable` (A16): a restriction-stable local family of subsets of a
  sheaf is a sheaf, and the equalizer of two morphisms into a sheaf is such a family.

A matching family is stated as "equal restrictions to every open `W` inside both members", which by
restriction transitivity is equivalent to equality on the open intersections `U_i ∩ U_j`. Covers are indexed by
an arbitrary type (the canonical cover of `U` by its points `{x // x ∈ U}`).
-/

namespace LeanProofs.IPRA.Topology.FiniteSheafTheory

variable {k : ℕ}

/-- A finite space: opens closed under intersection, with least open neighbourhoods. -/
structure Space (k : ℕ) where
  IsOpen : Finset (Fin k) → Prop
  inter : ∀ {U V}, IsOpen U → IsOpen V → IsOpen (U ∩ V)
  N : Fin k → Finset (Fin k)
  N_open : ∀ x, IsOpen (N x)
  mem_N : ∀ x, x ∈ N x
  N_least : ∀ {U x}, IsOpen U → x ∈ U → N x ⊆ U

/-- A presheaf of tables: sections over each open, and restrictions satisfying `ρ_{U,U} = 1` and
`ρ_{V,W} ρ_{U,V} = ρ_{U,W}`. -/
structure Presheaf (X : Space k) where
  F : Finset (Fin k) → Type
  ρ : ∀ {U V : Finset (Fin k)}, V ⊆ U → F U → F V
  ρ_id : ∀ {U} (s : F U), ρ (Finset.Subset.refl U) s = s
  ρ_comp : ∀ {U V W : Finset (Fin k)} (h₁ : V ⊆ U) (h₂ : W ⊆ V) (s : F U), ρ h₂ (ρ h₁ s) = ρ (h₂.trans h₁) s

variable {X : Space k} (P : Presheaf X)

/-- A matching family on a cover `(V_i)`. -/
def Match {ι : Type} (V : ι → Finset (Fin k)) (s : ∀ i, P.F (V i)) : Prop :=
  ∀ i j W (hi : W ⊆ V i) (hj : W ⊆ V j), X.IsOpen W → P.ρ hi (s i) = P.ρ hj (s j)

/-- Unique gluing on every open cover. -/
def Sheaf : Prop :=
  ∀ (U : Finset (Fin k)) (ι : Type) (V : ι → Finset (Fin k)) (hV : ∀ i, V i ⊆ U), X.IsOpen U →
    (∀ i, X.IsOpen (V i)) → (∀ x ∈ U, ∃ i, x ∈ V i) → ∀ s : ∀ i, P.F (V i), Match P V s →
    ∃! g : P.F U, ∀ i, P.ρ (hV i) g = s i

/-- Matching on the canonical cover of `U`. -/
def CMatch (U : Finset (Fin k)) (t : ∀ x, x ∈ U → P.F (X.N x)) : Prop :=
  ∀ x hx y hy W (h₁ : W ⊆ X.N x) (h₂ : W ⊆ X.N y), X.IsOpen W → P.ρ h₁ (t x hx) = P.ρ h₂ (t y hy)

/-- Unique gluing on the canonical covers `(N_x)_{x ∈ U}`. -/
def Canonical : Prop :=
  ∀ (U : Finset (Fin k)) (hU : X.IsOpen U) (t : ∀ x, x ∈ U → P.F (X.N x)), CMatch P U t →
    ∃! g : P.F U, ∀ x (hx : x ∈ U), P.ρ (X.N_least hU hx) g = t x hx

variable {P}

/-- The restrictions of one section to the canonical cover match. -/
theorem cmatch_restrict {U V : Finset (Fin k)} (hV : X.IsOpen V) (hVU : V ⊆ U) (g : P.F U) :
    CMatch P V fun x hx => P.ρ ((X.N_least hV hx).trans hVU) g := by
  intro x hx y hy W h₁ h₂ _
  rw [P.ρ_comp, P.ρ_comp]

/-- A14: on a canonical presheaf, sections with equal restrictions to every `N_x` are equal. -/
theorem local_eq (hP : Canonical P) {U : Finset (Fin k)} (hU : X.IsOpen U) {s t : P.F U}
    (h : ∀ x (hx : x ∈ U), P.ρ (X.N_least hU hx) s = P.ρ (X.N_least hU hx) t) : s = t := by
  obtain ⟨g, _, hg⟩ := hP U hU _ (cmatch_restrict (P := P) hU (Finset.Subset.refl U) s)
  have es := hg s fun x hx => rfl
  have et := hg t fun x hx => (h x hx).symm
  rw [es, et]

/-- A11, `⇐`: unique canonical gluing gives unique gluing on every open cover. -/
theorem sheaf_of_canonical (hP : Canonical P) : Sheaf P := by
  intro U ι V hV hU hVo hcov s hs
  classical
  let i : ∀ x, x ∈ U → ι := fun x hx => Classical.choose (hcov x hx)
  have hi : ∀ x (hx : x ∈ U), x ∈ V (i x hx) := fun x hx => Classical.choose_spec (hcov x hx)
  let t : ∀ x, x ∈ U → P.F (X.N x) := fun x hx => P.ρ (X.N_least (hVo _) (hi x hx)) (s (i x hx))
  have ht : CMatch P U t := by
    intro x hx y hy W h₁ h₂ hW
    simp only [t, P.ρ_comp]
    exact hs _ _ W _ _ hW
  obtain ⟨g, hg, hguniq⟩ := hP U hU t ht
  -- every gluing of `(s_i)` is a canonical gluing of `t`
  have canon : ∀ g' : P.F U, (∀ j, P.ρ (hV j) g' = s j) →
      ∀ x (hx : x ∈ U), P.ρ (X.N_least hU hx) g' = t x hx := by
    intro g' hg' x hx
    have := congrArg (P.ρ (X.N_least (hVo _) (hi x hx))) (hg' (i x hx))
    rw [P.ρ_comp] at this
    exact this
  refine ⟨g, ?_, fun g' hg' => hguniq g' (canon g' hg')⟩
  intro j
  -- canonical uniqueness on `V j`
  obtain ⟨_, _, huniq⟩ := hP (V j) (hVo j) _ (cmatch_restrict (P := P) (hVo j) (Finset.Subset.refl _) (s j))
  have h₁ := huniq (s j) fun x hx => rfl
  have h₂ := huniq (P.ρ (hV j) g) fun x hx => by
    rw [P.ρ_comp]
    have e := hg x (hV j hx)
    calc P.ρ ((X.N_least (hVo j) hx).trans (hV j)) g = P.ρ (X.N_least hU (hV j hx)) g := rfl
      _ = t x (hV j hx) := e
      _ = P.ρ ((X.N_least (hVo j) hx).trans (Finset.Subset.refl _)) (s j) :=
          hs _ _ (X.N x) _ _ (X.N_open x)
  rw [h₂, ← h₁]

/-- A11, `⇒`: the canonical covers are covers. -/
theorem canonical_of_sheaf (hP : Sheaf P) : Canonical P := by
  intro U hU t ht
  exact hP U {x // x ∈ U} (fun x => X.N x.1) (fun x => X.N_least hU x.2) hU (fun x => X.N_open x.1)
    (fun x hx => ⟨⟨x, hx⟩, X.mem_N x⟩) (fun x => t x.1 x.2)
    (fun x y W hx hy hW => ht x.1 x.2 y.1 y.2 W hx hy hW) |>.imp fun g ⟨hg, hu⟩ =>
      ⟨fun x hx => hg ⟨x, hx⟩, fun g' hg' => hu g' fun x => hg' x.1 x.2⟩

/-- A11 (`thm:canonical-sheaf`). -/
theorem canonical_iff_sheaf : Canonical P ↔ Sheaf P := ⟨sheaf_of_canonical, canonical_of_sheaf⟩

/-! ## A13 -/

/-- The canonical neighbourhoods of the points of an open `W` lie in `W`, so the canonical cover of an open
`U ⊆ W` is a cover inside `W`. -/
theorem nbhd_within {W : Finset (Fin k)} (hW : X.IsOpen W) {x : Fin k} (hx : x ∈ W) : X.N x ⊆ W :=
  X.N_least hW hx

/-- A13: the restriction `F|_W` (the same tables on the opens inside `W`) satisfies the sheaf condition. -/
theorem restrict_sheaf (hP : Sheaf P) {W : Finset (Fin k)} (U : Finset (Fin k)) (_ : U ⊆ W) (ι : Type)
    (V : ι → Finset (Fin k)) (hV : ∀ i, V i ⊆ U) (hU : X.IsOpen U) (hVo : ∀ i, X.IsOpen (V i))
    (hcov : ∀ x ∈ U, ∃ i, x ∈ V i) (s : ∀ i, P.F (V i)) (hs : Match P V s) :
    ∃! g : P.F U, ∀ i, P.ρ (hV i) g = s i :=
  hP U ι V hV hU hVo hcov s hs

/-! ## A15 -/

variable {Q : Presheaf X}

/-- A morphism of presheaves: maps commuting with restrictions. -/
structure Hom (P Q : Presheaf X) where
  α : ∀ U, P.F U → Q.F U
  nat : ∀ {U V} (h : V ⊆ U) (s : P.F U), α V (P.ρ h s) = Q.ρ h (α U s)

/-- A15, injectivity: if every `α_{N_x}` is injective, so is every `α_U`. -/
theorem stalk_inj (hP : Canonical P) (φ : Hom P Q) (hinj : ∀ x, Function.Injective (φ.α (X.N x)))
    {U : Finset (Fin k)} (hU : X.IsOpen U) : Function.Injective (φ.α U) := by
  intro s t h
  refine local_eq hP hU fun x hx => hinj x ?_
  rw [φ.nat, φ.nat, h]

/-- A15, surjectivity: if every `α_{N_x}` is bijective, every `α_U` is surjective. -/
theorem stalk_surj (hP : Canonical P) (hQ : Canonical Q) (φ : Hom P Q)
    (hinj : ∀ x, Function.Injective (φ.α (X.N x))) (hsurj : ∀ x, Function.Surjective (φ.α (X.N x)))
    {U : Finset (Fin k)} (hU : X.IsOpen U) : Function.Surjective (φ.α U) := by
  intro g
  classical
  let t : ∀ x, x ∈ U → P.F (X.N x) := fun x hx => Classical.choose (hsurj x (Q.ρ (X.N_least hU hx) g))
  have ht : ∀ x (hx : x ∈ U), φ.α _ (t x hx) = Q.ρ (X.N_least hU hx) g :=
    fun x hx => Classical.choose_spec (hsurj x _)
  have hm : CMatch P U t := by
    intro x hx y hy W h₁ h₂ hW
    refine stalk_inj hP φ hinj hW ?_
    rw [φ.nat, φ.nat, ht x hx, ht y hy, Q.ρ_comp, Q.ρ_comp]
  obtain ⟨s, hs, _⟩ := hP U hU t hm
  refine ⟨s, local_eq hQ hU fun x hx => ?_⟩
  rw [← φ.nat, hs x hx, ht x hx]

/-! ## A16 -/

/-- The subpresheaf of sections satisfying a restriction-stable predicate. -/
def Sub (S : ∀ U, P.F U → Prop) (stab : ∀ {U V} (h : V ⊆ U) (s : P.F U), S U s → S V (P.ρ h s)) :
    Presheaf X where
  F U := {s : P.F U // S U s}
  ρ h s := ⟨P.ρ h s.1, stab h s.1 s.2⟩
  ρ_id s := Subtype.ext (P.ρ_id s.1)
  ρ_comp h₁ h₂ s := Subtype.ext (P.ρ_comp h₁ h₂ s.1)

/-- A16: a restriction-stable local family of subsets of a sheaf is a sheaf. -/
theorem sub_sheaf (hP : Sheaf P) (S : ∀ U, P.F U → Prop)
    (stab : ∀ {U V} (h : V ⊆ U) (s : P.F U), S U s → S V (P.ρ h s))
    (loc : ∀ (U : Finset (Fin k)) (ι : Type) (V : ι → Finset (Fin k)) (hV : ∀ i, V i ⊆ U), X.IsOpen U →
      (∀ i, X.IsOpen (V i)) → (∀ x ∈ U, ∃ i, x ∈ V i) → ∀ s : P.F U, (∀ i, S (V i) (P.ρ (hV i) s)) → S U s) :
    Sheaf (Sub S stab) := by
  intro U ι V hV hU hVo hcov s hs
  obtain ⟨g, hg, hu⟩ := hP U ι V hV hU hVo hcov (fun i => (s i).1)
    (fun i j W hi hj hW => congrArg Subtype.val (hs i j W hi hj hW))
  have hgS : S U g := loc U ι V hV hU hVo hcov g fun i => by rw [hg i]; exact (s i).2
  refine ⟨⟨g, hgS⟩, fun i => Subtype.ext (hg i), fun g' hg' => Subtype.ext ?_⟩
  exact hu g'.1 fun i => congrArg Subtype.val (hg' i)

variable {H : Presheaf X}

/-- A16: the equalizer of two morphisms is restriction stable. -/
theorem equalizer_stable (φ ψ : Hom P H) {U V : Finset (Fin k)} (h : V ⊆ U) (s : P.F U)
    (hs : φ.α U s = ψ.α U s) : φ.α V (P.ρ h s) = ψ.α V (P.ρ h s) := by
  rw [φ.nat, ψ.nat, hs]

/-- A16: the equalizer of two morphisms into a sheaf is local. -/
theorem equalizer_local (hH : Sheaf H) (φ ψ : Hom P H) (U : Finset (Fin k)) (ι : Type)
    (V : ι → Finset (Fin k)) (hV : ∀ i, V i ⊆ U) (hU : X.IsOpen U) (hVo : ∀ i, X.IsOpen (V i))
    (hcov : ∀ x ∈ U, ∃ i, x ∈ V i) (s : P.F U)
    (h : ∀ i, φ.α (V i) (P.ρ (hV i) s) = ψ.α (V i) (P.ρ (hV i) s)) : φ.α U s = ψ.α U s := by
  have hm : Match H V fun i => H.ρ (hV i) (φ.α U s) := by
    intro i j W hi hj _
    rw [H.ρ_comp, H.ρ_comp]
  obtain ⟨_, _, hu⟩ := hH U ι V hV hU hVo hcov _ hm
  have e₁ := hu (φ.α U s) fun i => rfl
  have e₂ := hu (ψ.α U s) fun i => by rw [← ψ.nat, ← h i, φ.nat]
  rw [e₁, e₂]

/-- A16: the equalizer of two morphisms into a sheaf is a subsheaf. -/
theorem equalizer_sheaf (hP : Sheaf P) (hH : Sheaf H) (φ ψ : Hom P H) :
    Sheaf (Sub (fun U s => φ.α U s = ψ.α U s) fun h s hs => equalizer_stable φ ψ h s hs) :=
  sub_sheaf hP _ _ fun U ι V hV hU hVo hcov s h => equalizer_local hH φ ψ U ι V hV hU hVo hcov s h

end LeanProofs.IPRA.Topology.FiniteSheafTheory
