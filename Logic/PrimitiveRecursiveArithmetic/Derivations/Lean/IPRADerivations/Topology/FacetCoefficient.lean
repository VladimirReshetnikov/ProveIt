import IPRADerivations.Topology.ObstructionLabels
import Mathlib.GroupTheory.Perm.Sign

/-!
# The coefficient functional of the positive facet

Packet: `topology/hairy_ball_ipra`, `sections/degree.tex`, "Oriented chains": "Use integer formal sums of
oriented simplices. A tuple `[v_0, …, v_p]` changes sign under a transposition and denotes zero if two entries
coincide." The obstruction theorems of `Topology/AntipodalObstruction`, `Topology/ObstructionAlternating` and
`Topology/ObstructionLabels` take as a hypothesis a functional `φ` reading "the coefficient at the all-positive
face" of the cross-polytope. Here it is constructed, with the four properties those theorems use:

* `coefFn τ`: for a tuple `τ : ℕ → Vtx (n + 1)`, the sign of the permutation `m ↦ index of τ_m` if the first
  `n + 1` entries are positive vertices `+e_{π(0)}, …, +e_{π(n)}`, and `0` otherwise;
* `coefFn_congr`: it reads only the first `n + 1` entries;
* `coefFn_facet`: on a facet `[ε_0 e_0, …, ε_n e_n]` it is `1` for the positive facet and `0` otherwise;
* `coefFn_swap`: it changes sign under adjacent transpositions;
* `coefFn_repeat`: it vanishes on tuples with a repeated entry;
* `obstruction_of_cycle`: `ObstructionLabels.finite_obstruction_labels` with this functional: only the cycle
  (`hcyc`) and its carrier degree (`hdeg1`) remain as hypotheses.

Metatheory-level chain algebra, as in `Topology/PrismIdentity`.
-/

namespace LeanProofs.IPRA.Topology.FacetCoefficient

open Finset
open LeanProofs.IPRA.Topology.PrismIdentity (face prism)
open LeanProofs.IPRA.Topology.SphereCycle (Vtx facet coef anti)
open LeanProofs.IPRA.Topology.AntipodalObstruction (ext)
open LeanProofs.IPRA.Topology.DegenerateBoundary (swapAt)
open LeanProofs.IPRA.Topology.ObstructionLabels (finite_obstruction_labels)

variable {n : ℕ}

/-- The index map of the first `n + 1` entries. -/
def idx (τ : ℕ → Vtx (n + 1)) : Fin (n + 1) → Fin (n + 1) := fun m => (τ m.val).2

/-- The first `n + 1` entries are positive vertices. -/
def pos (τ : ℕ → Vtx (n + 1)) : Prop := ∀ m : Fin (n + 1), (τ m.val).1 = true

open Classical in
/-- The sign of a self-map of `Fin (n + 1)`: the sign of the permutation, or `0` if it is not bijective. -/
noncomputable def sgnMap (g : Fin (n + 1) → Fin (n + 1)) : ℤ :=
  if h : Function.Bijective g then ((Equiv.Perm.sign (Equiv.ofBijective g h) : ℤˣ) : ℤ) else 0

open Classical in
/-- The coefficient of the positive facet. -/
noncomputable def coefFn (τ : ℕ → Vtx (n + 1)) : ℤ := if pos τ then sgnMap (idx τ) else 0

theorem sgnMap_id : sgnMap (id : Fin (n + 1) → Fin (n + 1)) = 1 := by
  have e : Equiv.ofBijective (id : Fin (n + 1) → Fin (n + 1)) Function.bijective_id = 1 := by
    ext x
    rfl
  rw [sgnMap, dif_pos Function.bijective_id, e, Equiv.Perm.sign_one]
  rfl

theorem sgnMap_comp_swap (g : Fin (n + 1) → Fin (n + 1)) {a b : Fin (n + 1)} (hab : a ≠ b) :
    sgnMap (g ∘ Equiv.swap a b) = -sgnMap g := by
  by_cases hb : Function.Bijective g
  · have hbs : Function.Bijective (g ∘ Equiv.swap a b) := hb.comp (Equiv.swap a b).bijective
    have he : Equiv.ofBijective (g ∘ Equiv.swap a b) hbs = Equiv.ofBijective g hb * Equiv.swap a b := by
      ext x
      rfl
    rw [sgnMap, dif_pos hbs, sgnMap, dif_pos hb, he, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab]
    simp
  · have hnb : ¬ Function.Bijective (g ∘ Equiv.swap a b) := fun h => hb (by
      have e : g = (g ∘ Equiv.swap a b) ∘ Equiv.swap a b := by
        funext x
        simp [Function.comp_apply]
      rw [e]
      exact h.comp (Equiv.swap a b).bijective)
    rw [sgnMap, dif_neg hnb, sgnMap, dif_neg hb, _root_.neg_zero]

/-- The functional reads only the first `n + 1` entries. -/
theorem coefFn_congr (ρ τ : ℕ → Vtx (n + 1)) (h : ∀ m < n + 1, ρ m = τ m) : coefFn ρ = coefFn τ := by
  have hidx : idx ρ = idx τ := funext fun m => by simp only [idx, h m.val m.isLt]
  have hp : pos ρ ↔ pos τ := forall_congr' fun m => by rw [h m.val m.isLt]
  unfold coefFn
  rw [hidx]
  classical exact if_congr hp rfl rfl

theorem idx_ext_facet (ε : Fin (n + 1) → Bool) : idx (ext (facet ε)) = id := by
  funext m
  simp [idx, AntipodalObstruction.ext, facet, Nat.le_of_lt_succ m.isLt]

theorem pos_ext_facet (ε : Fin (n + 1) → Bool) : pos (ext (facet ε)) ↔ ε = fun _ => true := by
  constructor
  · intro h
    funext i
    have hi := h i
    simpa [AntipodalObstruction.ext, facet, Nat.le_of_lt_succ i.isLt] using hi
  · rintro rfl m
    simp [AntipodalObstruction.ext, facet, Nat.le_of_lt_succ m.isLt]

/-- On a facet the functional is the indicator of the positive facet. -/
theorem coefFn_facet (ε : Fin (n + 1) → Bool) :
    coefFn (ext (facet ε)) = if facet ε = facet (fun _ => true) then 1 else 0 := by
  by_cases hε : ε = fun _ => true
  · have hp : pos (ext (facet ε)) := (pos_ext_facet ε).mpr hε
    rw [if_pos (by rw [hε]), coefFn, if_pos hp, idx_ext_facet, sgnMap_id]
  · have hne : facet ε ≠ facet fun _ => true := fun h =>
      hε (funext fun i => congrArg Prod.fst (congrFun h i))
    have hp : ¬ pos (ext (facet ε)) := fun h => hε ((pos_ext_facet ε).mp h)
    rw [if_neg hne, coefFn, if_neg hp]

/-- The functional vanishes on tuples with a repeated entry. -/
theorem coefFn_repeat (τ : ℕ → Vtx (n + 1)) (j k : ℕ) (hjk : j < k) (hk : k < n + 1) (h : τ j = τ k) :
    coefFn τ = 0 := by
  have hnb : ¬ Function.Bijective (idx τ) := fun hb => by
    have e := hb.1 (show idx τ ⟨j, by omega⟩ = idx τ ⟨k, hk⟩ by simp only [idx, h])
    have e' : j = k := congrArg Fin.val e
    omega
  unfold coefFn
  split_ifs
  · rw [sgnMap, dif_neg hnb]
  · rfl

/-- The functional changes sign under an adjacent transposition. -/
theorem coefFn_swap (τ : ℕ → Vtx (n + 1)) (j : ℕ) (hj : j + 1 < n + 1) :
    coefFn (swapAt j τ) = -coefFn τ := by
  have hab : (⟨j, by omega⟩ : Fin (n + 1)) ≠ ⟨j + 1, hj⟩ := fun h => by
    have := congrArg Fin.val h
    simp at this
  have hsw : ∀ m : Fin (n + 1),
      swapAt j τ m.val = τ (Equiv.swap (⟨j, by omega⟩ : Fin (n + 1)) ⟨j + 1, hj⟩ m).val := by
    intro m
    by_cases h1 : m = ⟨j, by omega⟩
    · subst h1
      simp [swapAt]
    · by_cases h2 : m = ⟨j + 1, hj⟩
      · subst h2
        simp [swapAt]
      · have h1' : m.val ≠ j := fun h => h1 (Fin.ext h)
        have h2' : m.val ≠ j + 1 := fun h => h2 (Fin.ext h)
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
        simp only [swapAt]
        rw [if_neg h1', if_neg h2']
  have hidx : idx (swapAt j τ) = idx τ ∘ Equiv.swap (⟨j, by omega⟩ : Fin (n + 1)) ⟨j + 1, hj⟩ :=
    funext fun m => congrArg Prod.snd (hsw m)
  have hpos : pos (swapAt j τ) ↔ pos τ := by
    constructor
    · intro h m
      have hm := h (Equiv.swap (⟨j, by omega⟩ : Fin (n + 1)) ⟨j + 1, hj⟩ m)
      rw [hsw, Equiv.swap_apply_self] at hm
      exact hm
    · intro h m
      show (swapAt j τ m.val).1 = true
      rw [hsw m]
      exact h _
  unfold coefFn
  rw [hidx]
  by_cases hp : pos τ
  · rw [if_pos (hpos.mpr hp), if_pos hp, sgnMap_comp_swap _ hab]
  · rw [if_neg (fun h => hp (hpos.mp h)), if_neg hp, _root_.neg_zero]

/-- The finite obstruction with the constructed coefficient functional: for even `n`, a cycle of carrier
degree one and labellings from `ℓ_0` to `A ∘ ℓ_0` cannot avoid opposite pairs on every prism tuple. -/
theorem obstruction_of_cycle {V ι : Type*} (hn : Even n) (s : Finset ι) (c : ι → ℤ) (σ : ι → ℕ → V)
    (ℓ : ℕ → V → Vtx (n + 1)) (T : ℕ) (hT : ℓ T = anti ∘ ℓ 0)
    (hcyc : ∀ ψ : (ℕ → V) → ℤ, ∑ i ∈ s, c i • ∑ l ∈ range (n + 1), ((-1 : ℤ) ^ l) • ψ (face l (σ i)) = 0)
    (hdeg1 : ∀ χ : (ℕ → Vtx (n + 1)) → ℤ,
      (∀ ρ τ : ℕ → Vtx (n + 1), (∀ m < n + 1, ρ m = τ m) → χ ρ = χ τ) →
      ∑ i ∈ s, c i • χ (ℓ 0 ∘ σ i) = ∑ ε : Fin (n + 1) → Bool, coef ε • χ (ext (facet ε)))
    (hno : ∀ t < T, ∀ i ∈ s, ∀ m ∈ range (n + 1), ∀ p q, p < n + 2 → q < n + 2 →
      prism (ℓ t) (ℓ (t + 1)) m (σ i) p ≠ anti (prism (ℓ t) (ℓ (t + 1)) m (σ i) q)) : False :=
  finite_obstruction_labels hn s c σ ℓ T hT coefFn coefFn_congr coefFn_facet hcyc hdeg1
    coefFn_swap coefFn_repeat hno

end LeanProofs.IPRA.Topology.FacetCoefficient
