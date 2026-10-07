import OAI.Combinatorics.Progressions.Estimates.NormalizedTwistCellSelection

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]
  {X R : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
  [∀ j, DecidableEq (R j)]

theorem pi_fiber_set (F : ∀ j, X j → R j) (r : ∀ j, R j) :
    (Finset.univ.filter (fun x => (fun j => F j (x j)) = r)) =
      piRestrictionSet (fun j => Finset.univ.filter (fun x => F j x = r j)) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_piRestrictionSet, funext_iff]

theorem pi_fiber_mass (p : ∀ j, FiniteProbabilityWeights (X j))
    (F : ∀ j, X j → R j) (r : ∀ j, R j) :
    (pi p).mass (Finset.univ.filter (fun x => (fun j => F j (x j)) = r)) =
      ∏ j, (p j).mass (Finset.univ.filter (fun x => F j x = r j)) := by
  rw [pi_fiber_set, piRestriction_mass]

theorem pi_fiber_mass_pos (p : ∀ j, FiniteProbabilityWeights (X j))
    (F : ∀ j, X j → R j) (r : ∀ j, R j)
    (hr : ∀ j, 0 < (p j).mass (Finset.univ.filter (fun x => F j x = r j))) :
    0 < (pi p).mass (Finset.univ.filter (fun x => (fun j => F j (x j)) = r)) := by
  rw [pi_fiber_mass]
  exact Finset.prod_pos (fun j _ => hr j)

theorem pi_condition_fiber (p : ∀ j, FiniteProbabilityWeights (X j))
    (F : ∀ j, X j → R j) (r : ∀ j, R j)
    (hr : ∀ j, 0 < (p j).mass (Finset.univ.filter (fun x => F j x = r j))) :
    (pi p).condition (Finset.univ.filter (fun x => (fun j => F j (x j)) = r))
        (pi_fiber_mass_pos p F r hr) =
      pi (fun j => (p j).condition (Finset.univ.filter (fun x => F j x = r j)) (hr j)) := by
  simpa only [← pi_fiber_set F r] using
    (pi_condition p (fun j => Finset.univ.filter (fun x => F j x = r j)) hr).symm

variable [∀ j, Fintype (R j)]

theorem pi_retained_cell_mixture (p : ∀ j, FiniteProbabilityWeights (X j))
    (F : ∀ j, X j → R j) (S : ∀ j, Finset (R j))
    (hS : ∀ j r, r ∈ S j → 0 < (p j).mass (Finset.univ.filter (fun x => F j x = r)))
    (f : (∀ j, X j) → ℂ) :
    (∑ r : piRestrictionSet S,
      ((∏ j, (p j).mass (Finset.univ.filter (fun x => F j x = r.val j)) : ℝ) : ℂ) *
        (pi (fun j => (p j).condition (Finset.univ.filter (fun x => F j x = r.val j))
          (hS j (r.val j) ((mem_piRestrictionSet S r.val).mp r.property j)))).complexMean f) =
      (pi p).complexMean (fun x => if ∀ j, F j (x j) ∈ S j then f x else 0) := by
  have hpos : ∀ r ∈ piRestrictionSet S,
      0 < (pi p).mass (Finset.univ.filter (fun x => (fun j => F j (x j)) = r)) := by
    intro r hr
    exact pi_fiber_mass_pos p F r (fun j => hS j (r j) ((mem_piRestrictionSet S r).mp hr j))
  calc
    _ = ∑ r : piRestrictionSet S,
        ((pi p).mass (Finset.univ.filter (fun x => (fun j => F j (x j)) = r.val)) : ℂ) *
          ((pi p).condition (Finset.univ.filter (fun x => (fun j => F j (x j)) = r.val))
            (hpos r.val r.property)).complexMean f := by
      apply Finset.sum_congr rfl
      intro r _
      rw [pi_fiber_mass]
      have hc := pi_condition_fiber p F r.val
        (fun j => hS j (r.val j) ((mem_piRestrictionSet S r.val).mp r.property j))
      rw [hc]
    _ = (pi p).complexMean
        (fun x => if (fun j => F j (x j)) ∈ piRestrictionSet S then f x else 0) :=
      (pi p).sum_condition_complexMean_on (fun x j => F j (x j)) (piRestrictionSet S) hpos f
    _ = _ := by simp only [mem_piRestrictionSet]

theorem pi_retained_cell_mixture_error (p : ∀ j, FiniteProbabilityWeights (X j))
    (F : ∀ j, X j → R j) (S : ∀ j, Finset (R j))
    (hS : ∀ j r, r ∈ S j → 0 < (p j).mass (Finset.univ.filter (fun x => F j x = r)))
    (f : (∀ j, X j) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖(pi p).complexMean f - ∑ r : piRestrictionSet S,
      ((∏ j, (p j).mass (Finset.univ.filter (fun x => F j x = r.val j)) : ℝ) : ℂ) *
        (pi (fun j => (p j).condition (Finset.univ.filter (fun x => F j x = r.val j))
          (hS j (r.val j) ((mem_piRestrictionSet S r.val).mp r.property j)))).complexMean f‖ ≤
      ∑ j, (p j).mass (Finset.univ.filter (fun x => F j x ∉ S j)) := by
  classical
  rw [pi_retained_cell_mixture]
  have h := pi_remove_bad_event_error p (fun j => Finset.univ.filter (fun x => F j x ∉ S j)) f hf
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, ← not_forall, ite_not] using h

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem embedded_pi_cell_mixture {n : ℕ} {X R : Fin n → Type*}
    [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    [∀ j, Fintype (R j)] [∀ j, DecidableEq (R j)]
    (w : ∀ j, X j → ℝ) (hw : ∀ j x, 0 ≤ w j x) (htotal : ∀ j, 0 < ∑ x, w j x)
    (F : ∀ j, X j → R j) (S : ∀ j, Finset (R j))
    (Y : ∀ j, R j → Type*) [∀ j r, Fintype (Y j r)]
    (e : ∀ j r, Y j r ↪ X j)
    (hcell : ∀ j r, finiteEmbeddingRange (e j r) = Finset.univ.filter (fun x => F j x = r))
    (hchild : ∀ j r, r ∈ S j → 0 < ∑ y, w j (e j r y)) (f : (∀ j, X j) → ℂ) :
    let p := fun j => ofPositiveWeights (w j) (hw j) (htotal j)
    (∑ r : piRestrictionSet S,
      ((∏ j, (p j).mass (Finset.univ.filter (fun x => F j x = r.val j)) : ℝ) : ℂ) *
        (pi (fun j => ofPositiveWeights (fun y => w j (e j (r.val j) y))
          (fun y => hw j (e j (r.val j) y))
          (hchild j (r.val j) ((mem_piRestrictionSet S r.val).mp r.property j)))).complexMean
            (fun y => f (fun j => e j (r.val j) (y j)))) =
      (pi p).complexMean (fun x => if ∀ j, F j (x j) ∈ S j then f x else 0) := by
  let p := fun j => ofPositiveWeights (w j) (hw j) (htotal j)
  have hS : ∀ j r, r ∈ S j → 0 < (p j).mass (Finset.univ.filter (fun x => F j x = r)) := by
    intro j r hr
    change 0 < (ofPositiveWeights (w j) (hw j) (htotal j)).mass _
    rw [← hcell j r, ofPositiveWeights_mass, sum_finiteEmbeddingRange]
    exact div_pos (hchild j r hr) (htotal j)
  convert (pi_retained_cell_mixture p F S hS f) using 1
  swap
  · apply congrArg (pi p).complexMean
    funext x
    split_ifs <;> rfl
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  symm
  apply complexMean_pi_transport
    (fun j => (p j).condition (Finset.univ.filter (fun x => F j x = r.val j))
      (hS j (r.val j) ((mem_piRestrictionSet S r.val).mp r.property j)))
    (fun j => ofPositiveWeights (fun y => w j (e j (r.val j) y))
      (fun y => hw j (e j (r.val j) y))
      (hchild j (r.val j) ((mem_piRestrictionSet S r.val).mp r.property j)))
    (fun _ x => x) (fun j y => e j (r.val j) y) _ f
  intro j test
  have hG : 0 < (ofPositiveWeights (w j) (hw j) (htotal j)).mass
      (finiteEmbeddingRange (e j (r.val j))) := by
    rw [hcell]
    exact hS j (r.val j) ((mem_piRestrictionSet S r.val).mp r.property j)
  have h := ofPositiveWeights_condition_embedding_complexMean (w j) (hw j) (htotal j)
    (e j (r.val j)) (hchild j (r.val j) ((mem_piRestrictionSet S r.val).mp r.property j)) hG test
  simpa only [hcell, p] using h

theorem embedded_pi_cell_mixture_error {n : ℕ} {X R : Fin n → Type*}
    [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    [∀ j, Fintype (R j)] [∀ j, DecidableEq (R j)]
    (w : ∀ j, X j → ℝ) (hw : ∀ j x, 0 ≤ w j x) (htotal : ∀ j, 0 < ∑ x, w j x)
    (F : ∀ j, X j → R j) (S : ∀ j, Finset (R j))
    (Y : ∀ j, R j → Type*) [∀ j r, Fintype (Y j r)]
    (e : ∀ j r, Y j r ↪ X j)
    (hcell : ∀ j r, finiteEmbeddingRange (e j r) = Finset.univ.filter (fun x => F j x = r))
    (hchild : ∀ j r, r ∈ S j → 0 < ∑ y, w j (e j r y))
    (f : (∀ j, X j) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    let p := fun j => ofPositiveWeights (w j) (hw j) (htotal j)
    ‖(pi p).complexMean f - ∑ r : piRestrictionSet S,
      ((∏ j, (p j).mass (Finset.univ.filter (fun x => F j x = r.val j)) : ℝ) : ℂ) *
        (pi (fun j => ofPositiveWeights (fun y => w j (e j (r.val j) y))
          (fun y => hw j (e j (r.val j) y))
          (hchild j (r.val j) ((mem_piRestrictionSet S r.val).mp r.property j)))).complexMean
            (fun y => f (fun j => e j (r.val j) (y j)))‖ ≤
      ∑ j, (p j).mass (Finset.univ.filter (fun x => F j x ∉ S j)) := by
  classical
  dsimp only
  rw [embedded_pi_cell_mixture w hw htotal F S Y e hcell hchild f]
  have h := pi_remove_bad_event_error (fun j => ofPositiveWeights (w j) (hw j) (htotal j))
    (fun j => Finset.univ.filter (fun x => F j x ∉ S j)) f hf
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, ← not_forall, ite_not] using h

end Erdos3.FiniteProbabilityWeights

end

end OAI
