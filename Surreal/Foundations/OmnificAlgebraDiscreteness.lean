import Surreal.Algebra.SeparatedSubrings
import Surreal.Foundations.OmnificAlgebraAbsorption
import Surreal.Foundations.OmnificFloor
import Surreal.Foundations.SignSequenceUniformity

/-!
# Closed and uniformly discrete omnific-generated algebras

The actual-surreal clause of `osq:nm:thm:discrete`. A generating set is
lower-universe-small; its generated algebra need not be. A single positive
monomial denominator separates all pairs in the entire algebra and yields
one entourage forcing equality. Closedness and discreteness concern the
native fine order topology, not an arithmetic congruence topology.
-/

universe u v
namespace Surreal.Foundations.SignSequence
noncomputable section
open Filter Topology Uniformity

/-- The reciprocal of a common positive monomial separates the entire generated algebra. -/
theorem omnific_adjoin_separation (s : Set SignSequence.{u}) [Small.{u} s] :
    ∃ h : SignSequence.{u}, 0 < h ∧
      ∀ x ∈ Algebra.adjoin OmnificInteger s, ∀ y ∈ Algebra.adjoin OmnificInteger s,
        x ≠ y → 1 / omegaPower h ≤ |x - y| := by
  obtain ⟨h, hh, hs⟩ := omnific_adjoin_monomial_clearing s
  refine ⟨h, hh, SeparatedSubrings.separation_of_absorption _
    existsUnique_omnific_integerPart (omegaPower h) (omegaPower_pos h) ?_⟩
  intro x hx
  obtain ⟨a, _, ha⟩ := hs x hx
  exact ⟨a, ha⟩

/-- The generated algebra is discrete in the ambient fine order topology. -/
theorem omnific_adjoin_isDiscrete (s : Set SignSequence.{u}) [Small.{u} s] :
    IsDiscrete (Algebra.adjoin OmnificInteger s : Set SignSequence.{u}) := by
  obtain ⟨h, _, hs⟩ := omnific_adjoin_separation s
  exact SeparatedSubrings.isDiscrete_of_separation _ (1 / omegaPower h)
    (div_pos zero_lt_one (omegaPower_pos h)) hs

/-- The generated algebra is a closed subset of the actual surreal field. -/
theorem omnific_adjoin_isClosed (s : Set SignSequence.{u}) [Small.{u} s] :
    IsClosed (Algebra.adjoin OmnificInteger s : Set SignSequence.{u}) := by
  obtain ⟨h, _, hs⟩ := omnific_adjoin_separation s
  exact SeparatedSubrings.isClosed_of_separation (Algebra.adjoin OmnificInteger s).toSubring
    (1 / omegaPower h) (div_pos zero_lt_one (omegaPower_pos h)) hs

/-- The induced topology on the algebra's native subtype is discrete. -/
theorem omnific_adjoin_discreteTopology (s : Set SignSequence.{u}) [Small.{u} s] :
    DiscreteTopology (Algebra.adjoin OmnificInteger s) :=
  isDiscrete_iff_discreteTopology.mp (omnific_adjoin_isDiscrete s)

/-- One native additive entourage forces equality throughout the algebra. -/
theorem omnific_adjoin_uniformly_discrete (s : Set SignSequence.{u}) [Small.{u} s] :
    ∃ U ∈ 𝓤 SignSequence.{u}, ∀ x ∈ Algebra.adjoin OmnificInteger s,
      ∀ y ∈ Algebra.adjoin OmnificInteger s, (x, y) ∈ U → x = y := by
  obtain ⟨h, _, hs⟩ := omnific_adjoin_separation s
  refine ⟨{p : SignSequence.{u} × SignSequence.{u} | |p.1 - p.2| < 1 / omegaPower h},
    abs_sub_entourage _ (div_pos zero_lt_one (omegaPower_pos h)), ?_⟩
  intro x hx y hy hxy
  by_contra hne
  exact (not_lt_of_ge (hs x hx y hy hne)) hxy

/-- A Cauchy net in this algebra is eventually equal to one of its values, with no index bound. -/
theorem omnific_adjoin_cauchy_eventually_constant (s : Set SignSequence.{u}) [Small.{u} s]
    {ι : Type v} (f : ι → SignSequence.{u})
    (hf : ∀ i, f i ∈ Algebra.adjoin OmnificInteger s) {l : Filter ι}
    (hc : Cauchy (Filter.map f l)) : ∃ i₀, ∀ᶠ i in l, f i = f i₀ := by
  haveI : NeBot l := (map_neBot_iff f).mp hc.1
  obtain ⟨U, hU, hUeq⟩ := omnific_adjoin_uniformly_discrete s
  obtain ⟨t, ht, hsmall⟩ := (cauchy_iff'.mp hc).2 U hU
  have hpre : f ⁻¹' t ∈ l := ht
  obtain ⟨i₀, hi₀⟩ := Filter.nonempty_of_mem hpre
  refine ⟨i₀, Filter.mem_of_superset hpre ?_⟩
  intro i hi
  exact hUeq (f i) (hf i) (f i₀) (hf i₀) (hsmall (f i) hi (f i₀) hi₀)

end
end Surreal.Foundations.SignSequence
