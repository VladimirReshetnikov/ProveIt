import Surreal.Surcomplex.FineTopology
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# No nonconstant fine-continuous paths

The small-subset discreteness theorem makes any fine-continuous map
with permitted-small range constant on every preconnected subset of
its domain. In particular this proves `found:cor:nopaths` and
`a:cor:nopath` for ordinary real intervals. The domain retains its own
topology, so this statement does not identify ordinary contours with
fine-continuous surcomplex paths.
-/

universe u v

namespace Surreal.Surcomplex

open Set

/-- Fine-continuous maps with small range are constant on preconnected subsets. -/
theorem eq_of_isPreconnected_of_small_range {X : Type v} [TopologicalSpace X]
    {s : Set X} (hs : IsPreconnected s) {f : X → Surcomplex.{u}}
    [Small.{u} (range f)] (hf : ContinuousOn f s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    f x = f y :=
  hs.constant_of_mapsTo (isDiscrete_of_small (range f)) hf
    (fun a _ => mem_range_self a) hx hy

/-- The same conclusion for a permitted-small parameter type. -/
theorem eq_of_isPreconnected {X : Type v} [TopologicalSpace X] [Small.{u} X]
    {s : Set X} (hs : IsPreconnected s) {f : X → Surcomplex.{u}}
    (hf : ContinuousOn f s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) : f x = f y :=
  eq_of_isPreconnected_of_small_range hs hf hx hy

/-- A continuous map from a small preconnected space is constant. -/
theorem eq_of_continuous {X : Type v} [TopologicalSpace X] [PreconnectedSpace X]
    [Small.{u} X] {f : X → Surcomplex.{u}} (hf : Continuous f) (x y : X) : f x = f y :=
  eq_of_isPreconnected isPreconnected_univ hf.continuousOn (mem_univ x) (mem_univ y)

/-- Ordinary interval paths cannot be nonconstant in the actual fine topology. -/
theorem eq_of_continuousOn_Icc {a b : ℝ} {f : ℝ → Surcomplex.{u}}
    (hf : ContinuousOn f (Icc a b)) {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    f x = f y :=
  eq_of_isPreconnected isPreconnected_Icc hf hx hy

end Surreal.Surcomplex
