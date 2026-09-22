import Mathlib.Topology.Algebra.Field
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

/-!
# Difference-quotient derivatives over a topological field

`FineHasDerivAt` expresses the punctured-neighborhood limit in
`found:eq:derivative`. It requires no real-valued norm or Archimedean
hypothesis. The actual surreal and surcomplex topologies supply its intended
fine interpretation. Uniqueness requires a nontrivial punctured neighborhood;
it must not be inferred from limits over small, eventually constant nets.
-/

namespace Surreal

open Filter Topology

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]

/-- The difference quotient tends to `d` through all nonzero increments. -/
def FineHasDerivAt (f : K → K) (d a : K) : Prop :=
  Tendsto (fun h => (f (a + h) - f a) / h) (𝓝[≠] 0) (𝓝 d)

namespace FineHasDerivAt

variable {f g : K → K} {d e a : K}

omit [IsTopologicalDivisionRing K] in
/-- A genuine punctured neighborhood and Hausdorff separation give uniqueness. -/
theorem unique [T2Space K] [NeBot (𝓝[≠] (0 : K))]
    (hf : FineHasDerivAt f d a) (hg : FineHasDerivAt f e a) : d = e :=
  tendsto_nhds_unique hf hg

/-- A derivative is determined by the function on a neighborhood of its point. -/
theorem congr_of_eventuallyEq (hf : FineHasDerivAt f d a) (hfg : f =ᶠ[𝓝 a] g) :
    FineHasDerivAt g d a := by
  have h0 : f a = g a := hfg.self_of_nhds
  have ht : Tendsto (fun h : K => a + h) (𝓝[≠] 0) (𝓝 a) := by
    simpa using (tendsto_const_nhds.add (tendsto_id.mono_left nhdsWithin_le_nhds) :
      Tendsto (fun h : K => a + h) (𝓝[≠] 0) (𝓝 (a + 0)))
  apply hf.congr'
  filter_upwards [ht.eventually hfg] with h hh
  simp only [hh, h0]

omit [IsTopologicalDivisionRing K] in
theorem const (c a : K) : FineHasDerivAt (fun _ => c) 0 a := by
  simpa only [FineHasDerivAt, sub_self, zero_div] using
    (tendsto_const_nhds : Tendsto (fun _ : K => (0 : K)) (𝓝[≠] 0) (𝓝 0))

omit [IsTopologicalDivisionRing K] in
theorem id (a : K) : FineHasDerivAt (fun x => x) 1 a := by
  apply (tendsto_const_nhds : Tendsto (fun _ : K => (1 : K)) (𝓝[≠] 0) (𝓝 1)).congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hne : h ≠ 0 := by simpa using hh
  simp [hne]

theorem add (hf : FineHasDerivAt f d a) (hg : FineHasDerivAt g e a) :
    FineHasDerivAt (fun x => f x + g x) (d + e) a := by
  apply (Filter.Tendsto.add hf hg).congr'
  exact Filter.Eventually.of_forall fun h => by dsimp; ring

theorem neg (hf : FineHasDerivAt f d a) :
    FineHasDerivAt (fun x => -f x) (-d) a := by
  apply (Filter.Tendsto.neg hf).congr'
  exact Filter.Eventually.of_forall fun h => by dsimp; ring

theorem sub (hf : FineHasDerivAt f d a) (hg : FineHasDerivAt g e a) :
    FineHasDerivAt (fun x => f x - g x) (d - e) a := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- Differentiability forces continuity even though no norm is available. -/
theorem continuousAt (hf : FineHasDerivAt f d a) : ContinuousAt f a := by
  have hid : Tendsto (fun h : K => h) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hdiff : Tendsto (fun h => f (a + h) - f a) (𝓝[≠] 0) (𝓝 0) := by
    have ht := hf.mul hid
    simp only [mul_zero] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hne : h ≠ 0 := by simpa using hh
    exact div_mul_cancel₀ _ hne
  have hshift : ContinuousAt (fun h => f (a + h)) 0 := by
    apply continuousAt_iff_punctured_nhds.mpr
    simpa only [sub_add_cancel, add_zero, zero_add] using hdiff.add_const (f a)
  have hs : ContinuousAt (fun x : K => x - a) a :=
    continuous_id.continuousAt.sub continuous_const.continuousAt
  have hh : ContinuousAt (fun h => f (a + h)) (a - a) := by simpa using hshift
  simpa only [Function.comp_def, add_sub_cancel] using hh.comp (f := fun x : K => x - a) hs

theorem mul (hf : FineHasDerivAt f d a) (hg : FineHasDerivAt g e a) :
    FineHasDerivAt (fun x => f x * g x) (d * g a + f a * e) a := by
  have ht : Tendsto (fun h : K => a + h) (𝓝[≠] 0) (𝓝 a) := by
    simpa using (tendsto_const_nhds.add (tendsto_id.mono_left nhdsWithin_le_nhds) :
      Tendsto (fun h : K => a + h) (𝓝[≠] 0) (𝓝 (a + 0)))
  have hgcont := hg.continuousAt.tendsto.comp ht
  apply (Filter.Tendsto.add (Filter.Tendsto.mul hf hgcont)
    (Filter.Tendsto.mul tendsto_const_nhds hg)).congr'
  exact Filter.Eventually.of_forall fun h => by dsimp; ring

theorem pow (hf : FineHasDerivAt f d a) (n : ℕ) :
    FineHasDerivAt (fun x => f x ^ n) ((n : K) * f a ^ (n - 1) * d) a := by
  induction n with
  | zero => simpa using const (1 : K) a
  | succ n ih =>
    have ht := ih.mul hf
    convert ht using 1
    · ext x; exact pow_succ (f x) n
    · cases n with
      | zero => simp
      | succ n => push_cast; simp only [pow_succ]; ring


/-- The fine derivative of a polynomial is its native formal derivative. -/
theorem polynomial (p : Polynomial K) (a : K) :
    FineHasDerivAt (fun x => p.eval x) (p.derivative.eval a) a := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [Polynomial.eval_add, Polynomial.derivative_add] using hp.add hq
  | monomial n c =>
    simpa only [Polynomial.eval_monomial, Polynomial.derivative_monomial,
      zero_mul, zero_add, mul_one, mul_assoc] using (const c a).mul ((id a).pow n)

end FineHasDerivAt

end Surreal
