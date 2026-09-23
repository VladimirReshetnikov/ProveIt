import Surreal.Algebra.FineDerivative

/-!
# Chain and reciprocal rules for fine derivatives

The difference quotient completed by its derivative at zero is continuous.
This gives the chain rule even when the inner increment vanishes, and avoids
assuming that a composed punctured neighborhood stays punctured. Inversion
uses its explicit nonzero-value hypothesis. No norm or Archimedean property
is used.
This supplies the chain and quotient calculus underlying `trigonometry:prop:lift`.
-/

namespace Surreal

open Filter Topology
open scoped Classical

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]

noncomputable section

/-- Complete the difference quotient by its proposed derivative at zero. -/
def fineSlope (f : K → K) (d a h : K) : K :=
  if h = 0 then d else (f (a + h) - f a) / h

omit [TopologicalSpace K] [IsTopologicalDivisionRing K] in
@[simp] theorem fineSlope_zero (f : K → K) (d a : K) : fineSlope f d a 0 = d := by
  simp [fineSlope]

omit [TopologicalSpace K] [IsTopologicalDivisionRing K] in
/-- The completed slope recovers the exact increment, including at zero. -/
theorem mul_fineSlope (f : K → K) (d a h : K) :
    h * fineSlope f d a h = f (a + h) - f a := by
  by_cases hh : h = 0
  · simp [hh]
  · simp only [fineSlope, if_neg hh]
    exact mul_div_cancel₀ _ hh

namespace FineHasDerivAt

variable {f g : K → K} {d e a : K}

omit [IsTopologicalDivisionRing K] in
/-- A fine derivative makes the completed slope continuous at zero. -/
theorem continuousAt_fineSlope (hf : FineHasDerivAt f d a) :
    ContinuousAt (fineSlope f d a) 0 := by
  rw [continuousAt_iff_punctured_nhds, fineSlope_zero]
  apply hf.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hne : h ≠ 0 := by simpa using hh
  simp only [fineSlope, if_neg hne]

/-- The chain rule includes inner functions locally attaining their center. -/
theorem comp (hg : FineHasDerivAt g e (f a)) (hf : FineHasDerivAt f d a) :
    FineHasDerivAt (g ∘ f) (e * d) a := by
  have harg : ContinuousAt (fun h : K => a + h) 0 :=
    continuous_const.continuousAt.add continuous_id.continuousAt
  have hinner : ContinuousAt (fun h : K => f (a + h) - f a) 0 := by
    have hc : ContinuousAt f (a + 0) := by simpa only [add_zero] using hf.continuousAt
    exact (hc.comp harg).sub continuous_const.continuousAt
  have houter : ContinuousAt (fineSlope g e (f a)) (f (a + 0) - f a) := by
    simpa only [add_zero, sub_self] using hg.continuousAt_fineSlope
  have ht := (houter.comp (f := fun h : K => f (a + h) - f a) hinner).mul
    hf.continuousAt_fineSlope
  have ht' : Tendsto (fun h => fineSlope g e (f a) (f (a + h) - f a) * fineSlope f d a h)
      (𝓝[≠] 0) (𝓝 (e * d)) := by
    simpa only [Function.comp_def, Pi.mul_def, add_zero, sub_self, fineSlope_zero] using
      ht.tendsto.mono_left (show 𝓝[≠] (0 : K) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  apply ht'.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hne : h ≠ 0 := by simpa using hh
  have hfinc := mul_fineSlope f d a h
  have hginc := mul_fineSlope g e (f a) (f (a + h) - f a)
  simp only [add_sub_cancel] at hginc
  dsimp only [Function.comp_apply]
  apply (eq_div_iff hne).mpr
  calc
    (fineSlope g e (f a) (f (a + h) - f a) * fineSlope f d a h) * h =
        (h * fineSlope f d a h) * fineSlope g e (f a) (f (a + h) - f a) := by ring
    _ = g (f (a + h)) - g (f a) := by rw [hfinc, hginc]

/-- The reciprocal rule retains the indispensable nonzero-value hypothesis. -/
theorem inv [T1Space K] (hf : FineHasDerivAt f d a) (ha : f a ≠ 0) :
    FineHasDerivAt (fun x => (f x)⁻¹) (-d / (f a) ^ 2) a := by
  have ht : Tendsto (fun h : K => a + h) (𝓝[≠] 0) (𝓝 a) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun h : K => a + h) (𝓝[≠] 0) (𝓝 (a + 0)))
  have hc := hf.continuousAt.tendsto.comp ht
  have hd := Filter.Tendsto.div (Filter.Tendsto.neg hf)
    (hc.mul_const (f a)) (mul_ne_zero ha ha)
  rw [← pow_two] at hd
  apply hd.congr'
  filter_upwards [hc.eventually_ne ha, self_mem_nhdsWithin] with h hh hne
  have hh' : f (a + h) ≠ 0 := hh
  have hne' : h ≠ 0 := by simpa using hne
  dsimp only [Function.comp_apply, Pi.div_apply, Pi.neg_apply]
  field_simp [ha, hh', hne']
  ring

/-- The quotient rule follows without assuming a real-valued norm. -/
theorem div [T1Space K] (hf : FineHasDerivAt f d a) (hg : FineHasDerivAt g e a)
    (ha : g a ≠ 0) :
    FineHasDerivAt (fun x => f x / g x) ((d * g a - f a * e) / (g a) ^ 2) a := by
  have ht := hf.mul (hg.inv ha)
  convert ht using 1
  · ext x; exact div_eq_mul_inv _ _
  · field_simp
    ring

/-- A continuous local right inverse has reciprocal derivative when the original derivative
is nonzero. The completed slope avoids any assumption about punctured maps. -/
theorem of_local_rightInverse [T1Space K] (hf : FineHasDerivAt f d (g a)) (hd : d ≠ 0)
    (hg : ContinuousAt g a) (hfg : ∀ᶠ x in 𝓝 a, f (g x) = x) :
    FineHasDerivAt g d⁻¹ a := by
  have ha := hfg.self_of_nhds
  have harg : ContinuousAt (fun h : K => a + h) 0 :=
    continuous_const.continuousAt.add continuous_id.continuousAt
  have hg' : ContinuousAt g (a + 0) := by simpa only [add_zero] using hg
  have hinner : ContinuousAt (fun h : K => g (a + h) - g a) 0 :=
    (hg'.comp harg).sub continuous_const.continuousAt
  have hs : ContinuousAt (fineSlope f d (g a)) (g (a + 0) - g a) := by
    simpa only [add_zero, sub_self] using hf.continuousAt_fineSlope
  have ht : Tendsto (fun h => (fineSlope f d (g a) (g (a + h) - g a))⁻¹)
      (𝓝[≠] 0) (𝓝 d⁻¹) := by
    have hc := (hs.comp (f := fun h : K => g (a + h) - g a) hinner).tendsto
    simp only [Function.comp_def, add_zero, sub_self, fineSlope_zero] at hc
    exact (hc.inv₀ hd).mono_left nhdsWithin_le_nhds
  have hshift : Tendsto (fun h : K => a + h) (𝓝[≠] 0) (𝓝 a) := by
    simpa only [add_zero] using harg.tendsto.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [hshift.eventually hfg, self_mem_nhdsWithin] with h hh hne
  have hn : h ≠ 0 := by simpa using hne
  have he := mul_fineSlope f d (g a) (g (a + h) - g a)
  rw [add_sub_cancel, hh, ha, add_sub_cancel_left] at he
  have hsne : fineSlope f d (g a) (g (a + h) - g a) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at he
    exact hn he.symm
  apply (eq_div_iff hn).mpr
  conv_lhs => rhs; rw [← he]
  field_simp

end FineHasDerivAt

end

end Surreal
