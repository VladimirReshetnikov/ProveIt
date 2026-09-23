import Surreal.Surcomplex.AnalyticComposition
import Surreal.Surcomplex.AnalyticFineDerivativeAll
import Surreal.Foundations.SignSequenceAnalyticSign

/-!
# The recentered analytic lift as a function on its natural domain

For `trigonometry:prop:lift`, the domain consists of finite actual inputs
whose ordinary standard parts admit the given analytic germ. The Taylor rule
determines the values uniquely on that domain. The domain contains a full
infinitesimal monad around each of its points, where the lift agrees with the
fixed-center Taylor function. Hence its fine derivative is the recentered
lift of the ordinary derivative, with every positive surreal tolerance.
-/

universe u

open Filter Topology

namespace Surreal.Foundations.SignSequence

noncomputable section

open scoped Classical

/-- The recentered analytic lift, with zero extension outside its finite analytic domain. -/
def analyticLiftFunction (f : ℝ → ℝ) (z : SignSequence.{u}) : SignSequence.{u} :=
  if h : IsFinite z ∧ AnalyticAt ℝ f (standardPart z) then
    analyticLift f z h.1 h.2 else 0

/-- The total function has the prescribed value on its actual analytic domain. -/
theorem analyticLiftFunction_of_domain (f : ℝ → ℝ) (z : SignSequence.{u})
    (hz : IsFinite z) (hf : AnalyticAt ℝ f (standardPart z)) :
    analyticLiftFunction f z = analyticLift f z hz hf := by
  have h : IsFinite z ∧ AnalyticAt ℝ f (standardPart z) := ⟨hz, hf⟩
  rw [analyticLiftFunction, dif_pos h]

/-- On its natural domain the recentered function is exactly the prescribed Taylor strong sum. -/
theorem analyticLiftFunction_eq_strongSum (f : ℝ → ℝ) (z : SignSequence.{u})
    (hz : IsFinite z) (hf : AnalyticAt ℝ f (standardPart z)) :
    analyticLiftFunction f z =
      strongSum (fun n => ofReal (iteratedDeriv n f (standardPart z) / n.factorial) *
        (z - ofReal (standardPart z)) ^ n)
        (stronglySummable_analyticTaylor f _ _ (infinitesimal_sub_standardPart hz)) := by
  rw [analyticLiftFunction_of_domain f z hz hf, analyticLift_eq_strongSum]

/-- The extension agrees with the original value at every analytic ordinary input. -/
theorem analyticLiftFunction_ofReal (f : ℝ → ℝ) (c : ℝ)
    (hf : AnalyticAt ℝ f c) :
    analyticLiftFunction f (ofReal c : SignSequence.{u}) = ofReal (f c) := by
  rw [analyticLiftFunction_of_domain f _ (finite_ofReal c)
    (by simpa only [standardPart_ofReal] using hf)]
  exact analyticLift_ofReal f c hf

/-- Sums are preserved wherever both ordinary germs are analytic. -/
theorem analyticLiftFunction_add (f g : ℝ → ℝ) (z : SignSequence.{u}) (hz : IsFinite z)
    (hf : AnalyticAt ℝ f (standardPart z)) (hg : AnalyticAt ℝ g (standardPart z)) :
    analyticLiftFunction (f + g) z = analyticLiftFunction f z + analyticLiftFunction g z := by
  rw [analyticLiftFunction_of_domain (f + g) z hz (hf.add hg),
    analyticLiftFunction_of_domain f z hz hf, analyticLiftFunction_of_domain g z hz hg,
    analyticLift_add]

/-- Negation is preserved on the finite analytic domain. -/
theorem analyticLiftFunction_neg (f : ℝ → ℝ) (z : SignSequence.{u}) (hz : IsFinite z)
    (hf : AnalyticAt ℝ f (standardPart z)) :
    analyticLiftFunction (-f) z = -analyticLiftFunction f z := by
  rw [analyticLiftFunction_of_domain (-f) z hz hf.neg,
    analyticLiftFunction_of_domain f z hz hf]
  simp only [analyticLift, analyticTaylorEvaluation, Analytic.taylorSeries_neg, map_neg]

/-- Products are preserved on the common finite analytic domain. -/
theorem analyticLiftFunction_mul (f g : ℝ → ℝ) (z : SignSequence.{u}) (hz : IsFinite z)
    (hf : AnalyticAt ℝ f (standardPart z)) (hg : AnalyticAt ℝ g (standardPart z)) :
    analyticLiftFunction (f * g) z = analyticLiftFunction f z * analyticLiftFunction g z := by
  rw [analyticLiftFunction_of_domain (f * g) z hz (hf.mul hg),
    analyticLiftFunction_of_domain f z hz hf, analyticLiftFunction_of_domain g z hz hg,
    analyticLift_mul]

/-- Composition uses the ordinary image of the standard part as the outer center. -/
theorem analyticLiftFunction_comp (f g : ℝ → ℝ) (z : SignSequence.{u}) (hz : IsFinite z)
    (hf : AnalyticAt ℝ f (g (standardPart z))) (hg : AnalyticAt ℝ g (standardPart z)) :
    analyticLiftFunction (f ∘ g) z = analyticLiftFunction f (analyticLiftFunction g z) := by
  rw [analyticLiftFunction_of_domain (f ∘ g) z hz (hf.comp hg),
    analyticLiftFunction_of_domain g z hz hg,
    analyticLiftFunction_of_domain f _ (isFinite_analyticLift g z hz hg)
      (by simpa only [standardPart_analyticLift] using hf)]
  exact analyticLift_comp f g z hz hf hg

/-- Constant ordinary functions lift to their embedded constant on finite inputs. -/
theorem analyticLiftFunction_const (a : ℝ) (x : SignSequence.{u}) (hx : IsFinite x) :
    analyticLiftFunction (fun _ : ℝ => a) x = ofReal a := by
  rw [analyticLiftFunction_of_domain _ x hx analyticAt_const]
  simp only [analyticLift, analyticTaylorEvaluation, Analytic.taylorSeries_const,
    powerSeriesEvaluation_C]

/-- The identity ordinary function lifts to the identity on all finite actual inputs. -/
theorem analyticLiftFunction_id (x : SignSequence.{u}) (hx : IsFinite x) :
    analyticLiftFunction (id : ℝ → ℝ) x = x := by
  rw [analyticLiftFunction_of_domain _ x hx analyticAt_id]
  simp only [analyticLift, analyticTaylorEvaluation, Analytic.taylorSeries_id,
    map_add, powerSeriesEvaluation_C, powerSeriesEvaluation_X, add_sub_cancel]

/-- Differences are preserved on the common finite analytic domain. -/
theorem analyticLiftFunction_sub (f g : ℝ → ℝ) (x : SignSequence.{u}) (hx : IsFinite x)
    (hf : AnalyticAt ℝ f (standardPart x)) (hg : AnalyticAt ℝ g (standardPart x)) :
    analyticLiftFunction (f - g) x = analyticLiftFunction f x - analyticLiftFunction g x := by
  simpa only [sub_eq_add_neg, analyticLiftFunction_neg g x hx hg] using
    analyticLiftFunction_add f (-g) x hx hf hg.neg

/-- The Taylor strong-sum rule determines the extension uniquely on its natural domain. -/
theorem analyticLiftFunction_unique (f : ℝ → ℝ) (F : SignSequence.{u} → SignSequence.{u})
    (hF : ∀ (z : SignSequence.{u}) (hz : IsFinite z) (_hf : AnalyticAt ℝ f (standardPart z)),
      F z = strongSum (fun n => ofReal (iteratedDeriv n f (standardPart z) / n.factorial) *
        (z - ofReal (standardPart z)) ^ n)
        (stronglySummable_analyticTaylor f _ _ (infinitesimal_sub_standardPart hz))) :
    Set.EqOn F (analyticLiftFunction f)
      {z | IsFinite z ∧ AnalyticAt ℝ f (standardPart z)} := by
  intro z hz
  rw [analyticLiftFunction_of_domain f z hz.1 hz.2, analyticLift_eq_strongSum]
  exact hF z hz.1 hz.2

/-- Every point infinitesimally close to an analytic ordinary center uses that same germ. -/
theorem analyticLiftFunction_of_isInfinitesimal (f : ℝ → ℝ) (c : ℝ)
    (hf : AnalyticAt ℝ f c) (z : SignSequence.{u})
    (hz : IsInfinitesimal (z - ofReal c)) :
    analyticLiftFunction f z = analyticTaylorFunction f c z := by
  have hfinite : IsFinite z := by
    have h : IsFinite ((z - ofReal c) + ofReal c) :=
      finite_add (finite_of_infinitesimal hz) (finite_ofReal c)
    simpa only [sub_add_cancel] using h
  have hc : standardPart z = c := (infinitesimal_sub_ofReal_iff hfinite).mp hz
  have hfa : AnalyticAt ℝ f (standardPart z) := by rw [hc]; exact hf
  rw [analyticLiftFunction_of_domain f z hfinite hfa,
    ← analyticTaylorFunction_standardPart_eq_analyticLift, hc]

/-- The total recentered lift and its fixed-center representation agree near each valid point. -/
theorem analyticLiftFunction_eventuallyEq (f : ℝ → ℝ) (z : SignSequence.{u})
    (hz : IsFinite z) (hf : AnalyticAt ℝ f (standardPart z)) :
    analyticLiftFunction f =ᶠ[𝓝 z] analyticTaylorFunction f (standardPart z) := by
  have hn := (isClopen_monad (ofReal (standardPart z))).isOpen.mem_nhds
    (infinitesimal_sub_standardPart hz)
  filter_upwards [hn] with y hy
  exact analyticLiftFunction_of_isInfinitesimal f _ hf y hy

/-- Differentiation commutes with the recentered analytic lift at every valid finite input. -/
theorem fineHasDerivAt_analyticLiftFunction (f : ℝ → ℝ) (z : SignSequence.{u})
    (hz : IsFinite z) (hf : AnalyticAt ℝ f (standardPart z)) :
    FineHasDerivAt (analyticLiftFunction f) (analyticLiftFunction (deriv f) z) z := by
  rw [analyticLiftFunction_of_domain (deriv f) z hz hf.deriv]
  exact (fineHasDerivAt_analyticTaylorFunction_standardPart f z hz hf).congr_of_eventuallyEq
    (analyticLiftFunction_eventuallyEq f z hz hf).symm

/-- The recentered analytic lift is fine-continuous on its finite analytic domain. -/
theorem continuousAt_analyticLiftFunction (f : ℝ → ℝ) (z : SignSequence.{u})
    (hz : IsFinite z) (hf : AnalyticAt ℝ f (standardPart z)) :
    ContinuousAt (analyticLiftFunction f) z :=
  (fineHasDerivAt_analyticLiftFunction f z hz hf).continuousAt


/-- Ordinary analytic nonnegativity on a closed interval holds for this same canonical function. -/
theorem analyticLiftFunction_nonneg_of_mem_Icc (f : ℝ → ℝ) (a b : ℝ)
    (hf : AnalyticOnNhd ℝ f (Set.Icc a b)) (hpos : ∀ y ∈ Set.Icc a b, 0 ≤ f y)
    (x : SignSequence.{u}) (hx : x ∈ Set.Icc (ofReal a) (ofReal b)) :
    0 ≤ analyticLiftFunction f x := by
  rw [analyticLiftFunction_of_domain f x (isFinite_of_mem_real_Icc hx)
    (hf _ (standardPart_mem_real_Icc hx))]
  exact analyticLift_nonneg_of_mem_Icc f a b hf hpos x hx

end

end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex

noncomputable section

open scoped Classical

/-- The recentered analytic lift, with zero extension outside its finite analytic domain. -/
def analyticLiftFunction (f : ℂ → ℂ) (z : Surcomplex.{u}) : Surcomplex.{u} :=
  if h : IsFinite z ∧ AnalyticAt ℂ f (standardPart z) then
    analyticLift f z h.1 h.2 else 0

/-- The total function has the prescribed value on its actual analytic domain. -/
theorem analyticLiftFunction_of_domain (f : ℂ → ℂ) (z : Surcomplex.{u})
    (hz : IsFinite z) (hf : AnalyticAt ℂ f (standardPart z)) :
    analyticLiftFunction f z = analyticLift f z hz hf := by
  have h : IsFinite z ∧ AnalyticAt ℂ f (standardPart z) := ⟨hz, hf⟩
  rw [analyticLiftFunction, dif_pos h]

/-- On its natural domain the recentered function is exactly the prescribed Taylor strong sum. -/
theorem analyticLiftFunction_eq_strongSum (f : ℂ → ℂ) (z : Surcomplex.{u})
    (hz : IsFinite z) (hf : AnalyticAt ℂ f (standardPart z)) :
    analyticLiftFunction f z =
      strongSum (fun n => ofComplex (iteratedDeriv n f (standardPart z) / n.factorial) *
        (z - ofComplex (standardPart z)) ^ n)
        (stronglySummable_analyticTaylor f _ _ (infinitesimal_sub_standardPart hz)) := by
  rw [analyticLiftFunction_of_domain f z hz hf, analyticLift_eq_strongSum]

/-- The extension agrees with the original value at every analytic ordinary input. -/
theorem analyticLiftFunction_ofComplex (f : ℂ → ℂ) (c : ℂ)
    (hf : AnalyticAt ℂ f c) :
    analyticLiftFunction f (ofComplex c : Surcomplex.{u}) = ofComplex (f c) := by
  rw [analyticLiftFunction_of_domain f _ (finite_ofComplex c)
    (by simpa only [standardPart_ofComplex] using hf)]
  exact analyticLift_ofComplex f c hf

/-- Sums are preserved wherever both ordinary germs are analytic. -/
theorem analyticLiftFunction_add (f g : ℂ → ℂ) (z : Surcomplex.{u}) (hz : IsFinite z)
    (hf : AnalyticAt ℂ f (standardPart z)) (hg : AnalyticAt ℂ g (standardPart z)) :
    analyticLiftFunction (f + g) z = analyticLiftFunction f z + analyticLiftFunction g z := by
  rw [analyticLiftFunction_of_domain (f + g) z hz (hf.add hg),
    analyticLiftFunction_of_domain f z hz hf, analyticLiftFunction_of_domain g z hz hg,
    analyticLift_add]

/-- Negation is preserved on the finite analytic domain. -/
theorem analyticLiftFunction_neg (f : ℂ → ℂ) (z : Surcomplex.{u}) (hz : IsFinite z)
    (hf : AnalyticAt ℂ f (standardPart z)) :
    analyticLiftFunction (-f) z = -analyticLiftFunction f z := by
  rw [analyticLiftFunction_of_domain (-f) z hz hf.neg,
    analyticLiftFunction_of_domain f z hz hf]
  simp only [analyticLift, analyticTaylorEvaluation, Analytic.taylorSeries_neg, map_neg]

/-- Products are preserved on the common finite analytic domain. -/
theorem analyticLiftFunction_mul (f g : ℂ → ℂ) (z : Surcomplex.{u}) (hz : IsFinite z)
    (hf : AnalyticAt ℂ f (standardPart z)) (hg : AnalyticAt ℂ g (standardPart z)) :
    analyticLiftFunction (f * g) z = analyticLiftFunction f z * analyticLiftFunction g z := by
  rw [analyticLiftFunction_of_domain (f * g) z hz (hf.mul hg),
    analyticLiftFunction_of_domain f z hz hf, analyticLiftFunction_of_domain g z hz hg,
    analyticLift_mul]

/-- Composition uses the ordinary image of the standard part as the outer center. -/
theorem analyticLiftFunction_comp (f g : ℂ → ℂ) (z : Surcomplex.{u}) (hz : IsFinite z)
    (hf : AnalyticAt ℂ f (g (standardPart z))) (hg : AnalyticAt ℂ g (standardPart z)) :
    analyticLiftFunction (f ∘ g) z = analyticLiftFunction f (analyticLiftFunction g z) := by
  rw [analyticLiftFunction_of_domain (f ∘ g) z hz (hf.comp hg),
    analyticLiftFunction_of_domain g z hz hg,
    analyticLiftFunction_of_domain f _ (isFinite_analyticLift g z hz hg)
      (by simpa only [standardPart_analyticLift] using hf)]
  exact analyticLift_comp f g z hz hf hg

/-- Constant ordinary functions lift to their embedded constant on finite inputs. -/
theorem analyticLiftFunction_const (a : ℂ) (x : Surcomplex.{u}) (hx : IsFinite x) :
    analyticLiftFunction (fun _ : ℂ => a) x = ofComplex a := by
  rw [analyticLiftFunction_of_domain _ x hx analyticAt_const]
  simp only [analyticLift, analyticTaylorEvaluation, Analytic.taylorSeries_const,
    powerSeriesEvaluation_C]

/-- The identity ordinary function lifts to the identity on all finite actual inputs. -/
theorem analyticLiftFunction_id (x : Surcomplex.{u}) (hx : IsFinite x) :
    analyticLiftFunction (id : ℂ → ℂ) x = x := by
  rw [analyticLiftFunction_of_domain _ x hx analyticAt_id]
  simp only [analyticLift, analyticTaylorEvaluation, Analytic.taylorSeries_id,
    map_add, powerSeriesEvaluation_C, powerSeriesEvaluation_X, add_sub_cancel]

/-- Differences are preserved on the common finite analytic domain. -/
theorem analyticLiftFunction_sub (f g : ℂ → ℂ) (x : Surcomplex.{u}) (hx : IsFinite x)
    (hf : AnalyticAt ℂ f (standardPart x)) (hg : AnalyticAt ℂ g (standardPart x)) :
    analyticLiftFunction (f - g) x = analyticLiftFunction f x - analyticLiftFunction g x := by
  simpa only [sub_eq_add_neg, analyticLiftFunction_neg g x hx hg] using
    analyticLiftFunction_add f (-g) x hx hf hg.neg

/-- The Taylor strong-sum rule determines the extension uniquely on its natural domain. -/
theorem analyticLiftFunction_unique (f : ℂ → ℂ) (F : Surcomplex.{u} → Surcomplex.{u})
    (hF : ∀ (z : Surcomplex.{u}) (hz : IsFinite z) (_hf : AnalyticAt ℂ f (standardPart z)),
      F z = strongSum (fun n => ofComplex (iteratedDeriv n f (standardPart z) / n.factorial) *
        (z - ofComplex (standardPart z)) ^ n)
        (stronglySummable_analyticTaylor f _ _ (infinitesimal_sub_standardPart hz))) :
    Set.EqOn F (analyticLiftFunction f)
      {z | IsFinite z ∧ AnalyticAt ℂ f (standardPart z)} := by
  intro z hz
  rw [analyticLiftFunction_of_domain f z hz.1 hz.2, analyticLift_eq_strongSum]
  exact hF z hz.1 hz.2

/-- Every point infinitesimally close to an analytic ordinary center uses that same germ. -/
theorem analyticLiftFunction_of_isInfinitesimal (f : ℂ → ℂ) (c : ℂ)
    (hf : AnalyticAt ℂ f c) (z : Surcomplex.{u})
    (hz : IsInfinitesimal (z - ofComplex c)) :
    analyticLiftFunction f z = analyticTaylorFunction f c z := by
  have hfinite : IsFinite z := by
    have h : IsFinite ((z - ofComplex c) + ofComplex c) :=
      finiteSubring.add_mem (finite_of_infinitesimal hz) (finite_ofComplex c)
    simpa only [sub_add_cancel] using h
  have hc : standardPart z = c := (infinitesimal_sub_ofComplex_iff hfinite).mp hz
  have hfa : AnalyticAt ℂ f (standardPart z) := by rw [hc]; exact hf
  rw [analyticLiftFunction_of_domain f z hfinite hfa,
    ← analyticTaylorFunction_standardPart_eq_analyticLift, hc]

/-- The total recentered lift and its fixed-center representation agree near each valid point. -/
theorem analyticLiftFunction_eventuallyEq (f : ℂ → ℂ) (z : Surcomplex.{u})
    (hz : IsFinite z) (hf : AnalyticAt ℂ f (standardPart z)) :
    analyticLiftFunction f =ᶠ[𝓝 z] analyticTaylorFunction f (standardPart z) := by
  have hn := (isClopen_monad (ofComplex (standardPart z))).isOpen.mem_nhds
    (infinitesimal_sub_standardPart hz)
  filter_upwards [hn] with y hy
  exact analyticLiftFunction_of_isInfinitesimal f _ hf y hy

/-- Differentiation commutes with the recentered analytic lift at every valid finite input. -/
theorem fineHasDerivAt_analyticLiftFunction (f : ℂ → ℂ) (z : Surcomplex.{u})
    (hz : IsFinite z) (hf : AnalyticAt ℂ f (standardPart z)) :
    FineHasDerivAt (analyticLiftFunction f) (analyticLiftFunction (deriv f) z) z := by
  rw [analyticLiftFunction_of_domain (deriv f) z hz hf.deriv]
  exact (fineHasDerivAt_analyticTaylorFunction_standardPart f z hz hf).congr_of_eventuallyEq
    (analyticLiftFunction_eventuallyEq f z hz hf).symm

/-- The recentered analytic lift is fine-continuous on its finite analytic domain. -/
theorem continuousAt_analyticLiftFunction (f : ℂ → ℂ) (z : Surcomplex.{u})
    (hz : IsFinite z) (hf : AnalyticAt ℂ f (standardPart z)) :
    ContinuousAt (analyticLiftFunction f) z :=
  (fineHasDerivAt_analyticLiftFunction f z hz hf).continuousAt

end

end Surreal.Surcomplex
