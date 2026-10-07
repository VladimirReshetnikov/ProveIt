import Mathlib.NumberTheory.Padics.PadicVal.Basic
import OAI.Combinatorics.Progressions.Lattices.CRTPrescribedProductStep
import OAI.Combinatorics.Progressions.Lattices.CRTValuationProduct

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

local instance divisorCRTModulusNeZero (p A : L → ℕ) [∀ l, NeZero (p l)] :
    NeZero (∏ l, p l ^ A l) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩

theorem crtPolynomialInputLaw_product_step_uniform
    (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l)) :
    crtPolynomialInputLaw p A e hq origin =
      (FiniteProbabilityWeights.uniform (V → ZMod (∏ l, p l ^ A l))).fiberLaw
        (fun x v => crtInput (fun l => p l ^ A l) hq origin v + (∏ l, p l ^ e l : ℕ) * x v) := by
  let E := crtInputAddEquiv (V := V) (fun l => p l ^ A l) hq
  let T := prescribedCRTProductStepEquiv (V := V) p A e hp hinj
  let f : (V → ZMod (∏ l, p l ^ A l)) → (V → ZMod (∏ l, p l ^ A l)) :=
    fun x v => crtInput (fun l => p l ^ A l) hq origin v + (∏ l, p l ^ e l : ℕ) * x v
  have hT := uniform_fiberLaw_surjective_hom T.toAddMonoidHom T.surjective
  change (FiniteProbabilityWeights.uniform (∀ l, V → ZMod (p l ^ A l))).fiberLaw T = _ at hT
  have hE := uniform_fiberLaw_surjective_hom E.toAddMonoidHom E.surjective
  change (FiniteProbabilityWeights.uniform (∀ l, V → ZMod (p l ^ A l))).fiberLaw E = _ at hE
  have heq : prescribedCRTPolynomialInput p A e hq origin ∘ T = f ∘ E := by
    funext x v
    exact prescribedCRTPolynomialInput_product_step p A e hp hinj hq origin x v
  rw [crtPolynomialInputLaw, crtPrimePowerPolynomialLaw_eq_uniform]
  calc
    _ = ((FiniteProbabilityWeights.uniform (∀ l, V → ZMod (p l ^ A l))).fiberLaw T).fiberLaw
        (prescribedCRTPolynomialInput p A e hq origin) := by rw [hT]
    _ = (FiniteProbabilityWeights.uniform (∀ l, V → ZMod (p l ^ A l))).fiberLaw (f ∘ E) := by
      rw [FiniteProbabilityWeights.fiberLaw_comp, heq]
    _ = _ := by rw [← FiniteProbabilityWeights.fiberLaw_comp, hE]

theorem crtPolynomialInputLaw_divisor_affine
    (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l))
    {q : ℕ} [NeZero q] (hdiv : q ∣ ∏ l, p l ^ A l) :
    (crtPolynomialInputLaw p A e hq origin).fiberLaw (tupleResidueReduction hdiv) =
      (FiniteProbabilityWeights.uniform (V → ZMod q)).fiberLaw
        (fun x v => tupleResidueReduction hdiv (crtInput (fun l => p l ^ A l) hq origin) v +
          (∏ l, p l ^ e l : ℕ) * x v) := by
  rw [crtPolynomialInputLaw_product_step_uniform p A e hp hinj hq origin]
  exact uniform_affine_tupleResidueReduction_fiberLaw hdiv _ _

theorem crtPolynomialInputLaw_divisor_complexMean
    (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l))
    {q : ℕ} [NeZero q] (hdiv : q ∣ ∏ l, p l ^ A l)
    (f : (V → ZMod q) → ℂ) :
    (crtPolynomialInputLaw p A e hq origin).complexMean
        (fun x => f (tupleResidueReduction hdiv x)) =
      (FiniteProbabilityWeights.uniform (V → ZMod q)).complexMean
        (fun x => f (fun v => tupleResidueReduction hdiv
          (crtInput (fun l => p l ^ A l) hq origin) v + (∏ l, p l ^ e l : ℕ) * x v)) := by
  rw [← FiniteProbabilityWeights.fiberLaw_complexMean,
    crtPolynomialInputLaw_divisor_affine p A e hp hinj hq origin,
    FiniteProbabilityWeights.fiberLaw_complexMean]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

 theorem tupleResidueReduction_integer_lift {V : Type*} {q N : ℕ} [NeZero N]
    (hdiv : q ∣ N) (x : V → ZMod N) (v : V) :
    tupleResidueReduction hdiv x v = (((x v).val : ℤ) : ZMod q) := by
  change ZMod.castHom hdiv (ZMod q) (x v) = _
  have hx : (((x v).val : ℤ) : ZMod N) = x v := by simp
  calc
    _ = ZMod.castHom hdiv (ZMod q) (((x v).val : ℤ) : ZMod N) := congrArg _ hx.symm
    _ = _ := map_intCast _ _

variable {L V : Type*} [Fintype L] [Fintype V]
local instance integerOriginCRTModulusNeZero (p A : L → ℕ) [∀ l, NeZero (p l)] :
    NeZero (∏ l, p l ^ A l) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩

theorem crtPolynomialInputLaw_divisor_integerOrigin_complexMean
    (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l))
    {q : ℕ} [NeZero q] (hdiv : q ∣ ∏ l, p l ^ A l)
    (f : (V → ZMod q) → ℂ) :
    let c : V → ℤ := fun v => (crtInput (fun l => p l ^ A l) hq origin v).val
    (crtPolynomialInputLaw p A e hq origin).complexMean
        (fun x => f (tupleResidueReduction hdiv x)) =
      (FiniteProbabilityWeights.uniform (V → ZMod q)).complexMean
        (fun x => f (fun v => (c v : ZMod q) + (∏ l, p l ^ e l : ℕ) * x v)) := by
  intro c
  simpa only [tupleResidueReduction_integer_lift] using
    crtPolynomialInputLaw_divisor_complexMean p A e hp hinj hq origin hdiv f

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem padicStepQuotient_coprime {p step : ℕ} (hp : p.Prime)
    (hstep : step ≠ 0) (A : ℕ) :
    (step / p ^ padicValNat p step).Coprime (p ^ A) := by
  let : Fact p.Prime := ⟨hp⟩
  apply Nat.Coprime.pow_right A
  apply Nat.Coprime.symm
  apply hp.coprime_iff_not_dvd.mpr
  intro h
  have hm := Nat.mul_dvd_mul_left (p ^ padicValNat p step) h
  rw [← pow_succ, Nat.mul_div_cancel' (pow_padicValNat_dvd (p := p) (n := step))] at hm
  exact pow_succ_padicValNat_not_dvd hstep hm

def padicStepQuotientUnit (p A step : ℕ) (hp : p.Prime) (hstep : step ≠ 0) :
    (ZMod (p ^ A))ˣ :=
  ZMod.unitOfCoprime (step / p ^ padicValNat p step)
    (padicStepQuotient_coprime hp hstep A)

@[simp] theorem padicStepQuotientUnit_coe (p A step : ℕ)
    (hp : p.Prime) (hstep : step ≠ 0) :
    (padicStepQuotientUnit p A step hp hstep : ZMod (p ^ A)) =
      (step / p ^ padicValNat p step : ℕ) := rfl

theorem padicStepQuotientUnit_factor (p A step : ℕ)
    (hp : p.Prime) (hstep : step ≠ 0) :
    (p : ZMod (p ^ A)) ^ padicValNat p step *
        padicStepQuotientUnit p A step hp hstep = (step : ZMod (p ^ A)) := by
  rw [padicStepQuotientUnit_coe, ← Nat.cast_pow, ← Nat.cast_mul,
    Nat.mul_div_cancel' (pow_padicValNat_dvd (p := p) (n := step))]

variable {L V : Type*} [Fintype L]

def prescribedCRTArbitraryStepEquiv (p A : L → ℕ) (step : ℕ)
    (hp : ∀ l, (p l).Prime) (hstep : step ≠ 0) :
    (∀ l, V → ZMod (p l ^ A l)) ≃+ (∀ l, V → ZMod (p l ^ A l)) where
  toFun x l v := padicStepQuotientUnit (p l) (A l) step (hp l) hstep * x l v
  invFun x l v := ↑(padicStepQuotientUnit (p l) (A l) step (hp l) hstep)⁻¹ * x l v
  left_inv x := by
    funext l v
    simp only [← mul_assoc, Units.inv_mul, one_mul]
  right_inv x := by
    funext l v
    simp only [← mul_assoc, Units.mul_inv, one_mul]
  map_add' x y := by
    funext l v
    exact mul_add _ _ _

omit [Fintype L] in
theorem prescribedCRTArbitraryStepEquiv_local_step (p A : L → ℕ) (step : ℕ)
    (hp : ∀ l, (p l).Prime) (hstep : step ≠ 0)
    (x : ∀ l, V → ZMod (p l ^ A l)) (l : L) (v : V) :
    (p l : ZMod (p l ^ A l)) ^ padicValNat (p l) step *
        prescribedCRTArbitraryStepEquiv p A step hp hstep x l v =
      (step : ZMod (p l ^ A l)) * x l v := by
  change (p l : ZMod (p l ^ A l)) ^ padicValNat (p l) step *
    ((padicStepQuotientUnit (p l) (A l) step (hp l) hstep : ZMod (p l ^ A l)) *
      x l v) = _
  rw [← mul_assoc, padicStepQuotientUnit_factor]

theorem prescribedCRTPolynomialInput_arbitrary_step (p A : L → ℕ) (step : ℕ)
    (hp : ∀ l, (p l).Prime) (hstep : step ≠ 0)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin x : ∀ l, V → ZMod (p l ^ A l)) (v : V) :
    prescribedCRTPolynomialInput p A (fun l => padicValNat (p l) step) hq origin
        (prescribedCRTArbitraryStepEquiv p A step hp hstep x) v =
      crtInput (fun l => p l ^ A l) hq origin v +
        (step : ℕ) * crtInput (fun l => p l ^ A l) hq x v := by
  apply (ZMod.prodEquivPi (fun l => p l ^ A l) hq).injective
  funext l
  rw [ZMod.prodEquivPi_apply, ZMod.prodEquivPi_apply]
  simp only [prescribedCRTPolynomialInput, map_add, map_mul, map_natCast]
  rw [crtInput_reduce (fun l => p l ^ A l) hq _ l v,
    crtInput_reduce (fun l => p l ^ A l) hq origin l v,
    crtInput_reduce (fun l => p l ^ A l) hq x l v]
  exact congrArg (origin l v + ·)
    (prescribedCRTArbitraryStepEquiv_local_step p A step hp hstep x l v)

local instance arbitraryStepCRTModulusNeZero (p A : L → ℕ) [∀ l, NeZero (p l)] :
    NeZero (∏ l, p l ^ A l) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩

variable [Fintype V]

theorem crtPolynomialInputLaw_arbitrary_step_uniform
    (p A : L → ℕ) [∀ l, NeZero (p l)] (step : ℕ)
    (hp : ∀ l, (p l).Prime) (hstep : step ≠ 0)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l)) :
    crtPolynomialInputLaw p A (fun l => padicValNat (p l) step) hq origin =
      (FiniteProbabilityWeights.uniform (V → ZMod (∏ l, p l ^ A l))).fiberLaw
        (fun x v => crtInput (fun l => p l ^ A l) hq origin v + (step : ℕ) * x v) := by
  let E := crtInputAddEquiv (V := V) (fun l => p l ^ A l) hq
  let T := prescribedCRTArbitraryStepEquiv (V := V) p A step hp hstep
  let f : (V → ZMod (∏ l, p l ^ A l)) → (V → ZMod (∏ l, p l ^ A l)) :=
    fun x v => crtInput (fun l => p l ^ A l) hq origin v + (step : ℕ) * x v
  have hT := uniform_fiberLaw_surjective_hom T.toAddMonoidHom T.surjective
  change (FiniteProbabilityWeights.uniform (∀ l, V → ZMod (p l ^ A l))).fiberLaw T = _ at hT
  have hE := uniform_fiberLaw_surjective_hom E.toAddMonoidHom E.surjective
  change (FiniteProbabilityWeights.uniform (∀ l, V → ZMod (p l ^ A l))).fiberLaw E = _ at hE
  have heq : prescribedCRTPolynomialInput p A (fun l => padicValNat (p l) step) hq origin ∘ T =
      f ∘ E := by
    funext x v
    exact prescribedCRTPolynomialInput_arbitrary_step p A step hp hstep hq origin x v
  rw [crtPolynomialInputLaw, crtPrimePowerPolynomialLaw_eq_uniform]
  calc
    _ = ((FiniteProbabilityWeights.uniform (∀ l, V → ZMod (p l ^ A l))).fiberLaw T).fiberLaw
        (prescribedCRTPolynomialInput p A (fun l => padicValNat (p l) step) hq origin) := by rw [hT]
    _ = (FiniteProbabilityWeights.uniform (∀ l, V → ZMod (p l ^ A l))).fiberLaw (f ∘ E) := by
      rw [FiniteProbabilityWeights.fiberLaw_comp, heq]
    _ = _ := by rw [← FiniteProbabilityWeights.fiberLaw_comp, hE]

omit [Fintype V] in
theorem crtInput_intCast_apply (q : L → ℕ)
    (hq : Pairwise (fun l k => (q l).Coprime (q k))) (c : V → ℤ) (v : V) :
    crtInput q hq (fun l v => (c v : ZMod (q l))) v =
      (c v : ZMod (∏ l, q l)) := by
  exact map_intCast (ZMod.prodEquivPi q hq).symm (c v)

theorem uniform_affine_valuationProduct_eq_step
    (p A : L → ℕ) [∀ l, NeZero (p l)] (step : ℕ)
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p) (hstep : step ≠ 0)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k))) (c : V → ℤ) :
    (FiniteProbabilityWeights.uniform (V → ZMod (∏ l, p l ^ A l))).fiberLaw
        (fun x v => (c v : ZMod (∏ l, p l ^ A l)) +
          (∏ l, p l ^ padicValNat (p l) step : ℕ) * x v) =
      (FiniteProbabilityWeights.uniform (V → ZMod (∏ l, p l ^ A l))).fiberLaw
        (fun x v => (c v : ZMod (∏ l, p l ^ A l)) + (step : ℕ) * x v) := by
  have hprod := crtPolynomialInputLaw_product_step_uniform p A
    (fun l => padicValNat (p l) step) hp hinj hq
    (fun l v => (c v : ZMod (p l ^ A l)))
  have hstride := crtPolynomialInputLaw_arbitrary_step_uniform p A step hp hstep hq
    (fun l v => (c v : ZMod (p l ^ A l)))
  simpa only [crtInput_intCast_apply] using hprod.symm.trans hstride

theorem crtPolynomialInputLaw_arbitrary_step_divisor_affine
    (p A : L → ℕ) [∀ l, NeZero (p l)] (step : ℕ)
    (hp : ∀ l, (p l).Prime) (hstep : step ≠ 0)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (c : V → ℤ) {q : ℕ} [NeZero q] (hdiv : q ∣ ∏ l, p l ^ A l) :
    (crtPolynomialInputLaw p A (fun l => padicValNat (p l) step) hq
      (fun l v => (c v : ZMod (p l ^ A l)))).fiberLaw (tupleResidueReduction hdiv) =
      (FiniteProbabilityWeights.uniform (V → ZMod q)).fiberLaw
        (fun x v => (c v : ZMod q) + (step : ZMod q) * x v) := by
  rw [crtPolynomialInputLaw_arbitrary_step_uniform p A step hp hstep hq,
    uniform_affine_tupleResidueReduction_fiberLaw hdiv]
  congr 1
  funext x v
  change ZMod.castHom hdiv (ZMod q)
    (crtInput (fun l => p l ^ A l) hq (fun l v => (c v : ZMod (p l ^ A l))) v) + _ = _
  rw [crtInput_intCast_apply, map_intCast]

theorem crtPolynomialInputLaw_arbitrary_step_divisor_complexMean
    (p A : L → ℕ) [∀ l, NeZero (p l)] (step : ℕ)
    (hp : ∀ l, (p l).Prime) (hstep : step ≠ 0)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (c : V → ℤ) {q : ℕ} [NeZero q] (hdiv : q ∣ ∏ l, p l ^ A l)
    (f : (V → ZMod q) → ℂ) :
    (crtPolynomialInputLaw p A (fun l => padicValNat (p l) step) hq
      (fun l v => (c v : ZMod (p l ^ A l)))).complexMean
        (fun x => f (tupleResidueReduction hdiv x)) =
      (FiniteProbabilityWeights.uniform (V → ZMod q)).complexMean
        (fun x => f (fun v => (c v : ZMod q) + (step : ZMod q) * x v)) := by
  rw [← FiniteProbabilityWeights.fiberLaw_complexMean,
    crtPolynomialInputLaw_arbitrary_step_divisor_affine p A step hp hstep hq c hdiv,
    FiniteProbabilityWeights.fiberLaw_complexMean]

end Erdos3

end

end OAI
