import GowersSzemeredi.Proofs03GowersCS
import GowersSzemeredi.Proofs17Phase
import Mathlib.Analysis.MeanInequalities

/-!
# Global polynomial phase removal

This module proves Proposition 17.2.  We apply Lemma 17.1 to the multiaffine
frequency `(y,x) ↦ y * sigma x`, identify the resulting phased cube form with
the original Fourier energy, and then use Lemma 3.8 and AM--GM to select one
of the polynomial phases.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

@[simp] private lemma prop172_exponential_add {N : Nat} [NeZero N]
    (x y : ZMod N) : exponential (x + y) = exponential x * exponential y := by
  exact AddChar.map_add_eq_mul (ZMod.stdAddChar (N := N)) x y

@[simp] private lemma prop172_star_exponential {N : Nat} [NeZero N]
    (x : ZMod N) : star (exponential x) = exponential (-x) := by
  simpa only [exponential, starRingEnd_apply] using
    (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := N)) x).symm

@[simp] private lemma prop172_norm_exponential {N : Nat} [NeZero N]
    (x : ZMod N) : ‖exponential x‖ = 1 := by
  exact (ZMod.stdAddChar (N := N)).norm_apply x

/-- Squaring a Fourier coefficient introduces one more difference variable. -/
private lemma prop172_fourier_sq {N : Nat} [NeZero N]
    (g : ZMod N → Complex) (r : ZMod N) :
    ((‖fourier g r‖ ^ 2 : Real) : Complex) =
      ∑ y : ZMod N, ∑ s : ZMod N,
        difference g y s * exponential (-(y * r)) := by
  simp only [fourier, ZMod.dft_apply, smul_eq_mul]
  calc
    ((‖∑ s : ZMod N, exponential (-(s * r)) * g s‖ ^ 2 : Real) : Complex) =
        (∑ s : ZMod N, exponential (-(s * r)) * g s) *
          star (∑ t : ZMod N, exponential (-(t * r)) * g t) := by
      rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow]
    _ = ∑ s : ZMod N, ∑ t : ZMod N,
        (exponential (-(s * r)) * g s) *
          (star (g t) * exponential (t * r)) := by
      simp only [star_sum, star_mul, prop172_star_exponential, neg_neg]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
    _ = ∑ s : ZMod N, ∑ y : ZMod N,
        (exponential (-(s * r)) * g s) *
          (star (g (s - y)) * exponential ((s - y) * r)) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← (Equiv.subLeft s).sum_comp]
      rfl
    _ = ∑ y : ZMod N, ∑ s : ZMod N,
        difference g y s * exponential (-(y * r)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro s _
      have hphase :
          exponential (-(s * r)) * exponential ((s - y) * r) =
            exponential (-(y * r)) := by
        rw [← prop172_exponential_add]
        congr 1
        ring
      rw [← hphase]
      unfold difference
      ring

private def prop172Monomial {N k : Nat} (e : Fin k → Bool) (x : Point N k) :
    ZMod N := ∏ i, if e i then x i else 1

private lemma prop172Monomial_cons {N k : Nat} (b : Bool) (e : Fin k → Bool)
    (z : Point N (k + 1)) :
    prop172Monomial (Fin.cons b e) z =
      (if b then z 0 else 1) * prop172Monomial e (Fin.tail z) := by
  simp [prop172Monomial, Fin.prod_univ_succ, Fin.tail]

/-- Multiplying a multiaffine function by a new first coordinate remains
multiaffine. -/
private lemma prop172_multilinear_cons {N k : Nat}
    (sigma : Point N k → ZMod N) (hsigma : IsMultilinear sigma) :
    IsMultilinear (fun z : Point N (k + 1) => z 0 * sigma (Fin.tail z)) := by
  classical
  obtain ⟨c, hc⟩ := hsigma
  let c' : (Fin (k + 1) → Bool) → ZMod N := fun e =>
    if e 0 then c (Fin.tail e) else 0
  refine ⟨c', fun z => ?_⟩
  let T : (Fin (k + 1) → Bool) → ZMod N := fun e =>
    c' e * prop172Monomial e z
  have htrue (e : Fin k → Bool) :
      T (Fin.cons true e) =
        z 0 * (c e * prop172Monomial e (Fin.tail z)) := by
    simp [T, c', prop172Monomial_cons]
    ring
  have hfalse (e : Fin k → Bool) : T (Fin.cons false e) = 0 := by
    simp [T, c']
  change z 0 * sigma (Fin.tail z) = ∑ e, T e
  calc
    z 0 * sigma (Fin.tail z) =
        z 0 * ∑ e : Fin k → Bool,
          c e * prop172Monomial e (Fin.tail z) := by
      rw [hc]
      rfl
    _ = ∑ e : Fin k → Bool, T (Fin.cons true e) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      rw [htrue]
    _ = ∑ e : Fin k → Bool, T (Fin.cons true e) +
        ∑ e : Fin k → Bool, T (Fin.cons false e) := by
      simp [hfalse]
    _ = ∑ p : Bool × (Fin k → Bool), T (Fin.cons p.1 p.2) := by
      rw [Fintype.sum_prod_type, Fintype.sum_bool]
    _ = ∑ e : Fin (k + 1) → Bool, T e := by
      exact (Fin.consEquiv (fun _ : Fin (k + 1) => Bool)).sum_comp T

private lemma prop172_countWhere_eq_sum_ite {X : Type*} [Fintype X]
    (P : X → Prop) :
    countWhere P = ∑ x : X,
      @ite Nat (P x) (Classical.propDecidable (P x)) 1 0 := by
  classical
  unfold countWhere
  simp

private lemma prop172_boolWeight_cons {n : Nat}
    (b : Bool) (e : Fin n → Bool) :
    boolWeight (Fin.cons b e) = (if b then 1 else 0) + boolWeight e := by
  classical
  unfold boolWeight
  simp_rw [prop172_countWhere_eq_sum_ite]
  rw [Fin.sum_univ_succ]
  cases b <;> simp
  all_goals
    convert (@Finset.sum_boole (Fin n) Nat inferInstance
      (fun i : Fin n => e i = true)
      (fun i => Classical.propDecidable (e i = true))
      (Finset.univ : Finset (Fin n))).symm using 1
    all_goals simp only [Nat.cast_id]
  all_goals congr

private lemma prop172_parityConj_cons_false {n : Nat}
    (e : Fin n → Bool) (z : Complex) :
    parityConj (Fin.cons false e) z = parityConj e z := by
  unfold parityConj
  rw [prop172_boolWeight_cons]
  simp

private lemma prop172_parityConj_cons_true {n : Nat}
    (e : Fin n → Bool) (z : Complex) :
    parityConj (Fin.cons true e) z = star (parityConj e z) := by
  unfold parityConj
  rw [prop172_boolWeight_cons]
  have heven : Even (1 + boolWeight e) ↔ ¬Even (boolWeight e) := by
    rw [add_comm, Nat.even_add_one]
  by_cases h : Even (boolWeight e) <;> simp [heven, h]

private lemma prop172_cubeArgument_cons {N n : Nat}
    (s r : ZMod N) (a : Point N n) (b : Bool) (e : Fin n → Bool) :
    cubeArgument s (Fin.cons r a) (Fin.cons b e) =
      s - (if b then r else 0) - ∑ i, if e i then a i else 0 := by
  unfold cubeArgument
  rw [Fin.sum_univ_succ]
  simp
  abel

/-- Closed cube-product formula for an iterated difference. -/
private lemma prop172_cubeDifference_product {N d : Nat}
    (f : ZMod N → Complex) (x : Point N d) (s : ZMod N) :
    cubeDifference f x s =
      ∏ e : Fin d → Bool, parityConj e (f (cubeArgument s x e)) := by
  induction d generalizing s with
  | zero =>
      simp [cubeDifference, iteratedDifference, parityConj, boolWeight,
        cubeArgument, countWhere]
  | succ n ih =>
      let r : ZMod N := x 0
      let a : Point N n := Fin.tail x
      have hx : x = Fin.cons r a := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      rw [hx, cubeDifference_cons]
      simp only [difference, ih]
      let T : (Fin (n + 1) → Bool) → Complex := fun e =>
        parityConj e (f (cubeArgument s (Fin.cons r a) e))
      calc
        (∏ e : Fin n → Bool,
              parityConj e (f (cubeArgument s a e))) *
            star (∏ e : Fin n → Bool,
              parityConj e (f (cubeArgument (s - r) a e))) =
            (∏ e : Fin n → Bool, T (Fin.cons false e)) *
              ∏ e : Fin n → Bool, T (Fin.cons true e) := by
          rw [star_prod]
          congr 1
          · apply Finset.prod_congr rfl
            intro e _
            simp only [T]
            rw [prop172_parityConj_cons_false, prop172_cubeArgument_cons]
            simp only [Bool.false_eq_true, if_false, sub_zero]
            rfl
          · apply Finset.prod_congr rfl
            intro e _
            simp only [T]
            rw [prop172_parityConj_cons_true, prop172_cubeArgument_cons]
            simp only [if_true]
            rfl
        _ = ∏ p : Bool × (Fin n → Bool), T (Fin.cons p.1 p.2) := by
          rw [Fintype.prod_prod_type, Fintype.prod_bool, mul_comm]
        _ = ∏ e : Fin (n + 1) → Bool, T e := by
          exact (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).prod_comp T

private def prop172PhasedFamily {N d : Nat} [NeZero N]
    (f : ZMod N → Complex)
    (phi : (Fin d → Bool) → ZMod N → ZMod N) :
    (Fin d → Bool) → ZMod N → Complex :=
  fun e s => f s * exponential (-(phi e s))

private lemma prop172_parity_phased {N d : Nat} [NeZero N]
    (f : ZMod N → Complex)
    (phi : (Fin d → Bool) → ZMod N → ZMod N)
    (e : Fin d → Bool) (z : ZMod N) :
    parityConj e (prop172PhasedFamily f phi e z) =
      parityConj e (f z) * exponential
        (-(if Even (boolWeight e) then phi e z else -phi e z)) := by
  by_cases h : Even (boolWeight e)
  · simp [prop172PhasedFamily, parityConj, h]
  · simp [prop172PhasedFamily, parityConj, h, star_mul]
    ring

private lemma prop172_exponential_sum {N : Nat} [NeZero N]
    {I : Type*} (S : Finset I) (a : I → ZMod N) :
    exponential (∑ i ∈ S, a i) = ∏ i ∈ S, exponential (a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
      simp [hx, ih]

private lemma prop172_phasedCubeProduct {N d : Nat} [NeZero N]
    (f : ZMod N → Complex)
    (phi : (Fin d → Bool) → ZMod N → ZMod N)
    (x : Point N d) (s : ZMod N) :
    (∏ e : Fin d → Bool,
        parityConj e
          (prop172PhasedFamily f phi e (cubeArgument s x e))) =
      cubeDifference f x s * exponential (-(signedCubeSum phi s x)) := by
  calc
    (∏ e : Fin d → Bool,
        parityConj e
          (prop172PhasedFamily f phi e (cubeArgument s x e))) =
        ∏ e : Fin d → Bool,
          (parityConj e (f (cubeArgument s x e)) *
            exponential
              (-(if Even (boolWeight e) then
                phi e (cubeArgument s x e)
              else -phi e (cubeArgument s x e)))) := by
      apply Finset.prod_congr rfl
      intro e _
      exact prop172_parity_phased f phi e (cubeArgument s x e)
    _ = (∏ e : Fin d → Bool,
          parityConj e (f (cubeArgument s x e))) *
        ∏ e : Fin d → Bool,
          exponential
            (-(if Even (boolWeight e) then phi e (cubeArgument s x e)
              else -phi e (cubeArgument s x e))) := by
      rw [Finset.prod_mul_distrib]
    _ = cubeDifference f x s *
        exponential
          (∑ e : Fin d → Bool,
            -(if Even (boolWeight e) then phi e (cubeArgument s x e)
              else -phi e (cubeArgument s x e))) := by
      rw [← prop172_cubeDifference_product]
      congr 1
      exact (prop172_exponential_sum Finset.univ _).symm
    _ = cubeDifference f x s * exponential (-(signedCubeSum phi s x)) := by
      congr 2
      unfold signedCubeSum
      rw [Finset.sum_neg_distrib]

private lemma prop172_cubeForm_phased {N d : Nat} [NeZero N]
    (f : ZMod N → Complex)
    (phi : (Fin d → Bool) → ZMod N → ZMod N)
    (tau : Point N d → ZMod N)
    (hphase : ∀ s x, tau x = signedCubeSum phi s x) :
    cubeForm (prop172PhasedFamily f phi) =
      ∑ x : Point N d, ∑ s : ZMod N,
        cubeDifference f x s * exponential (-(tau x)) := by
  unfold cubeForm
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro s _
  rw [prop172_phasedCubeProduct, hphase s x]

private lemma prop172_energy_expansion {N k : Nat} [NeZero N]
    (f : ZMod N → Complex) (sigma : Point N k → ZMod N) :
    ((∑ x : Point N k, ‖fourier (cubeDifference f x) (sigma x)‖ ^ 2 : Real) :
        Complex) =
      ∑ z : Point N (k + 1), ∑ s : ZMod N,
        cubeDifference f z s *
          exponential (-(z 0 * sigma (Fin.tail z))) := by
  calc
    ((∑ x : Point N k,
        ‖fourier (cubeDifference f x) (sigma x)‖ ^ 2 : Real) : Complex) =
        ∑ x : Point N k,
          ((‖fourier (cubeDifference f x) (sigma x)‖ ^ 2 : Real) :
            Complex) := by
      rw [Complex.ofReal_sum]
    _ = ∑ x : Point N k, ∑ y : ZMod N, ∑ s : ZMod N,
        difference (cubeDifference f x) y s *
          exponential (-(y * sigma x)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact prop172_fourier_sq (cubeDifference f x) (sigma x)
    _ = ∑ y : ZMod N, ∑ x : Point N k, ∑ s : ZMod N,
        cubeDifference f (Fin.cons y x : Point N (k + 1)) s *
          exponential (-((Fin.cons y x : Point N (k + 1)) 0 *
            sigma (Fin.tail (Fin.cons y x : Point N (k + 1))))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro s _
      rw [cubeDifference_cons]
      simp
    _ = ∑ z : Point N (k + 1), ∑ s : ZMod N,
        cubeDifference f z s *
          exponential (-(z 0 * sigma (Fin.tail z))) := by
      exact (sum_point_succ (N := N) (n := k) (M := Complex)
        (fun z => ∑ s : ZMod N, cubeDifference f z s *
          exponential (-(z 0 * sigma (Fin.tail z))))).symm

private lemma prop172_phased_discValued {N d : Nat} [NeZero N]
    (f : ZMod N → Complex) (hf : DiscValued f)
    (phi : (Fin d → Bool) → ZMod N → ZMod N) (e : Fin d → Bool) :
    DiscValued (prop172PhasedFamily f phi e) := by
  intro s
  rw [prop172PhasedFamily, norm_mul, prop172_norm_exponential, mul_one]
  exact hf s

private lemma prop172_constantCubeForm_norm {N k : Nat} [NeZero N]
    (g : ZMod N → Complex) :
    ‖cubeForm (d := k + 1) (fun (_ : Fin (k + 1) → Bool) => g)‖ =
      ∑ x : Point N k, ‖∑ s : ZMod N, cubeDifference g x s‖ ^ 2 := by
  have hform :
      cubeForm (d := k + 1) (fun (_ : Fin (k + 1) → Bool) => g) =
        ∑ z : Point N (k + 1), ∑ s : ZMod N, cubeDifference g z s := by
    unfold cubeForm
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro s _
    exact (prop172_cubeDifference_product g z s).symm
  rw [hform, sum_cube_succ_eq_sum_norm_sq]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Gowers, Proposition 17.2.** A global multiaffine frequency can be
removed by one polynomial phase. -/
theorem proposition_17_2_holds : proposition_17_2 := by
  intro N k _ _ f sigma alpha hkN hkfac hf hsigma henergy
  let tau : Point N (k + 1) → ZMod N := fun z =>
    z 0 * sigma (Fin.tail z)
  have htau : IsMultilinear tau := prop172_multilinear_cons sigma hsigma
  obtain ⟨Phi, hPhiPoly, hPhi⟩ :=
    lemma_17_1_holds N (k + 1) hkN hkfac tau htau
  let F : (Fin (k + 1) → Bool) → ZMod N → Complex :=
    prop172PhasedFamily f Phi
  let E : Real :=
    ∑ x : Point N k, ‖fourier (cubeDifference f x) (sigma x)‖ ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcube : cubeForm F = (E : Complex) := by
    calc
      cubeForm F = ∑ z : Point N (k + 1), ∑ s : ZMod N,
          cubeDifference f z s * exponential (-(tau z)) :=
        prop172_cubeForm_phased f Phi tau hPhi
      _ = (E : Complex) := by
        exact (prop172_energy_expansion f sigma).symm
  have hcubeNorm : ‖cubeForm F‖ = E := by
    rw [hcube, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE]
  have hFdisc : ∀ e, DiscValued (F e) := fun e =>
    prop172_phased_discValued f hf Phi e
  have hgcs := lemma_3_8_holds N (k + 1) F hFdisc
  let G : (Fin (k + 1) → Bool) → Real := fun e =>
    ‖cubeForm (d := k + 1)
      (fun (_ : Fin (k + 1) → Bool) => F e)‖
  let m : Nat := (2 : Nat) ^ (k + 1)
  let w : Real := (m : Real)⁻¹
  let T : Real := alpha * (N : Real) ^ (k + 2)
  have hm : m ≠ 0 := by positivity
  have hmpos : 0 < (m : Real) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hw : 0 < w := inv_pos.mpr hmpos
  have hG (e : Fin (k + 1) → Bool) : 0 ≤ G e := norm_nonneg _
  have hweight : ∑ _e : Fin (k + 1) → Bool, w = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul, m, w, Nat.cast_pow,
      Nat.cast_ofNat]
    apply mul_inv_cancel₀
    positivity
  have hgeom : T ≤ ∏ e : Fin (k + 1) → Bool, G e ^ w := by
    calc
      T ≤ E := henergy
      _ = ‖cubeForm F‖ := hcubeNorm.symm
      _ ≤ ∏ e : Fin (k + 1) → Bool,
          ‖cubeForm (d := k + 1)
            (fun (_ : Fin (k + 1) → Bool) => F e)‖ ^
              ((1 : Real) / (2 : Real) ^ (k + 1)) := hgcs
      _ = ∏ e : Fin (k + 1) → Bool, G e ^ w := by
        apply Finset.prod_congr rfl
        intro e _
        congr 2
        simp only [w, m, one_div, Nat.cast_pow, Nat.cast_ofNat]
  have hamgm : (∏ e : Fin (k + 1) → Bool, G e ^ w) ≤
      ∑ e : Fin (k + 1) → Bool, w * G e := by
    exact Real.geom_mean_le_arith_mean_weighted Finset.univ
      (fun _ => w) G (fun _ _ => hw.le) hweight (fun e _ => hG e)
  have havg : ∑ _e : Fin (k + 1) → Bool, w * T ≤
      ∑ e : Fin (k + 1) → Bool, w * G e := by
    calc
      (∑ _e : Fin (k + 1) → Bool, w * T) = T := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        rw [show (Fintype.card (Fin (k + 1) → Bool) : Real) = (m : Real) by
          simp [m]]
        rw [← mul_assoc, show (m : Real) * w = 1 by
          simp only [w, mul_inv_cancel₀ hmpos.ne'], one_mul]
      _ ≤ ∏ e : Fin (k + 1) → Bool, G e ^ w := hgeom
      _ ≤ ∑ e : Fin (k + 1) → Bool, w * G e := hamgm
  obtain ⟨e, _heMem, he⟩ := Finset.exists_le_of_sum_le
    (Finset.univ_nonempty :
      (Finset.univ : Finset (Fin (k + 1) → Bool)).Nonempty) havg
  have he' : T ≤ G e := le_of_mul_le_mul_left he hw
  refine ⟨Phi e, hPhiPoly e, ?_⟩
  calc
    alpha * (N : Real) ^ (k + 2) = T := rfl
    _ ≤ G e := he'
    _ = ∑ x : Point N k,
        ‖∑ s : ZMod N,
          cubeDifference (phaseTwist f (Phi e)) x s‖ ^ 2 := by
      have hterm :=
        prop172_constantCubeForm_norm (k := k) (prop172PhasedFamily f Phi e)
      rw [show prop172PhasedFamily f Phi e = phaseTwist f (Phi e) by rfl] at hterm
      exact hterm

end LeanProofs.GowersSzemeredi
