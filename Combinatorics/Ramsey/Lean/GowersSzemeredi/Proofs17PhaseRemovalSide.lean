import GowersSzemeredi.Proofs17PhaseRemoval

/-! Declarations of `Proofs17PhaseRemoval` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

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
  rw [prop172PhasedFamily, norm_mul, cor57_norm_exponential, mul_one]
  exact hf s

private lemma prop172_constantCubeForm_norm {N k : Nat} [NeZero N]
    (g : ZMod N → Complex) :
    ‖cubeForm (d := k + 1) (fun (_ : Fin (k + 1) → Bool) => g)‖ =
      ∑ x : Point N k, ‖∑ s : ZMod N, cubeDifference g x s‖ ^ 2 := by
  rw [constant_cubeForm_eq_sum_cubeDifference, sum_cube_succ_eq_sum_norm_sq]
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
      _ = (E : Complex) := (prop172_energy_expansion f sigma).symm
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

/-- Fourier energy as a sum of differences, available to localized phase removal. -/
theorem fourier_norm_sq_eq_difference_sum {N : Nat} [NeZero N]
    (g : ZMod N → Complex) (r : ZMod N) :
    ((‖fourier g r‖ ^ 2 : Real) : Complex) =
      ∑ y : ZMod N, ∑ s : ZMod N,
        difference g y s * exponential (-(y * r)) := by
  exact prop172_fourier_sq g r

/-- Multiplication by a fresh first coordinate preserves multilinearity. -/
theorem isMultilinear_mul_first_coordinate {N k : Nat}
    (sigma : Point N k → ZMod N) (hsigma : IsMultilinear sigma) :
    IsMultilinear (fun z : Point N (k + 1) => z 0 * sigma (Fin.tail z)) := by
  exact prop172_multilinear_cons sigma hsigma

end LeanProofs.GowersSzemeredi
