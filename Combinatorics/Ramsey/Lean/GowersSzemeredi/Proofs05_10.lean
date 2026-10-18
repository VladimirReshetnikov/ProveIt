import GowersSzemeredi.Section05
import GowersSzemeredi.Sections06_07
import GowersSzemeredi.Section10
import GowersSzemeredi.ProofInfrastructure
import GowersSzemeredi.Proofs01_03
import GowersSzemeredi.Proofs06PhiAdditiveFourier
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Proofs for Gowers (2001), Sections 5--10

This file supplies proofs of those formalized statements from Sections 5--10
that follow directly from general results already available in Mathlib or from
finite combinatorial identities.

`lemma_5_15_holds`, `lemma_6_2_holds` and `lemma_9_1_holds` are in
`Proofs05_10Side`, outside the final route. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod Combinatorics.Additive
open Finset

namespace LeanProofs.GowersSzemeredi

attribute [simp] exponential_add

attribute [simp] star_exponential

/-- Expansion and change of variables at the start of Proposition 6.1. -/
private lemma prop61_energy_expansion {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (B : Finset (ZMod N)) (phi : ZMod N → ZMod N) :
    (((∑ k ∈ B, ‖fourier (difference f k) (phi k)‖ ^ 2 : ℝ)) : Complex) =
      ∑ u : ZMod N, ∑ s : ZMod N,
        f s * star (f (s - u)) *
          ∑ k ∈ B, star (f (s - k)) * f (s - k - u) *
            exponential (-(phi k * u)) := by
  simp only [fourier, difference, ZMod.dft_apply, smul_eq_mul]
  calc
    (((∑ k ∈ B,
        ‖∑ s : ZMod N, exponential (-(s * phi k)) *
          (f s * star (f (s - k)))‖ ^ 2 : ℝ)) : Complex) =
        ∑ k ∈ B,
          (∑ s : ZMod N, exponential (-(s * phi k)) *
            (f s * star (f (s - k)))) *
          star (∑ t : ZMod N, exponential (-(t * phi k)) *
            (f t * star (f (t - k)))) := by
              rw [Complex.ofReal_sum]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow]
    _ = ∑ k ∈ B, ∑ s : ZMod N, ∑ t : ZMod N,
          (exponential (-(s * phi k)) * (f s * star (f (s - k)))) *
            ((f (t - k) * star (f t)) * exponential (t * phi k)) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              simp only [star_sum, star_mul, star_star, star_exponential, neg_neg]
              simp_rw [sum_mul, mul_sum]
    _ = ∑ s : ZMod N, ∑ t : ZMod N, ∑ k ∈ B,
          (exponential (-(s * phi k)) * (f s * star (f (s - k)))) *
            ((f (t - k) * star (f t)) * exponential (t * phi k)) := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun s _ => ?_
              rw [Finset.sum_comm]
    _ = ∑ s : ZMod N, ∑ u : ZMod N, ∑ k ∈ B,
          (exponential (-(s * phi k)) * (f s * star (f (s - k)))) *
            ((f (s - u - k) * star (f (s - u))) * exponential ((s - u) * phi k)) := by
              refine Finset.sum_congr rfl fun s _ => ?_
              rw [← (Equiv.subLeft s).sum_comp]
              rfl
    _ = ∑ u : ZMod N, ∑ s : ZMod N,
          f s * star (f (s - u)) *
            ∑ k ∈ B, star (f (s - k)) * f (s - k - u) *
              exponential (-(phi k * u)) := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun s _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun k _ => ?_
              have hphase :
                  exponential (-(s * phi k)) * exponential ((s - u) * phi k) =
                    exponential (-(phi k * u)) := by
                rw [← exponential_add]
                congr 1
                ring
              rw [← hphase]
              ring

private lemma prop61_initial_bound {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (B : Finset (ZMod N)) (phi : ZMod N → ZMod N)
    (hf : DiscValued f) :
    (∑ k ∈ B, ‖fourier (difference f k) (phi k)‖ ^ 2) ≤
      ∑ u : ZMod N, ∑ s : ZMod N,
        ‖∑ k ∈ B, star (f (s - k)) * f (s - k - u) *
          exponential (-(phi k * u))‖ := by
  let inner : ZMod N → ZMod N → Complex := fun u s =>
    ∑ k ∈ B, star (f (s - k)) * f (s - k - u) * exponential (-(phi k * u))
  have hnonneg : 0 ≤ ∑ k ∈ B, ‖fourier (difference f k) (phi k)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc
    (∑ k ∈ B, ‖fourier (difference f k) (phi k)‖ ^ 2) =
        ‖(((∑ k ∈ B, ‖fourier (difference f k) (phi k)‖ ^ 2 : ℝ)) : Complex)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hnonneg]
    _ = ‖∑ u : ZMod N, ∑ s : ZMod N,
          f s * star (f (s - u)) * inner u s‖ := by
            rw [prop61_energy_expansion f B phi]
    _ ≤ ∑ u : ZMod N, ‖∑ s : ZMod N,
          f s * star (f (s - u)) * inner u s‖ := norm_sum_le _ _
    _ ≤ ∑ u : ZMod N, ∑ s : ZMod N,
          ‖f s * star (f (s - u)) * inner u s‖ := by
            apply Finset.sum_le_sum
            intro u _
            exact norm_sum_le _ _
    _ ≤ ∑ u : ZMod N, ∑ s : ZMod N, ‖inner u s‖ := by
            gcongr with u _ s _
            rw [norm_mul, norm_mul, norm_star]
            have hs := hf s
            have hsu := hf (s - u)
            calc
              ‖f s‖ * ‖f (s - u)‖ * ‖inner u s‖ ≤ 1 * 1 * ‖inner u s‖ := by
                gcongr
              _ = ‖inner u s‖ := by ring

private lemma prop61_l1_cauchy {N : Nat} [NeZero N] (F : ZMod N → ZMod N → ℝ) :
    (∑ u : ZMod N, ∑ s : ZMod N, F u s) ^ 2 ≤
      (N : ℝ) ^ 2 * ∑ u : ZMod N, ∑ s : ZMod N, (F u s) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (ZMod N × ZMod N))) (f := fun q => F q.1 q.2)
  simp only [Finset.card_univ, Fintype.card_prod, ZMod.card, Fintype.sum_prod_type] at h
  calc _ ≤ _ := h
    _ = _ := by push_cast; ring

private def prop61F {N : Nat} (f : ZMod N → Complex) (u x : ZMod N) : Complex :=
  star (f (-x)) * f (-x - u)

private lemma prop61_correlation_eq {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (B : Finset (ZMod N)) (phi : ZMod N → ZMod N)
    (u s : ZMod N) :
    correlation (prop61F f u) (prop61G B phi u) (-s) =
      ∑ k ∈ B, star (f (s - k)) * f (s - k - u) *
        exponential (-(phi k * u)) := by
  simp only [correlation]
  rw [← (Equiv.subRight s).sum_comp]
  simp only [Equiv.subRight_apply, prop61F, prop61G, sub_neg_eq_add, sub_add_cancel,
    neg_sub, indicator, star_mul]
  simp [mul_assoc]

private lemma prop61_mixed_eq_l2 {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (B : Finset (ZMod N)) (phi : ZMod N → ZMod N) :
    (∑ u : ZMod N, ∑ r : ZMod N,
        ‖fourier (prop61F f u) r‖ ^ 2 * ‖fourier (prop61G B phi u) r‖ ^ 2) =
      (N : ℝ) * ∑ u : ZMod N, ∑ s : ZMod N,
        ‖∑ k ∈ B, star (f (s - k)) * f (s - k - u) *
          exponential (-(phi k * u))‖ ^ 2 := by
  calc
    _ = ∑ u : ZMod N, (N : ℝ) * ∑ t : ZMod N,
        ‖correlation (prop61F f u) (prop61G B phi u) t‖ ^ 2 := by
          refine Finset.sum_congr rfl fun u _ => ?_
          exact lemma_2_1_holds N (prop61F f u) (prop61G B phi u)
    _ = (N : ℝ) * ∑ u : ZMod N, ∑ s : ZMod N,
        ‖∑ k ∈ B, star (f (s - k)) * f (s - k - u) *
          exponential (-(phi k * u))‖ ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun u _ => ?_
          congr 1
          have hneg :
              (∑ t : ZMod N,
                ‖correlation (prop61F f u) (prop61G B phi u) t‖ ^ 2) =
              ∑ s : ZMod N,
                ‖correlation (prop61F f u) (prop61G B phi u) (-s)‖ ^ 2 := by
            symm
            exact Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ fun _ => rfl
          rw [hneg]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [prop61_correlation_eq]

private lemma prop61F_disc {N : Nat} (f : ZMod N → Complex) (hf : DiscValued f)
    (u : ZMod N) : DiscValued (prop61F f u) := by
  intro x
  rw [prop61F, norm_mul, norm_star]
  calc
    ‖f (-x)‖ * ‖f (-x - u)‖ ≤ 1 * 1 := by gcongr <;> apply hf
    _ = 1 := one_mul 1

private lemma prop61_global_cauchy {N : Nat} [NeZero N]
    (f : ZMod N → Complex) (B : Finset (ZMod N)) (phi : ZMod N → ZMod N) :
    (∑ u : ZMod N, ∑ r : ZMod N,
        ‖fourier (prop61F f u) r‖ ^ 2 * ‖fourier (prop61G B phi u) r‖ ^ 2) ^ 2 ≤
      (∑ u : ZMod N, ∑ r : ZMod N, ‖fourier (prop61F f u) r‖ ^ 4) *
        ∑ u : ZMod N, ∑ r : ZMod N, ‖fourier (prop61G B phi u) r‖ ^ 4 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq
    ((Finset.univ : Finset (ZMod N)) ×ˢ (Finset.univ : Finset (ZMod N)))
    (fun p => ‖fourier (prop61F f p.1) p.2‖ ^ 2)
    (fun p => ‖fourier (prop61G B phi p.1) p.2‖ ^ 2)
  simpa only [Finset.sum_product, ← pow_mul] using h

/-- Two residues falling in the same one-dimensional grid cell differ by a
Bohr-small residue. -/
private lemma lemma77_centeredAbs_sub_le {N m : Nat} [NeZero N]
    {delta : ℝ} (hdelta : 0 < delta) (hm : 0 < m)
    (hm_lower : delta⁻¹ ≤ (m : ℝ)) {x y : ZMod N}
    (hbin : x.val * m / N = y.val * m / N) :
    (centeredAbs (x - y) : ℝ) ≤ delta * N := by
  have hNnat : 0 < N := NeZero.pos N
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hdelta_m : 1 ≤ delta * (m : ℝ) := by
    rw [← mul_inv_cancel₀ hdelta.ne']
    gcongr
  have hNm : (N : ℝ) / m ≤ delta * N := (div_le_iff₀ hmreal).2 (by nlinarith)
  -- two residues of one grid cell `[q N / m, (q + 1) N / m)` differ by less than `N / m`
  have ordered {a b : ZMod N} (hba : b.val ≤ a.val)
      (habin : a.val * m / N = b.val * m / N) :
      (centeredAbs (a - b) : ℝ) < (N : ℝ) / m := by
    let q := a.val * m / N
    have hhi : a.val * m < N * (q + 1) := by
      simpa only [q] using Nat.lt_mul_div_succ (a.val * m) hNnat
    have hlo : q * N ≤ b.val * m := by
      rw [show q = b.val * m / N from habin]
      exact Nat.div_mul_le_self _ _
    have hhiR : (a.val : ℝ) * m < (N : ℝ) * ((q : ℝ) + 1) := by exact_mod_cast hhi
    have hloR : (q : ℝ) * N ≤ (b.val : ℝ) * m := by exact_mod_cast hlo
    have hdiffR : ((a.val - b.val : Nat) : ℝ) * m < (N : ℝ) := by
      rw [Nat.cast_sub hba]
      nlinarith
    have hcenterNat : centeredAbs (a - b) ≤ a.val - b.val := by
      unfold centeredAbs
      rw [ZMod.valMinAbs_natAbs_eq_min, ZMod.val_sub hba]
      exact Nat.min_le_left _ _
    exact (lt_div_iff₀ hmreal).2
      ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcenterNat) hmreal.le).trans_lt hdiffR)
  rcases le_total y.val x.val with hyx | hxy
  · exact (ordered hyx hbin).le.trans hNm
  · rw [show centeredAbs (x - y) = centeredAbs (y - x) by
      unfold centeredAbs
      rw [show x - y = -(y - x) by abel, ZMod.natAbs_valMinAbs_neg]]
    exact (ordered hxy hbin.symm).le.trans hNm

/-- Lemma 5.4 is Mathlib's Dirichlet approximation theorem, with the resulting
rational written in reduced numerator/denominator form. -/
theorem lemma_5_4_holds : lemma_5_4 := by
  intro alpha u hu
  obtain ⟨r, hr, hru⟩ := Real.exists_rat_abs_sub_le_and_den_le alpha (by omega : 0 < u)
  refine ⟨r.num, r.den, r.den_pos, hru, r.reduced, ?_⟩
  have hden : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hu_real : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
  calc
    |alpha - (r.num : ℝ) / (r.den : ℝ)| = |alpha - (r : ℝ)| := by
      congr 2
      exact (Rat.cast_def r).symm
    _ ≤ 1 / (((u : ℝ) + 1) * r.den) := by simpa using hr
    _ ≤ (((r.den : ℝ) * u))⁻¹ := by
      rw [inv_eq_one_div]
      refine one_div_le_one_div_of_le (mul_pos hden hu_real) ?_
      nlinarith

/-- Proposition 6.1 follows by two applications of Cauchy--Schwarz, the
Fourier correlation identity, and character orthogonality. -/
theorem proposition_6_1_holds : proposition_6_1 := by
  intro N _ alpha f B phi hAlpha hf hlarge
  let inner : ZMod N → ZMod N → Complex := fun u s =>
    ∑ k ∈ B, star (f (s - k)) * f (s - k - u) * exponential (-(phi k * u))
  let L1 : ℝ := ∑ u : ZMod N, ∑ s : ZMod N, ‖inner u s‖
  let L2 : ℝ := ∑ u : ZMod N, ∑ s : ZMod N, ‖inner u s‖ ^ 2
  let mixed : ℝ := ∑ u : ZMod N, ∑ r : ZMod N,
    ‖fourier (prop61F f u) r‖ ^ 2 * ‖fourier (prop61G B phi u) r‖ ^ 2
  let fourthF : ℝ := ∑ u : ZMod N, ∑ r : ZMod N,
    ‖fourier (prop61F f u) r‖ ^ 4
  let fourthG : ℝ := ∑ u : ZMod N, ∑ r : ZMod N,
    ‖fourier (prop61G B phi u) r‖ ^ 4
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  -- `α N³ ≤ L1`; Cauchy--Schwarz gives `L1² ≤ N² L2`, hence `α² N⁴ ≤ L2`
  have hL1 : alpha * (N : ℝ) ^ 3 ≤ L1 := hlarge.trans <| by
    simpa only [L1, inner] using prop61_initial_bound f B phi hf
  have hCauchy1 : L1 ^ 2 ≤ (N : ℝ) ^ 2 * L2 := by
    simpa only [L1, L2] using
      (prop61_l1_cauchy (N := N) (fun u s => ‖inner u s‖))
  have hL2 : alpha ^ 2 * (N : ℝ) ^ 4 ≤ L2 := le_of_mul_le_mul_left (by
    linarith [mul_self_le_mul_self (by positivity) hL1]) hN2
  -- `mixed = N L2 ≥ α² N⁵`; Cauchy--Schwarz gives `mixed² ≤ fourthF fourthG ≤ N⁵ fourthG`
  have hmixed_eq : mixed = (N : ℝ) * L2 := by
    simpa only [mixed, L2, inner] using prop61_mixed_eq_l2 f B phi
  have hmixed : alpha ^ 2 * (N : ℝ) ^ 5 ≤ mixed := by
    linarith [mul_le_mul_of_nonneg_left hL2 hN.le]
  have hfourthF : fourthF ≤ (N : ℝ) ^ 5 := by
    calc fourthF ≤ ∑ _u : ZMod N, (N : ℝ) ^ 4 := Finset.sum_le_sum fun u _ =>
          fourier_fourth_moment_le (prop61F f u) (prop61F_disc f hf u)
      _ = (N : ℝ) ^ 5 := by simp; ring
  have hglobal : mixed ^ 2 ≤ fourthF * fourthG := by
    simpa only [mixed, fourthF, fourthG] using prop61_global_cauchy f B phi
  have hfourthG : alpha ^ 4 * (N : ℝ) ^ 5 ≤ fourthG := le_of_mul_le_mul_left (by
    linarith [mul_self_le_mul_self (by positivity) hmixed,
      mul_le_mul_of_nonneg_right hfourthF (Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) 4 : (0 : ℝ) ≤ fourthG)])
    (by positivity : (0 : ℝ) < (N : ℝ) ^ 5)
  have hfourthG_eq : fourthG = (N : ℝ) ^ 2 * phiAdditiveCount B phi := by
    simpa only [fourthG] using prop61_g_fourth_eq_count B phi
  exact le_of_mul_le_mul_left (by linarith) hN2

/-- Lemma 7.7 is the finite grid/pigeonhole proof of the standard Bohr-set
cardinality bound. -/
theorem lemma_7_7_holds : lemma_7_7 := by
  intro N _ K delta _ hdelta hdelta_one
  let m : Nat := ⌈delta⁻¹⌉₊
  have hm : 0 < m := by
    dsimp only [m]
    exact Nat.ceil_pos.mpr (inv_pos.mpr hdelta)
  have hm_lower : delta⁻¹ ≤ (m : ℝ) := by
    dsimp only [m]
    exact Nat.le_ceil _
  have hone_le_inv : (1 : ℝ) ≤ delta⁻¹ := (one_le_inv₀ hdelta).2 hdelta_one
  have hm_upper : (m : ℝ) ≤ 2 * delta⁻¹ := by
    have hceil := Nat.ceil_lt_add_one (inv_nonneg.mpr hdelta.le)
    dsimp only [m]
    linarith
  let gridCode : ZMod N → ((r : ↑K) → Fin m) := fun d r =>
    ⟨(r.1 * d).val * m / N, by
      apply (Nat.div_lt_iff_lt_mul (NeZero.pos N)).2
      calc
        (r.1 * d).val * m < N * m :=
          (Nat.mul_lt_mul_right hm).2 (r.1 * d).val_lt
        _ = m * N := Nat.mul_comm _ _⟩
  have hfiber_le (c : (r : ↑K) → Fin m) :
      #(Finset.univ.filter fun d : ZMod N => gridCode d = c) ≤ #(bohr K delta) := by
    let fiber : Finset (ZMod N) := Finset.univ.filter fun d => gridCode d = c
    change #fiber ≤ #(bohr K delta)
    by_cases hnonempty : fiber.Nonempty
    · obtain ⟨a, ha⟩ := hnonempty
      refine Finset.card_le_card_of_injOn (fun d => d - a) ?_ ?_
      · intro d hd
        have hda : gridCode d = gridCode a := by
          have hd' := (Finset.mem_filter.mp hd).2
          have ha' := (Finset.mem_filter.mp ha).2
          exact hd'.trans ha'.symm
        change d - a ∈ bohr K delta
        unfold bohr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro r hr
        have hcoord := congrArg Fin.val (congrFun hda ⟨r, hr⟩)
        dsimp only [gridCode] at hcoord
        rw [mul_sub]
        exact lemma77_centeredAbs_sub_le hdelta hm hm_lower hcoord
      · intro d _ e _ hde
        exact sub_left_injective hde
    · rw [(Finset.not_nonempty_iff_eq_empty.mp hnonempty)]
      exact Nat.zero_le _
  have hcountNat : N ≤ #(bohr K delta) * m ^ K.card := by
    have hcount := Finset.card_le_mul_card_image_of_maps_to
      (s := (Finset.univ : Finset (ZMod N)))
      (t := (Finset.univ : Finset ((r : ↑K) → Fin m)))
      (f := gridCode) (fun _ _ => Finset.mem_univ _) #(bohr K delta)
      (fun c _ => hfiber_le c)
    simpa using hcount
  have hcount : (N : ℝ) ≤ (#(bohr K delta) : ℝ) * (m : ℝ) ^ K.card := by
    exact_mod_cast hcountNat
  have hgrid : (delta / 2) * (m : ℝ) ≤ 1 := by
    calc
      (delta / 2) * (m : ℝ) ≤ (delta / 2) * (2 * delta⁻¹) := by gcongr
      _ = 1 := by field_simp
  have hlower : (delta / 2) ^ K.card * (N : ℝ) ≤ #(bohr K delta) := by
    calc
      (delta / 2) ^ K.card * (N : ℝ) ≤
          (delta / 2) ^ K.card * ((#(bohr K delta) : ℝ) * (m : ℝ) ^ K.card) := by gcongr
      _ = (#(bohr K delta) : ℝ) * ((delta / 2) * (m : ℝ)) ^ K.card := by ring
      _ ≤ #(bohr K delta) :=
        mul_le_of_le_one_right (Nat.cast_nonneg _) (pow_le_one₀ (by positivity) hgrid)
  refine ⟨hlower, ?_⟩
  intro hK hthreshold
  have hk : 0 < K.card := Finset.card_pos.mpr hK
  have hk_ne : K.card ≠ 0 := hk.ne'
  have hNreal : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hrootlt :
      (N : ℝ) ^ (-(1 / (K.card : ℝ))) < delta / 2 := by
    nlinarith
  have hrootpow :
      ((N : ℝ) ^ (-(1 / (K.card : ℝ)))) ^ K.card = (N : ℝ)⁻¹ := by
    rw [← Real.rpow_mul_natCast hNreal.le, show -(1 / (K.card : ℝ)) * K.card = -1 by field_simp,
      Real.rpow_neg_one]
  have hpowlt : (N : ℝ)⁻¹ < (delta / 2) ^ K.card := by
    rw [← hrootpow]
    exact pow_lt_pow_left₀ hrootlt (Real.rpow_nonneg hNreal.le _) hk_ne
  have hmass : (1 : ℝ) < (delta / 2) ^ K.card * N := by
    calc
      (1 : ℝ) = (N : ℝ)⁻¹ * N := (inv_mul_cancel₀ hNreal.ne').symm
      _ < (delta / 2) ^ K.card * N := mul_lt_mul_of_pos_right hpowlt hNreal
  have hcardReal : (1 : ℝ) < #(bohr K delta) := hmass.trans_le hlower
  have hcard : 1 < #(bohr K delta) := by exact_mod_cast hcardReal
  obtain ⟨b, hb, hb0⟩ := Finset.exists_mem_ne hcard 0
  exact ⟨b, hb, by simpa using hb0⟩

/-- Finite Fubini--Markov interchange in the form used by Lemma 10.7. -/
private theorem almostEvery_swap_of_nonneg {X Y : Type*}
    [DecidableEq X] [DecidableEq Y] (theta : ℝ) (U : Finset X) (V : Finset Y)
    (Q : X → Y → Prop) (htheta : 0 ≤ theta)
    (hcol : ∀ y, y ∈ V → AlmostEvery (1 - theta) U fun x => Q x y) :
    AlmostEvery (1 - Real.sqrt theta) U fun x =>
      AlmostEvery (1 - Real.sqrt theta) V fun y => Q x y := by
  classical
  simp only [AlmostEvery] at hcol ⊢
  let t : ℝ := Real.sqrt theta
  let row : X → ℕ := fun x => (V.filter fun y => Q x y).card
  let col : Y → ℕ := fun y => (U.filter fun x => Q x y).card
  let good : X → Prop := fun x => (1 - t) * V.card ≤ row x
  let G : Finset X := U.filter good
  let H : Finset X := U.filter fun x => ¬good x
  change (1 - t) * U.card ≤ (G.card : ℝ)
  have ht : 0 ≤ t := Real.sqrt_nonneg theta
  have htheta_sq : t ^ 2 = theta := Real.sq_sqrt htheta
  have htU : 0 ≤ t * U.card := mul_nonneg ht (Nat.cast_nonneg _)
  by_cases hV : V = ∅
  · subst V
    have hGU : G = U := by simp [G, good, row]
    rw [hGU]
    linarith
  have hVpos : (0 : ℝ) < V.card := by
    exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hV)
  by_contra hgoal
  have hGlt : (G.card : ℝ) < (1 - t) * U.card := lt_of_not_ge hgoal
  have hGH : (G.card : ℝ) + H.card = U.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := U) good
  have hHne : H.Nonempty := Finset.card_pos.mp <| by
    have : (0 : ℝ) < H.card := by linarith
    exact_mod_cast this
  -- double counting: `(1 - θ) |U| |V| ≤ Σ_y col y = Σ_x row x < |G| |V| + |H| (1 - t) |V|`
  have hlower : (1 - theta) * U.card * V.card ≤ ∑ y ∈ V, (col y : ℝ) := by
    calc
      _ = ∑ _y ∈ V, ((1 - theta) * U.card) := by simp; ring
      _ ≤ ∑ y ∈ V, (col y : ℝ) := Finset.sum_le_sum fun y hy => by simpa [col] using hcol y hy
  have hdouble : (∑ y ∈ V, (col y : ℝ)) = ∑ x ∈ U, (row x : ℝ) := by
    dsimp [col, row]
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    push_cast
    rw [Finset.sum_comm]
  have hupper :
      (∑ x ∈ U, (row x : ℝ)) < (G.card : ℝ) * V.card + H.card * ((1 - t) * V.card) := by
    calc
      _ = (∑ x ∈ U with good x, (row x : ℝ)) + ∑ x ∈ U with ¬good x, (row x : ℝ) :=
          (Finset.sum_filter_add_sum_filter_not U good (fun x => (row x : ℝ))).symm
      _ < (∑ _x ∈ U with good _x, (V.card : ℝ)) + ∑ _x ∈ U with ¬good _x, ((1 - t) * V.card) :=
          add_lt_add_of_le_of_lt
            (Finset.sum_le_sum fun x _ => by exact_mod_cast Finset.card_filter_le V (Q x))
            (Finset.sum_lt_sum_of_nonempty hHne fun x hx =>
              lt_of_not_ge (Finset.mem_filter.mp hx).2)
      _ = (G.card : ℝ) * V.card + H.card * ((1 - t) * V.card) := by simp [G, H]
  -- with `θ = t²` and `|H| = |U| - |G|` this says `t |V| ((1 - t) |U| - |G|) < 0`
  rw [show (H.card : ℝ) = U.card - G.card by linarith] at hupper
  rw [← htheta_sq] at hlower
  linarith [mul_nonneg (mul_nonneg ht hVpos.le) (sub_pos.mpr hGlt).le]

/-- Lemma 10.7 is the preceding finite Fubini--Markov interchange applied to
the local difference relation. -/
theorem lemma_10_7_holds : lemma_10_7 := by
  intro N _ X _ _ D phi W B B' psi eta
  dsimp
  intro hmodel
  rcases hmodel with ⟨_, _, hmodel⟩
  apply almostEvery_swap_of_nonneg
  · apply mul_nonneg (by norm_num)
    by_cases heta : 0 ≤ eta
    · exact Real.rpow_nonneg heta _
    · have heta_neg : eta < 0 := lt_of_not_ge heta
      rw [Real.rpow_def_of_neg heta_neg]
      apply mul_nonneg (Real.exp_pos _).le
      exact (Real.cos_pos_of_mem_Ioo (by
        have hpi := Real.pi_pos
        constructor <;> norm_num <;> nlinarith)).le
  · exact hmodel

lemma lemma78_fourier_indicator_energy {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) :
    (∑ r : ZMod N, ‖fourier (indicator A) r‖ ^ 2) =
      (N : Real) * A.card := by
  rw [identity_2_3_holds]
  congr 1
  calc
    (∑ x : ZMod N, ‖indicator A x‖ ^ 2) =
        ∑ x : ZMod N, if x ∈ A then (1 : Real) else 0 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : x ∈ A <;> simp [indicator, hx]
    _ = A.card := by simp

end LeanProofs.GowersSzemeredi
