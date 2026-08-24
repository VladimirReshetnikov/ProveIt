import GowersSzemeredi.Proofs05PhaseRemoval
import GowersSzemeredi.ProofInfrastructure
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.GroupTheory.OrderOfElement

/-!
# Downstream consequences of the Section 5 polynomial partition

This module develops the bookkeeping needed to apply the interval form of
Corollary 5.6 on an arbitrary proper modular progression.  In particular it
proves that the affine pullback of a polynomial still has the same degree
bound, and transports the resulting partition of natural indices back to
`ZMod N` without losing properness or multiplicity information.

The final density and refinement arguments are kept conditional on the one
remaining analytic input, `corollary_5_6`, so that they cannot accidentally
hide the outstanding Weyl-recurrence theorem.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ### Affine parametrization of modular progressions -/

/-- The point with natural index `t` in a modular progression. -/
def section5IndexPoint {N : Nat} (P : ModAP N) (t : Nat) : ZMod N :=
  P.start + (t : ZMod N) * P.step

/-- The same parametrization, with a modular index. -/
def section5ModIndexPoint {N : Nat} (P : ModAP N) (t : ZMod N) : ZMod N :=
  P.start + t * P.step

/-- Transport a natural-number progression through a modular progression. -/
def section5Transport {N : Nat} (P : ModAP N) (R : NatAP) : ModAP N where
  start := section5IndexPoint P R.start
  step := (R.step : ZMod N) * P.step
  length := R.length

@[simp] theorem section5Transport_length {N : Nat} (P : ModAP N) (R : NatAP) :
    (section5Transport P R).length = R.length :=
  rfl

theorem section5_modIndexPoint_natCast {N : Nat} (P : ModAP N) (t : Nat) :
    section5ModIndexPoint P (t : ZMod N) = section5IndexPoint P t :=
  rfl

theorem section5_carrier_eq_image_range {N : Nat} (P : ModAP N) :
    P.carrier = (Finset.range P.length).image (section5IndexPoint P) := by
  classical
  ext x
  unfold ModAP.carrier section5IndexPoint
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

theorem section5Transport_carrier {N : Nat} (P : ModAP N) (R : NatAP) :
    (section5Transport P R).carrier =
      R.carrier.image (section5IndexPoint P) := by
  classical
  ext x
  simp only [ModAP.carrier, NatAP.carrier, section5Transport,
    section5IndexPoint, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨R.start + (i : Nat) * R.step, ⟨i, rfl⟩, ?_⟩
    push_cast
    ring
  · rintro ⟨t, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    push_cast
    ring

theorem section5Transport_subset {N : Nat} (P : ModAP N) (R : NatAP)
    (hR : R.carrier ⊆ Finset.range P.length) :
    (section5Transport P R).carrier ⊆ P.carrier := by
  classical
  rw [section5Transport_carrier, section5_carrier_eq_image_range]
  exact Finset.image_mono _ hR

theorem section5IndexPoint_injective_on_range {N : Nat} [NeZero N]
    (P : ModAP N) (hP : P.IsProper) :
    Set.InjOn (section5IndexPoint P) (Finset.range P.length : Set Nat) := by
  classical
  rw [ModAP.IsProper, section5_carrier_eq_image_range] at hP
  have hinj : Set.InjOn (section5IndexPoint P)
      (Finset.range P.length : Set Nat) := by
    apply Finset.card_image_iff.mp
    simpa only [Finset.card_range] using hP
  exact hinj

theorem section5Transport_isProper {N : Nat} [NeZero N]
    (P : ModAP N) (R : NatAP) (hP : P.IsProper) (hR : R.IsProper)
    (hsub : R.carrier ⊆ Finset.range P.length) :
    (section5Transport P R).IsProper := by
  classical
  rw [ModAP.IsProper, section5Transport_carrier,
    Finset.card_image_iff.mpr]
  · exact hR.2
  · intro x hx y hy hxy
    exact section5IndexPoint_injective_on_range P hP (hsub hx) (hsub hy) hxy

theorem section5Transport_sum {N : Nat} [NeZero N]
    (P : ModAP N) (R : NatAP) (hP : P.IsProper)
    (hsub : R.carrier ⊆ Finset.range P.length) (g : ZMod N → Complex) :
    (∑ x ∈ (section5Transport P R).carrier, g x) =
      ∑ t ∈ R.carrier, g (section5IndexPoint P t) := by
  classical
  rw [section5Transport_carrier]
  rw [Finset.sum_image]
  intro x hx y hy hxy
  exact section5IndexPoint_injective_on_range P hP (hsub hx) (hsub hy) hxy

theorem section5Transport_partition {N M : Nat} [NeZero N]
    (P : ModAP N) (R : Fin M → NatAP) (hP : P.IsProper)
    (hR : IsNatAPPartition R (Finset.range P.length)) :
    IsPartition (fun j => (section5Transport P (R j)).carrier) P.carrier := by
  classical
  have hinj := section5IndexPoint_injective_on_range P hP
  constructor
  · intro x
    constructor
    · intro hx
      rw [section5_carrier_eq_image_range] at hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, htj⟩ := (hR.1 t).mp ht
      refine ⟨j, ?_⟩
      change section5IndexPoint P t ∈ (section5Transport P (R j)).carrier
      rw [section5Transport_carrier]
      exact Finset.mem_image.mpr ⟨t, htj, rfl⟩
    · rintro ⟨j, hx⟩
      exact section5Transport_subset P (R j)
        (IsPartition.cell_subset hR j) hx
  · intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    change x ∈ (section5Transport P (R i)).carrier at hxi
    change x ∈ (section5Transport P (R j)).carrier at hxj
    rw [section5Transport_carrier] at hxi hxj
    obtain ⟨s, hsi, hsx⟩ := Finset.mem_image.mp hxi
    obtain ⟨t, htj, htx⟩ := Finset.mem_image.mp hxj
    have hsRange := IsPartition.cell_subset hR i hsi
    have htRange := IsPartition.cell_subset hR j htj
    have hst : s = t := hinj hsRange htRange (hsx.trans htx.symm)
    subst t
    exact Finset.disjoint_left.mp (hR.2 i j hij) hsi htj

/-! ### Carrier-preserving properization -/

private lemma section5IndexPoint_mod_order {N : Nat} [NeZero N]
    (P : ModAP N) (i : Nat) :
    section5IndexPoint P (i % addOrderOf P.step) = section5IndexPoint P i := by
  unfold section5IndexPoint
  congr 1
  simpa only [nsmul_eq_mul] using mod_addOrderOf_nsmul P.step i

private lemma section5IndexPoint_injOn_order {N : Nat} [NeZero N]
    (P : ModAP N) :
    Set.InjOn (section5IndexPoint P) (Set.Iio (addOrderOf P.step)) := by
  intro i hi j hj hij
  have hmul : (i : ZMod N) * P.step = (j : ZMod N) * P.step :=
    add_left_cancel hij
  have hnsmul : i • P.step = j • P.step := by
    simpa only [nsmul_eq_mul] using hmul
  have hmod := ((isOfFinAddOrder_of_finite P.step).nsmul_inj_mod).mp hnsmul
  simpa only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hmod

private lemma section5_carrier_eq_order_range_of_le {N : Nat} [NeZero N]
    (P : ModAP N) (horder : addOrderOf P.step ≤ P.length) :
    P.carrier = (Finset.range (addOrderOf P.step)).image
      (section5IndexPoint P) := by
  classical
  rw [section5_carrier_eq_image_range]
  apply Finset.Subset.antisymm
  · intro x hx
    rw [Finset.mem_image] at hx ⊢
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨i % addOrderOf P.step, ?_, section5IndexPoint_mod_order P i⟩
    exact Finset.mem_range.mpr (Nat.mod_lt _ (addOrderOf_pos P.step))
  · intro x hx
    rw [Finset.mem_image] at hx ⊢
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨i, Finset.range_mono horder hi, rfl⟩

private lemma section5_carrier_card {N : Nat} [NeZero N] (P : ModAP N) :
    P.carrier.card = min P.length (addOrderOf P.step) := by
  classical
  by_cases hlength : P.length ≤ addOrderOf P.step
  · have hinj : Set.InjOn (section5IndexPoint P)
        (Finset.range P.length : Set Nat) := by
      intro i hi j hj hij
      exact section5IndexPoint_injOn_order P
        (lt_of_lt_of_le (Finset.mem_range.mp hi) hlength)
        (lt_of_lt_of_le (Finset.mem_range.mp hj) hlength) hij
    rw [min_eq_left hlength, section5_carrier_eq_image_range,
      Finset.card_image_iff.mpr hinj, Finset.card_range]
  · have horder : addOrderOf P.step ≤ P.length :=
      Nat.le_of_lt (Nat.lt_of_not_ge hlength)
    have hinj : Set.InjOn (section5IndexPoint P)
        (Finset.range (addOrderOf P.step) : Set Nat) := by
      intro i hi j hj hij
      exact section5IndexPoint_injOn_order P
        (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
    rw [min_eq_right horder, section5_carrier_eq_order_range_of_le P horder,
      Finset.card_image_iff.mpr hinj, Finset.card_range]

/-- Shorten an arbitrary modular progression to one traversal of its carrier. -/
def section5Normalize {N : Nat} (P : ModAP N) : ModAP N :=
  { P with length := P.carrier.card }

theorem section5Normalize_carrier {N : Nat} [NeZero N] (P : ModAP N) :
    (section5Normalize P).carrier = P.carrier := by
  classical
  let t := addOrderOf P.step
  have hcard := section5_carrier_card P
  by_cases hlength : P.length ≤ t
  · have heq : P.carrier.card = P.length := by
      simpa only [t, min_eq_left hlength] using hcard
    simp only [section5Normalize, heq]
  · have horder : t ≤ P.length := Nat.le_of_lt (Nat.lt_of_not_ge hlength)
    have heq : P.carrier.card = t := by
      simpa only [t, min_eq_right horder] using hcard
    rw [section5_carrier_eq_order_range_of_le P horder]
    change ({ P with length := P.carrier.card } : ModAP N).carrier = _
    rw [section5_carrier_eq_image_range, heq]
    rfl

theorem section5Normalize_isProper {N : Nat} [NeZero N] (P : ModAP N) :
    (section5Normalize P).IsProper := by
  rw [ModAP.IsProper, section5Normalize_carrier]
  rfl

/-! ### Affine pullback preserves the degree bound -/

theorem polynomialOn_affine_pullback {N k : Nat} [NeZero N]
    (phi : ZMod N → ZMod N) (a d : ZMod N)
    (hphi : PolynomialOn k Finset.univ phi) :
    PolynomialOn k Finset.univ
      (fun x => phi (a + x * d)) := by
  classical
  obtain ⟨c, hc⟩ := hphi
  let p : Polynomial (ZMod N) := Polynomial.ofFn (k + 1) c
  have hkpos : 1 ≤ k + 1 := Nat.succ_pos k
  have hpdeg : p.natDegree < k + 1 := by
    exact Polynomial.ofFn_natDegree_lt hkpos c
  have hpeval (x : ZMod N) :
      p.eval x = ∑ i, c i * x ^ (i : Nat) := by
    rw [Polynomial.eval_eq_sum_range' hpdeg]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _hi
    change (Polynomial.ofFn (k + 1) c).coeff (i : Nat) * x ^ (i : Nat) = _
    rw [Polynomial.ofFn_coeff_eq_val_of_lt c i.isLt]
  let affine : Polynomial (ZMod N) :=
    Polynomial.C a + Polynomial.C d * Polynomial.X
  let q : Polynomial (ZMod N) := p.comp affine
  have haffineDegree : affine.natDegree ≤ 1 := by
    dsimp only [affine]
    calc
      _ ≤ max (Polynomial.C a).natDegree
          (Polynomial.C d * Polynomial.X).natDegree :=
        Polynomial.natDegree_add_le _ _
      _ ≤ 1 := by
        apply max_le
        · simp only [Polynomial.natDegree_C]
          omega
        · exact (Polynomial.natDegree_C_mul_le d Polynomial.X).trans
            Polynomial.natDegree_X_le
  have hpdeg' : p.natDegree ≤ k := Nat.lt_succ_iff.mp hpdeg
  have hqdeg : q.natDegree < k + 1 := by
    apply Nat.lt_succ_iff.mpr
    dsimp only [q]
    exact Polynomial.natDegree_comp_le.trans
      ((Nat.mul_le_mul hpdeg' haffineDegree).trans (by simp))
  refine ⟨fun i => q.coeff i, ?_⟩
  intro x _hx
  calc
    phi (a + x * d) = p.eval (a + x * d) := (hc _ (Finset.mem_univ _)).trans
      (hpeval (a + x * d)).symm
    _ = q.eval x := by
      simp only [q, affine, Polynomial.eval_comp, Polynomial.eval_add,
        Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
      rw [mul_comm d x]
    _ = ∑ i : Fin (k + 1), q.coeff (i : Nat) * x ^ (i : Nat) := by
      rw [Polynomial.eval_eq_sum_range' hqdeg]
      rw [← Fin.sum_univ_eq_sum_range]

theorem polynomialOn_section5ModIndexPoint {N k : Nat} [NeZero N]
    (P : ModAP N) (phi : ZMod N → ZMod N)
    (hphi : PolynomialOn k Finset.univ phi) :
    PolynomialOn k Finset.univ
      (fun x => phi (section5ModIndexPoint P x)) := by
  simpa only [section5ModIndexPoint] using
    polynomialOn_affine_pullback phi P.start P.step hphi

/-! ### A uniform additive-error version of phase removal -/

@[simp] private lemma downstream_norm_exponential {N : Nat} [NeZero N]
    (x : ZMod N) : ‖exponential x‖ = 1 := by
  exact AddChar.norm_apply (ZMod.stdAddChar (N := N)) x

@[simp] private lemma downstream_exponential_add {N : Nat} [NeZero N]
    (x y : ZMod N) :
    exponential (x + y) = exponential x * exponential y := by
  exact AddChar.map_add_eq_mul (ZMod.stdAddChar (N := N)) x y

private lemma downstream_exponential_eq_exp_valMinAbs {N : Nat} [NeZero N]
    (x : ZMod N) :
    exponential x =
      Complex.exp
        (Complex.I * (2 * Real.pi * (x.valMinAbs : Real) / N : Real)) := by
  calc
    exponential x = ZMod.stdAddChar ((x.valMinAbs : Int) : ZMod N) := by
      simp [exponential]
    _ = Complex.exp (2 * Real.pi * Complex.I * (x.valMinAbs : Int) / N) :=
      ZMod.stdAddChar_coe x.valMinAbs
    _ = Complex.exp
        (Complex.I * (2 * Real.pi * (x.valMinAbs : Real) / N : Real)) := by
      congr 1
      push_cast
      ring

private lemma downstream_norm_exponential_sub_one_le {N : Nat} [NeZero N]
    (x : ZMod N) :
    ‖exponential x - 1‖ ≤ 2 * Real.pi * centeredAbs x / N := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have habsval : |(x.valMinAbs : Real)| = (centeredAbs x : Real) := by
    rw [centeredAbs, ← Int.cast_abs, Int.abs_eq_natAbs]
    rfl
  rw [downstream_exponential_eq_exp_valMinAbs]
  calc
    ‖Complex.exp
        (Complex.I * (2 * Real.pi * (x.valMinAbs : Real) / N : Real)) - 1‖ ≤
        ‖2 * Real.pi * (x.valMinAbs : Real) / N‖ :=
      Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * centeredAbs x / N := by
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : Real) ≤ 2),
        abs_of_pos Real.pi_pos, habsval, abs_of_pos hN]

private lemma downstream_centeredAbs_natCast_le {N i : Nat} [NeZero N] :
    centeredAbs (i : ZMod N) ≤ i := by
  rw [centeredAbs, ZMod.valMinAbs_natAbs_eq_min, ZMod.val_natCast]
  exact (Nat.min_le_left _ _).trans (Nat.mod_le i N)

private lemma downstream_centeredAbs_neg_natCast_le {N i : Nat} [NeZero N] :
    centeredAbs (-(i : ZMod N)) ≤ i := by
  rw [centeredAbs, ZMod.natAbs_valMinAbs_neg]
  exact downstream_centeredAbs_natCast_le

private lemma downstream_phase_close_of_mem_interval {N d : Nat} [NeZero N]
    (a y : ZMod N) (hy : y ∈ (modInterval N a (d + 1)).carrier) :
    ‖exponential (-y) - exponential (-a)‖ ≤
      2 * Real.pi * d / N := by
  classical
  unfold ModAP.carrier modInterval at hy
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy
  obtain ⟨i, rfl⟩ := hy
  have hi : (i : Nat) ≤ d := by omega
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  simp only [mul_one]
  calc
    ‖exponential (-(a + (i : ZMod N))) - exponential (-a)‖ =
        ‖exponential (-a) * (exponential (-(i : ZMod N)) - 1)‖ := by
      congr 1
      rw [show -(a + (i : ZMod N)) = -a + -(i : ZMod N) by ring]
      rw [downstream_exponential_add]
      ring
    _ = ‖exponential (-(i : ZMod N)) - 1‖ := by
      rw [norm_mul, downstream_norm_exponential, one_mul]
    _ ≤ 2 * Real.pi * centeredAbs (-(i : ZMod N)) / N :=
      downstream_norm_exponential_sub_one_le _
    _ ≤ 2 * Real.pi * d / N := by
      apply div_le_div_of_nonneg_right _ hN.le
      gcongr
      exact_mod_cast
        (downstream_centeredAbs_neg_natCast_le (N := N) (i := (i : Nat))).trans hi

private lemma downstream_cell_norm_le {N : Nat} [NeZero N]
    (S : Finset Nat) (f : ZMod N → Complex) (phi : ZMod N → ZMod N)
    (eta scale : Real) (hf : DiscValued f)
    (hdiam : diameterAtMostReal
      (S.image fun x : Nat => phi (x : ZMod N)) scale)
    (hscale : scale ≤ eta * N / (4 * Real.pi)) :
    ‖∑ s ∈ S, f (s : ZMod N) * exponential (-(phi (s : ZMod N)))‖ ≤
      ‖∑ s ∈ S, f (s : ZMod N)‖ + eta / 2 * S.card := by
  classical
  obtain ⟨d, ⟨a, hsubset⟩, hdscale⟩ := hdiam
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hphase (s : Nat) (hs : s ∈ S) :
      ‖exponential (-(phi (s : ZMod N))) - exponential (-a)‖ ≤ eta / 2 := by
    have himage : phi (s : ZMod N) ∈
        S.image (fun x : Nat => phi (x : ZMod N)) :=
      Finset.mem_image.mpr ⟨s, hs, rfl⟩
    calc
      _ ≤ 2 * Real.pi * d / N :=
        downstream_phase_close_of_mem_interval a _ (hsubset himage)
      _ ≤ 2 * Real.pi * scale / N := by gcongr
      _ ≤ eta / 2 := by
        have hpi : (0 : Real) < 4 * Real.pi := by positivity
        have hscaled : scale * (4 * Real.pi) ≤ eta * N :=
          (le_div_iff₀ hpi).1 hscale
        apply (div_le_iff₀ hN).2
        nlinarith [Real.pi_pos]
  let twisted := ∑ s ∈ S,
    f (s : ZMod N) * exponential (-(phi (s : ZMod N)))
  let plain := ∑ s ∈ S, f (s : ZMod N)
  let err := ∑ s ∈ S,
    f (s : ZMod N) *
      (exponential (-(phi (s : ZMod N))) - exponential (-a))
  have hdecomp : twisted = exponential (-a) * plain + err := by
    dsimp only [twisted, plain, err]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _hs
    ring
  have herr : ‖err‖ ≤ eta / 2 * S.card := by
    dsimp only [err]
    calc
      _ ≤ ∑ s ∈ S,
          ‖f (s : ZMod N) *
            (exponential (-(phi (s : ZMod N))) - exponential (-a))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _s ∈ S, eta / 2 := by
        apply Finset.sum_le_sum
        intro s hs
        rw [norm_mul]
        calc
          ‖f (s : ZMod N)‖ *
              ‖exponential (-(phi (s : ZMod N))) - exponential (-a)‖ ≤
              1 * (eta / 2) :=
            mul_le_mul (hf _) (hphase s hs) (norm_nonneg _) (by norm_num)
          _ = eta / 2 := one_mul _
      _ = eta / 2 * S.card := by simp [mul_comm]
  change ‖twisted‖ ≤ ‖plain‖ + eta / 2 * S.card
  rw [hdecomp]
  calc
    ‖exponential (-a) * plain + err‖ ≤
        ‖exponential (-a) * plain‖ + ‖err‖ := norm_add_le _ _
    _ ≤ ‖plain‖ + eta / 2 * S.card := by
      rw [norm_mul, downstream_norm_exponential, one_mul]
      gcongr

private lemma downstream_sum_partition {X R : Type*} [DecidableEq X]
    [AddCommMonoid R] {m : Nat} (P : Fin m → Finset X) (S : Finset X)
    (hpartition : IsPartition P S) (g : X → R) :
    ∑ j, ∑ x ∈ P j, g x = ∑ x ∈ S, g x := by
  classical
  have hpair : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint P := by
    intro i _ j _ hij
    exact hpartition.2 i j (bne_iff_ne.mpr hij)
  have hunion : (Finset.univ : Finset (Fin m)).biUnion P = S := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact (hpartition.1 x).symm
  rw [show (∑ j, ∑ x ∈ P j, g x) =
      ∑ j ∈ (Finset.univ : Finset (Fin m)), ∑ x ∈ P j, g x by simp]
  rw [← Finset.sum_biUnion hpair, hunion]

private lemma downstream_scale_le {k r : Nat} (eta : Real)
    (heta : 0 < eta)
    (hlarge :
      (4 * Real.pi / eta) ^ polynomialPartitionConstant k < (r : Real)) :
    (r : Real) ^ (-(polynomialPartitionConstant k : Real)⁻¹) * (1 : Real) ≤
      eta / (4 * Real.pi) := by
  let K := polynomialPartitionConstant k
  have hK : 0 < K := by
    dsimp only [K]
    unfold polynomialPartitionConstant
    positivity
  have hKReal : (0 : Real) < K := by exact_mod_cast hK
  have hr : (0 : Real) < r := by
    have hbase : 0 < 4 * Real.pi / eta := by positivity
    exact (pow_nonneg hbase.le K).trans_lt hlarge
  have hbase : 0 < 4 * Real.pi / eta := by positivity
  have hroot : 4 * Real.pi / eta < (r : Real) ^ (K : Real)⁻¹ := by
    rw [Real.lt_rpow_inv_iff_of_pos hbase.le hr.le hKReal]
    simpa only [Real.rpow_natCast] using hlarge
  have hrootPos : 0 < (r : Real) ^ (K : Real)⁻¹ :=
    Real.rpow_pos_of_pos hr _
  have hinv : ((r : Real) ^ (K : Real)⁻¹)⁻¹ <
      (4 * Real.pi / eta)⁻¹ :=
    (inv_lt_inv₀ hrootPos hbase).2 hroot
  rw [Real.rpow_neg hr.le]
  have hright : (4 * Real.pi / eta)⁻¹ = eta / (4 * Real.pi) := by
    field_simp
  simpa only [K, hright, mul_one] using hinv.le

/-!
The strengthened local form used in the proof of Lemma 5.14.  Unlike
Corollary 5.7, it retains the additive error estimate before a lower bound on
the original correlation is substituted.
-/
theorem section5_local_phase_refinement_of_corollary_5_6
    (h56 : corollary_5_6) {N k v : Nat} [NeZero N]
    (P : ModAP N) (phi : ZMod N → ZMod N) (eta : Real)
    (hP : P.IsProper) (hk : 1 ≤ k)
    (hphi : PolynomialOn k Finset.univ phi) (heta : 0 < eta)
    (hlarge : max (polynomialPartitionThreshold k : Real)
        ((4 * Real.pi / eta) ^ polynomialPartitionConstant k) < P.length)
    (hv : 1 ≤ v)
    (hvupper : (v : Real) ≤
      (P.length : Real) ^ (polynomialPartitionConstant k : Real)⁻¹) :
    ∃ L : Nat, ∃ R : Fin L → ModAP N,
      IsPartition (fun j => (R j).carrier) P.carrier ∧
      (∀ j, (R j).IsProper ∧ 0 < (R j).length ∧
        ((R j).length = v - 1 ∨ (R j).length = v)) ∧
      ∀ f : ZMod N → Complex, DiscValued f →
        ‖∑ s ∈ P.carrier, f s * exponential (-(phi s))‖ ≤
          (∑ j, ‖∑ s ∈ (R j).carrier, f s‖) +
            eta / 2 * P.carrier.card := by
  classical
  have hrPos : 0 < P.length := by
    have hzero : (0 : Real) ≤ polynomialPartitionThreshold k := by positivity
    have : (0 : Real) < P.length := hzero.trans_lt
      (lt_of_le_of_lt (le_max_left _ _) hlarge)
    exact_mod_cast this
  have hrN : P.length ≤ N := by
    rw [ModAP.IsProper] at hP
    rw [← hP]
    simpa only [ZMod.card] using P.carrier.card_le_univ
  have hthreshold : polynomialPartitionThreshold k < P.length := by
    exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hlarge)
  let pulledPhi : ZMod N → ZMod N :=
    fun x => phi (section5ModIndexPoint P x)
  have hpulled : PolynomialOn k Finset.univ pulledPhi :=
    polynomialOn_section5ModIndexPoint P phi hphi
  obtain ⟨L, S, hL, hpartition, hproper, hdiam⟩ :=
    h56 N k P.length v pulledPhi hk hpulled hthreshold hrN hv hvupper
  let R : Fin L → ModAP N := fun j => section5Transport P (S j)
  have hrefine : IsPartition (fun j => (R j).carrier) P.carrier := by
    exact section5Transport_partition P S hP hpartition
  have hRproper (j : Fin L) :
      (R j).IsProper ∧ 0 < (R j).length ∧
        ((R j).length = v - 1 ∨ (R j).length = v) := by
    have hsub := IsPartition.cell_subset hpartition j
    refine ⟨section5Transport_isProper P (S j) hP (hproper j).1 hsub, ?_, ?_⟩
    · simpa only [R, section5Transport_length] using (hproper j).2.1
    · simpa only [R, section5Transport_length] using (hproper j).2.2
  refine ⟨L, R, hrefine, hRproper, ?_⟩
  intro f hf
  let pulledF : ZMod N → Complex :=
    fun x => f (section5ModIndexPoint P x)
  have hpulledF : DiscValued pulledF := fun x => hf _
  have hscale :
      (P.length : Real) ^
          (-(polynomialPartitionConstant k : Real)⁻¹) * N ≤
        eta * N / (4 * Real.pi) := by
    have hpolyLarge :
        (4 * Real.pi / eta) ^ polynomialPartitionConstant k <
          (P.length : Real) :=
      lt_of_le_of_lt (le_max_right _ _) hlarge
    have hbase := downstream_scale_le eta heta hpolyLarge
    have hN : (0 : Real) ≤ N := by positivity
    calc
      _ = ((P.length : Real) ^
          (-(polynomialPartitionConstant k : Real)⁻¹) * 1) * N := by ring
      _ ≤ (eta / (4 * Real.pi)) * N :=
        mul_le_mul_of_nonneg_right hbase hN
      _ = eta * N / (4 * Real.pi) := by ring
  have hcell (j : Fin L) :
      ‖∑ s ∈ (S j).carrier,
          pulledF (s : ZMod N) * exponential (-(pulledPhi (s : ZMod N)))‖ ≤
        ‖∑ s ∈ (S j).carrier, pulledF (s : ZMod N)‖ +
          eta / 2 * (S j).carrier.card :=
    downstream_cell_norm_le (S j).carrier pulledF pulledPhi eta
      ((P.length : Real) ^
        (-(polynomialPartitionConstant k : Real)⁻¹) * N)
      hpulledF (hdiam j) hscale
  have htwisted (j : Fin L) :
      (∑ s ∈ (R j).carrier, f s * exponential (-(phi s))) =
        ∑ t ∈ (S j).carrier,
          pulledF (t : ZMod N) * exponential (-(pulledPhi (t : ZMod N))) := by
    rw [section5Transport_sum P (S j) hP
      (IsPartition.cell_subset hpartition j)]
    apply Finset.sum_congr rfl
    intro t _ht
    rfl
  have hplain (j : Fin L) :
      (∑ s ∈ (R j).carrier, f s) =
        ∑ t ∈ (S j).carrier, pulledF (t : ZMod N) := by
    rw [section5Transport_sum P (S j) hP
      (IsPartition.cell_subset hpartition j)]
    apply Finset.sum_congr rfl
    intro t _ht
    rfl
  have hphasePartition :
      (∑ j, ∑ s ∈ (R j).carrier, f s * exponential (-(phi s))) =
        ∑ s ∈ P.carrier, f s * exponential (-(phi s)) :=
    downstream_sum_partition (fun j => (R j).carrier) P.carrier hrefine _
  have hcardsNat : ∑ j, (S j).carrier.card = P.length := by
    simpa only [Finset.card_range] using IsPartition.sum_card hpartition
  have hcards : ∑ j, ((S j).carrier.card : Real) = P.carrier.card := by
    have hPcard : P.carrier.card = P.length := hP
    exact_mod_cast hcardsNat.trans hPcard.symm
  calc
    ‖∑ s ∈ P.carrier, f s * exponential (-(phi s))‖ =
        ‖∑ j, ∑ s ∈ (R j).carrier,
          f s * exponential (-(phi s))‖ := by rw [hphasePartition]
    _ ≤ ∑ j, ‖∑ s ∈ (R j).carrier,
          f s * exponential (-(phi s))‖ := norm_sum_le _ _
    _ = ∑ j, ‖∑ t ∈ (S j).carrier,
          pulledF (t : ZMod N) *
            exponential (-(pulledPhi (t : ZMod N)))‖ := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [htwisted]
    _ ≤ ∑ j, (‖∑ t ∈ (S j).carrier, pulledF (t : ZMod N)‖ +
          eta / 2 * (S j).carrier.card) := by
      apply Finset.sum_le_sum
      intro j _hj
      exact hcell j
    _ = (∑ j, ‖∑ s ∈ (R j).carrier, f s‖) +
          eta / 2 * P.carrier.card := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcards]
      congr 1
      apply Finset.sum_congr rfl
      intro j _hj
      rw [hplain]

/-! ### An efficient local refinement with a uniform constant -/

private def section5SingletonNatAP (t : Nat) : NatAP where
  start := t
  step := 1
  length := 1

@[simp] private lemma section5SingletonNatAP_carrier (t : Nat) :
    (section5SingletonNatAP t).carrier = {t} := by
  classical
  simp [section5SingletonNatAP, NatAP.carrier]

private lemma section5SingletonNatAP_isProper (t : Nat) :
    (section5SingletonNatAP t).IsProper := by
  constructor
  · simp [section5SingletonNatAP]
  · rw [section5SingletonNatAP_carrier]
    simp [section5SingletonNatAP]

private lemma section5SingletonNatAP_partition (r : Nat) :
    IsNatAPPartition (fun i : Fin r => section5SingletonNatAP i)
      (Finset.range r) := by
  classical
  constructor
  · intro x
    simp only [Finset.mem_range, section5SingletonNatAP_carrier,
      Finset.mem_singleton]
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact i.isLt
  · intro i j hij
    change Disjoint (section5SingletonNatAP (i : Nat)).carrier
      (section5SingletonNatAP (j : Nat)).carrier
    rw [section5SingletonNatAP_carrier, section5SingletonNatAP_carrier]
    exact Finset.disjoint_singleton.mpr fun h =>
      bne_iff_ne.mp hij (Fin.ext h)

/-- A concrete constant sufficient for the local form of Lemma 5.14. -/
def section5LocalRefinementConstant (k : Nat) (eta : Real) : Real :=
  max
      (max (polynomialPartitionThreshold k : Real)
        ((4 * Real.pi / eta) ^ polynomialPartitionConstant k))
      ((4 : Real) ^ polynomialPartitionConstant k) + 4

theorem section5LocalRefinementConstant_ge_four (k : Nat) (eta : Real) :
    4 ≤ section5LocalRefinementConstant k eta := by
  unfold section5LocalRefinementConstant
  have hthreshold : (0 : Real) ≤ polynomialPartitionThreshold k := by positivity
  have hinner : (0 : Real) ≤ max (polynomialPartitionThreshold k : Real)
      ((4 * Real.pi / eta) ^ polynomialPartitionConstant k) :=
    hthreshold.trans (le_max_left _ _)
  have houter : (0 : Real) ≤ max
      (max (polynomialPartitionThreshold k : Real)
        ((4 * Real.pi / eta) ^ polynomialPartitionConstant k))
      ((4 : Real) ^ polynomialPartitionConstant k) :=
    hinner.trans (le_max_left _ _)
  linarith

theorem section5LocalRefinementConstant_pos (k : Nat) (eta : Real) :
    0 < section5LocalRefinementConstant k eta := by
  exact lt_of_lt_of_le (by norm_num) (section5LocalRefinementConstant_ge_four k eta)

private lemma section5_floor_target (x : Real) (hx : 4 ≤ x) :
    ∃ v : Nat, 2 ≤ v ∧ (v : Real) ≤ x ∧ x / 2 < v := by
  have hfloorFour : 4 ≤ ⌊x⌋₊ :=
    (Nat.le_floor_iff (by positivity)).mpr hx
  refine ⟨⌊x⌋₊, by omega, Nat.floor_le (by positivity), ?_⟩
  · exact Nat.div_two_lt_floor (by linarith)

private lemma section5_rpow_root_ge_four {k r : Nat}
    (hr : (4 : Real) ^ polynomialPartitionConstant k < r) :
    4 < (r : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ := by
  have hK : (0 : Real) < polynomialPartitionConstant k := by
    unfold polynomialPartitionConstant
    positivity
  have hrpos : (0 : Real) < r := by
    exact (pow_nonneg (by norm_num : (0 : Real) ≤ 4)
      (polynomialPartitionConstant k)).trans_lt hr
  rw [Real.lt_rpow_inv_iff_of_pos (by norm_num) hrpos.le hK]
  simpa only [Real.rpow_natCast] using hr

private lemma section5_large_partition_count
    {k r v L : Nat} (hr : 0 < r)
    (hvroot : (r : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ / 2 < v)
    (hroot4 : 4 ≤ (r : Real) ^
      (polynomialPartitionConstant k : Real)⁻¹)
    (hcards : ∑ _j : Fin L, (v - 1 : Nat) ≤ r) :
    (L : Real) ≤ 4 * (r : Real) ^
      (1 - (polynomialPartitionConstant k : Real)⁻¹) := by
  let root : Real := (r : Real) ^
    (polynomialPartitionConstant k : Real)⁻¹
  have hrootPos : 0 < root := by
    dsimp only [root]
    exact Real.rpow_pos_of_pos (by exact_mod_cast hr) _
  have hvTwoReal : (2 : Real) < v := by
    have : (2 : Real) ≤
        (r : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ / 2 := by
      linarith
    exact this.trans_lt hvroot
  have hvTwo : 2 ≤ v := by exact_mod_cast hvTwoReal.le
  have hvOne : (1 : Real) ≤ v := by exact_mod_cast (show 1 ≤ v by omega)
  have hvminus : root / 4 ≤ ((v - 1 : Nat) : Real) := by
    rw [Nat.cast_sub (by exact_mod_cast hvOne)]
    change root / 2 < (v : Real) at hvroot
    change 4 ≤ root at hroot4
    linarith
  have hcardsReal : (L : Real) * (v - 1 : Nat) ≤ r := by
    have hcards' : L * (v - 1) ≤ r := by
      have hsum : (∑ _j : Fin L, (v - 1 : Nat)) = L * (v - 1) := by
        simp
      rw [hsum] at hcards
      exact hcards
    exact_mod_cast hcards'
  have hmul : (L : Real) * root ≤ 4 * r := by
    calc
      (L : Real) * root = 4 * ((L : Real) * (root / 4)) := by ring
      _ ≤ 4 * ((L : Real) * (v - 1 : Nat)) := by gcongr
      _ ≤ 4 * r := by gcongr
  have hdiv : (L : Real) ≤ 4 * r / root := by
    exact (le_div_iff₀ hrootPos).2 (by simpa only [mul_comm] using hmul)
  calc
    (L : Real) ≤ 4 * r / root := hdiv
    _ = 4 * (r : Real) ^
        (1 - (polynomialPartitionConstant k : Real)⁻¹) := by
      change 4 * (r : Real) /
          ((r : Real) ^ (polynomialPartitionConstant k : Real)⁻¹) = _
      rw [Real.rpow_sub (by exact_mod_cast hr : (0 : Real) < r),
        Real.rpow_one]
      ring

/-!
Every proper modular progression admits a phase-removing refinement with a
cell-count constant depending only on `k` and the uniform error tolerance.
This is the local quantitative engine of Lemma 5.14.
-/
theorem section5_efficient_local_phase_refinement_of_corollary_5_6
    (h56 : corollary_5_6) {N k : Nat} [NeZero N]
    (P : ModAP N) (phi : ZMod N → ZMod N) (eta : Real)
    (hP : P.IsProper) (hk : 1 ≤ k)
    (hphi : PolynomialOn k Finset.univ phi) (heta : 0 < eta) :
    ∃ L : Nat, ∃ R : Fin L → ModAP N,
      IsPartition (fun j => (R j).carrier) P.carrier ∧
      (∀ j, (R j).IsProper) ∧
      (L : Real) ≤ section5LocalRefinementConstant k eta *
        (P.carrier.card : Real) ^
          (1 - (polynomialPartitionConstant k : Real)⁻¹) ∧
      ∀ f : ZMod N → Complex, DiscValued f →
        ‖∑ s ∈ P.carrier, f s * exponential (-(phi s))‖ ≤
          (∑ j, ‖∑ s ∈ (R j).carrier, f s‖) +
            eta / 2 * P.carrier.card := by
  classical
  let K := polynomialPartitionConstant k
  let cutoff : Real := max
    (max (polynomialPartitionThreshold k : Real)
      ((4 * Real.pi / eta) ^ K)) ((4 : Real) ^ K)
  by_cases hPempty : P.carrier = ∅
  · refine ⟨0, Fin.elim0, ?_, ?_, ?_, ?_⟩
    · constructor
      · intro x
        simp [hPempty]
      · intro i
        exact Fin.elim0 i
    · intro j
      exact Fin.elim0 j
    · simpa only [Nat.cast_zero] using
        mul_nonneg (section5LocalRefinementConstant_pos k eta).le
          (Real.rpow_nonneg
            (show (0 : Real) ≤ (P.carrier.card : Real) by exact_mod_cast
              (Nat.zero_le P.carrier.card))
            (1 - (polynomialPartitionConstant k : Real)⁻¹))
    · intro f _hf
      simp [hPempty]
  have hr : 0 < P.length := by
    have hPcard : P.carrier.card = P.length := hP
    have hnonempty : P.carrier.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hPempty
    have hcardPos : 0 < P.carrier.card := Finset.card_pos.mpr hnonempty
    omega
  by_cases hlarge : cutoff < P.length
  · have hroot4strict :
        4 < (P.length : Real) ^ (K : Real)⁻¹ := by
      apply section5_rpow_root_ge_four
      exact lt_of_le_of_lt (le_max_right _ _) hlarge
    obtain ⟨v, hvTwo, hvupper, hvhalf⟩ :=
      section5_floor_target
        ((P.length : Real) ^ (K : Real)⁻¹) hroot4strict.le
    have hmainLarge : max (polynomialPartitionThreshold k : Real)
        ((4 * Real.pi / eta) ^ polynomialPartitionConstant k) < P.length := by
      exact lt_of_le_of_lt (le_max_left _ _) hlarge
    obtain ⟨L, R, hrefine, hproper, herror⟩ :=
      section5_local_phase_refinement_of_corollary_5_6 (v := v)
        h56 P phi eta hP hk hphi
        heta hmainLarge (by omega) (by simpa only [K] using hvupper)
    have hlower (j : Fin L) : v - 1 ≤ (R j).length := by
      rcases (hproper j).2.2 with h | h <;> omega
    have hsumLengths : ∑ j, (R j).length = P.carrier.card := by
      calc
        ∑ j, (R j).length = ∑ j, (R j).carrier.card := by
          apply Finset.sum_congr rfl
          intro j _hj
          exact (hproper j).1.symm
        _ = P.carrier.card := IsPartition.sum_card hrefine
    have hsumLower : ∑ _j : Fin L, (v - 1 : Nat) ≤ P.length := by
      have : ∑ _j : Fin L, (v - 1 : Nat) ≤ ∑ j, (R j).length := by
        exact Finset.sum_le_sum fun j _hj => hlower j
      rw [hsumLengths, hP] at this
      exact this
    have hcount0 : (L : Real) ≤ 4 * (P.length : Real) ^
        (1 - (K : Real)⁻¹) := by
      exact section5_large_partition_count hr (by simpa only [K] using hvhalf)
        (by simpa only [K] using hroot4strict.le) hsumLower
    have hconstant : (4 : Real) ≤ section5LocalRefinementConstant k eta := by
      exact section5LocalRefinementConstant_ge_four k eta
    refine ⟨L, R, hrefine, fun j => (hproper j).1, ?_, herror⟩
    rw [hP]
    calc
      (L : Real) ≤ 4 * (P.length : Real) ^
          (1 - (K : Real)⁻¹) := hcount0
      _ ≤ section5LocalRefinementConstant k eta *
          (P.length : Real) ^
            (1 - (polynomialPartitionConstant k : Real)⁻¹) := by
        simpa only [K] using mul_le_mul_of_nonneg_right hconstant (by positivity)
  · have hsmall : (P.length : Real) ≤ cutoff := le_of_not_gt hlarge
    let S : Fin P.length → NatAP :=
      fun i => section5SingletonNatAP i
    let R : Fin P.length → ModAP N :=
      fun i => section5Transport P (S i)
    have hpartition : IsNatAPPartition S (Finset.range P.length) := by
      exact section5SingletonNatAP_partition P.length
    have hrefine : IsPartition (fun j => (R j).carrier) P.carrier :=
      section5Transport_partition P S hP hpartition
    have hproper (j : Fin P.length) : (R j).IsProper := by
      exact section5Transport_isProper P (S j) hP
        (section5SingletonNatAP_isProper j)
        (IsPartition.cell_subset hpartition j)
    have hrootPos : 0 < (P.length : Real) ^
        (1 - (K : Real)⁻¹) := Real.rpow_pos_of_pos (by exact_mod_cast hr) _
    have hK : (0 : Real) < K := by
      dsimp only [K]
      unfold polynomialPartitionConstant
      positivity
    have hKNat : 0 < K := by exact_mod_cast hK
    have hfactor : (P.length : Real) ^ (K : Real)⁻¹ ≤ cutoff := by
      calc
        (P.length : Real) ^ (K : Real)⁻¹ ≤ (P.length : Real) := by
          simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le
              (by exact_mod_cast hr : (1 : Real) ≤ P.length)
              ((inv_le_one₀ hK).2 (by exact_mod_cast
                (show 1 ≤ K by omega)))
        _ ≤ cutoff := hsmall
    have hdecomp : (P.length : Real) =
        (P.length : Real) ^ (1 - (K : Real)⁻¹) *
          (P.length : Real) ^ (K : Real)⁻¹ := by
      rw [← Real.rpow_add (by exact_mod_cast hr : (0 : Real) < P.length)]
      ring_nf
      rw [Real.rpow_one]
    have hcount0 : (P.length : Real) ≤ cutoff *
        (P.length : Real) ^ (1 - (K : Real)⁻¹) := by
      calc
        (P.length : Real) = (P.length : Real) ^ (1 - (K : Real)⁻¹) *
            (P.length : Real) ^ (K : Real)⁻¹ := hdecomp
        _ ≤ (P.length : Real) ^ (1 - (K : Real)⁻¹) * cutoff :=
          mul_le_mul_of_nonneg_left hfactor hrootPos.le
        _ = cutoff * (P.length : Real) ^ (1 - (K : Real)⁻¹) := mul_comm _ _
    have hcutoffConstant : cutoff ≤ section5LocalRefinementConstant k eta := by
      unfold cutoff section5LocalRefinementConstant
      linarith
    have hcount : (P.length : Real) ≤ section5LocalRefinementConstant k eta *
        (P.carrier.card : Real) ^
          (1 - (polynomialPartitionConstant k : Real)⁻¹) := by
      rw [hP]
      calc
        (P.length : Real) ≤ cutoff * (P.length : Real) ^
            (1 - (K : Real)⁻¹) := hcount0
        _ ≤ section5LocalRefinementConstant k eta *
            (P.length : Real) ^
              (1 - (polynomialPartitionConstant k : Real)⁻¹) := by
          simpa only [K] using mul_le_mul_of_nonneg_right hcutoffConstant hrootPos.le
    refine ⟨P.length, R, hrefine, hproper, hcount, ?_⟩
    intro f hf
    have hphasePartition :
        (∑ j, ∑ s ∈ (R j).carrier,
          f s * exponential (-(phi s))) =
          ∑ s ∈ P.carrier, f s * exponential (-(phi s)) :=
      downstream_sum_partition (fun j => (R j).carrier) P.carrier hrefine _
    have hsingleton (j : Fin P.length) :
        ‖∑ s ∈ (R j).carrier, f s * exponential (-(phi s))‖ =
          ‖∑ s ∈ (R j).carrier, f s‖ := by
      have hcard : (R j).carrier.card = 1 := by
        rw [hproper j]
        rfl
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
      rw [hx]
      simp only [Finset.sum_singleton, norm_mul, downstream_norm_exponential, mul_one]
    calc
      ‖∑ s ∈ P.carrier, f s * exponential (-(phi s))‖ =
          ‖∑ j, ∑ s ∈ (R j).carrier,
            f s * exponential (-(phi s))‖ := by rw [hphasePartition]
      _ ≤ ∑ j, ‖∑ s ∈ (R j).carrier,
          f s * exponential (-(phi s))‖ := norm_sum_le _ _
      _ = ∑ j, ‖∑ s ∈ (R j).carrier, f s‖ := by
        apply Finset.sum_congr rfl
        intro j _hj
        exact hsingleton j
      _ ≤ (∑ j, ‖∑ s ∈ (R j).carrier, f s‖) +
          eta / 2 * P.carrier.card := by
        exact le_add_of_nonneg_right
          (mul_nonneg (div_nonneg heta.le (by norm_num))
            (show (0 : Real) ≤ (P.carrier.card : Real) by exact_mod_cast
              (Nat.zero_le P.carrier.card)))

/-- The efficient local refinement for an arbitrary (possibly wrapping or
repeating) input progression, obtained by carrier-preserving normalization. -/
theorem section5_efficient_local_phase_refinement_arbitrary_of_corollary_5_6
    (h56 : corollary_5_6) {N k : Nat} [NeZero N]
    (P : ModAP N) (phi : ZMod N → ZMod N) (eta : Real)
    (hk : 1 ≤ k) (hphi : PolynomialOn k Finset.univ phi) (heta : 0 < eta) :
    ∃ L : Nat, ∃ R : Fin L → ModAP N,
      IsPartition (fun j => (R j).carrier) P.carrier ∧
      (∀ j, (R j).IsProper) ∧
      (L : Real) ≤ section5LocalRefinementConstant k eta *
        (P.carrier.card : Real) ^
          (1 - (polynomialPartitionConstant k : Real)⁻¹) ∧
      ∀ f : ZMod N → Complex, DiscValued f →
        ‖∑ s ∈ P.carrier, f s * exponential (-(phi s))‖ ≤
          (∑ j, ‖∑ s ∈ (R j).carrier, f s‖) +
            eta / 2 * P.carrier.card := by
  obtain ⟨L, R, hrefine, hproper, hcount, herror⟩ :=
    section5_efficient_local_phase_refinement_of_corollary_5_6 h56
      (section5Normalize P) phi eta (section5Normalize_isProper P)
      hk hphi heta
  refine ⟨L, R, ?_, hproper, ?_, ?_⟩
  · simpa only [section5Normalize_carrier] using hrefine
  · simpa only [section5Normalize_carrier] using hcount
  · simpa only [section5Normalize_carrier] using herror

end LeanProofs.GowersSzemeredi
