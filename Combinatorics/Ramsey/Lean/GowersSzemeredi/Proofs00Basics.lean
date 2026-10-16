import GowersSzemeredi.Definitions

/-!
# Shared elementary lemmas

Small identities about `exponential`, `centeredAbs`, `countWhere` and Fourier transforms of
indicators that several proof modules used to re-prove privately.
-/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

section

open scoped BigOperators Pointwise ZMod ComplexConjugate
open Finset

lemma exponential_add {N : Nat} [NeZero N] (x y : ZMod N) :
    exponential (x + y) = exponential x * exponential y := by
  exact AddChar.map_add_eq_mul (ZMod.stdAddChar (N := N)) x y

end

section

open scoped BigOperators

theorem fejer_expect_exponential_mul {N : Nat} [NeZero N] (x : ZMod N) :
    (𝔼 u : ZMod N, exponential (x * u)) = if x = 0 then 1 else 0 := by
  have hs : (∑ u : ZMod N, exponential (x * u)) = if x = 0 then (N : Complex) else 0 := by
    simpa [exponential, mul_comm] using AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar N)
  rw [Finset.expect_eq_sum_div_card, Finset.card_univ, ZMod.card, hs]
  split_ifs <;> simp [NeZero.ne N]

end

section

open scoped BigOperators Pointwise ZMod ComplexConjugate
open Finset

lemma star_exponential {N : Nat} [NeZero N] (x : ZMod N) :
    star (exponential x) = exponential (-x) := by
  simpa only [exponential, starRingEnd_apply] using
    (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := N)) x).symm

end

section

open scoped BigOperators ZMod
open Finset

lemma gcs_countWhere_eq_sum_ite {X : Type*} [Fintype X]
    (P : X → Prop) :
    countWhere P = ∑ x : X,
      @ite Nat (P x) (Classical.propDecidable (P x)) 1 0 := by
  classical
  unfold countWhere
  simp

end

section

open scoped BigOperators ZMod
open Finset

lemma gcs_boolWeight_insertNth {n : Nat}
    (j : Fin (n + 1)) (b : Bool) (e : Fin n → Bool) :
    boolWeight (j.insertNth b e) = (if b then 1 else 0) + boolWeight e := by
  classical
  unfold boolWeight
  rw [gcs_countWhere_eq_sum_ite, gcs_countWhere_eq_sum_ite]
  let ind : Bool → Nat := fun c => if c then 1 else 0
  have hind (c : Bool) :
      @ite Nat (c = true) (Classical.propDecidable (c = true)) 1 0 = ind c := by
    cases c <;> simp [ind]
  have hfun :
      (fun i : Fin (n + 1) =>
        ind ((j.insertNth b e : Fin (n + 1) → Bool) i)) =
        j.insertNth (ind b) (fun i : Fin n => ind (e i)) := by
    rw [Fin.eq_insertNth_iff]
    constructor
    · simp
    · funext i
      simp [Fin.removeNth_apply]
  calc
    (∑ i : Fin (n + 1),
        @ite Nat ((j.insertNth b e : Fin (n + 1) → Bool) i = true)
          (Classical.propDecidable _) 1 0) =
        ∑ i : Fin (n + 1),
          ind ((j.insertNth b e : Fin (n + 1) → Bool) i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hind _
    _ = ∑ i : Fin (n + 1),
          (j.insertNth (ind b) (fun i : Fin n => ind (e i))) i := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrFun hfun i
    _ = ind b + ∑ i : Fin n, ind (e i) := Fin.sum_insertNth j _ _
    _ = (if b then 1 else 0) + ∑ i : Fin n, ind (e i) := by rfl
    _ = (if b then 1 else 0) +
        ∑ i : Fin n,
          @ite Nat (e i = true) (Classical.propDecidable _) 1 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact (hind _).symm

end

section

open scoped BigOperators ZMod
open Finset

lemma cor24_exponential_eq_exp_valMinAbs {N : Nat} [NeZero N]
    (x : ZMod N) :
    exponential x =
      Complex.exp (Complex.I * (2 * Real.pi * (x.valMinAbs : Real) / N : Real)) := by
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

end

section

open scoped BigOperators Pointwise ZMod
open Finset

private def lemma134Left : Finset (Fin 16) :=
  Finset.univ.filter fun i => (i : Nat) < 8

private def lemma134Right : Finset (Fin 16) :=
  Finset.univ.filter fun i => 8 ≤ (i : Nat)

private lemma lemma134_zero_mem_left : (0 : Fin 16) ∈ lemma134Left := by
  simp [lemma134Left]

private lemma lemma134_zero_notMem_right : (0 : Fin 16) ∉ lemma134Right := by
  simp [lemma134Right]

lemma lemma134_additive_ext {N : Nat}
    {x y : Fin 16 → ZMod N} (hx : IsAdditiveTuple (k := 8) x)
    (hy : IsAdditiveTuple (k := 8) y)
    (htail : ∀ i : Fin 15, x i.succ = y i.succ) : x = y := by
  have hoff : ∀ i : Fin 16, i ≠ 0 → x i = y i := by
    intro i hi
    rcases i with ⟨(_ | i), hiBound⟩
    · exact (hi rfl).elim
    · exact htail ⟨i, by omega⟩
  unfold IsAdditiveTuple at hx hy
  change (∑ i ∈ lemma134Left, x i) = ∑ i ∈ lemma134Right, x i at hx
  change (∑ i ∈ lemma134Left, y i) = ∑ i ∈ lemma134Right, y i at hy
  have hleft :
      (∑ i ∈ lemma134Left.erase 0, x i) =
        ∑ i ∈ lemma134Left.erase 0, y i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hoff i (Finset.ne_of_mem_erase hi)
  have hright :
      (∑ i ∈ lemma134Right, x i) = ∑ i ∈ lemma134Right, y i := by
    apply Finset.sum_congr rfl
    intro i hi
    apply hoff i
    intro hzero
    subst i
    exact lemma134_zero_notMem_right hi
  funext i
  refine Fin.cases ?_ (fun j => htail j) i
  apply add_left_cancel (a := ∑ i ∈ lemma134Left.erase 0, x i)
  calc
    (∑ i ∈ lemma134Left.erase 0, x i) + x 0 =
        ∑ i ∈ lemma134Left, x i :=
      Finset.sum_erase_add _ _ lemma134_zero_mem_left
    _ = ∑ i ∈ lemma134Right, x i := hx
    _ = ∑ i ∈ lemma134Right, y i := hright
    _ = ∑ i ∈ lemma134Left, y i := hy.symm
    _ = (∑ i ∈ lemma134Left.erase 0, y i) + y 0 := by
      symm
      exact Finset.sum_erase_add _ _ lemma134_zero_mem_left
    _ = (∑ i ∈ lemma134Left.erase 0, x i) + y 0 := by rw [hleft]

lemma restriction_mulLeft_range {N : Nat} [NeZero N] (h : ZMod N) :
    (AddMonoidHom.mulLeft h).range = AddSubgroup.zmultiples h := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rw [show x = (x.val : ZMod N) by
      exact (ZMod.natCast_zmod_val x).symm]
    simpa [mul_comm] using
      (AddSubgroup.intCast_mul_mem_zmultiples h (Int.ofNat x.val))
  · intro hz
    rw [AddSubgroup.mem_zmultiples_iff] at hz
    rcases hz with ⟨k, rfl⟩
    refine ⟨(k : ZMod N), ?_⟩
    change h * (k : ZMod N) = k • h
    rw [zsmul_eq_mul]
    exact mul_comm _ _

end

section

open scoped BigOperators Pointwise ZMod
open Finset

lemma restriction_mul_kernel_card {N : Nat} [NeZero N]
    (h : ZMod N) :
    Fintype.card {x : ZMod N // h * x = 0} = N.gcd h.val := by
  let f : ZMod N →+ ZMod N := AddMonoidHom.mulLeft h
  have hrange : Nat.card f.range = addOrderOf h := by
    rw [restriction_mulLeft_range h, Nat.card_zmultiples]
  have hcard : Nat.card f.ker * Nat.card f.range = Nat.card (ZMod N) := by
    rw [← AddSubgroup.index_ker f]
    exact f.ker.card_mul_index
  have hord : addOrderOf h = N / N.gcd h.val := by
    calc
      addOrderOf h = addOrderOf (h.val : ZMod N) := by
        rw [ZMod.natCast_zmod_val]
      _ = N / N.gcd h.val := ZMod.addOrderOf_coe h.val (NeZero.ne N)
  have hprod : Nat.card f.ker * (N / N.gcd h.val) = N := by
    rw [← hord, ← hrange]
    simpa using hcard
  have hgpos : 0 < N.gcd h.val :=
    Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne N))
  have hdiv : N.gcd h.val ∣ N := Nat.gcd_dvd_left _ _
  have hquotpos : 0 < N / N.gcd h.val :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hdiv)
      hgpos
  have heq : N.gcd h.val * (N / N.gcd h.val) = N :=
    Nat.mul_div_cancel' hdiv
  have hker : Nat.card f.ker = N.gcd h.val := by
    exact Nat.eq_of_mul_eq_mul_right hquotpos (hprod.trans heq.symm)
  let e : {x : ZMod N // h * x = 0} ≃ f.ker :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun x ↦ by rfl)
  calc
    Fintype.card {x : ZMod N // h * x = 0} = Fintype.card f.ker :=
      Fintype.card_congr e
    _ = N.gcd h.val := by
      simpa [Nat.card_eq_fintype_card] using hker

end

section

open scoped BigOperators Pointwise ZMod
open Finset

lemma fejer_prod_exponential {N : Nat} [NeZero N]
    {I : Type*} [Fintype I] (f : I → ZMod N) :
    ∏ i, exponential (f i) = exponential (∑ i, f i) := by
  classical
  symm
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => exact AddChar.map_zero_eq_one (ZMod.stdAddChar (N := N))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, exponential_add,
        Finset.prod_insert hi, ih]

end

section

open scoped BigOperators Pointwise ZMod Combinatorics.Additive
open Finset

lemma fejer_sum_exponential_mul {N : Nat} [NeZero N] (x : ZMod N) :
    ∑ u : ZMod N, exponential (x * u) = if x = 0 then (N : Complex) else 0 := by
  simpa [exponential, mul_comm] using
    AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar N)

end

section

open scoped BigOperators Pointwise ZMod
open Finset

lemma lemma154_sum_mul_sub_eq_two {N : Nat} {I : Type*}
    [Fintype I] [DecidableEq I] (a x y : I → ZMod N) (i j : I)
    (hij : i ≠ j) (hoff : ∀ t, t ≠ i → t ≠ j → x t = y t) :
    (∑ t, a t * x t) - (∑ t, a t * y t) =
      a i * (x i - y i) + a j * (x j - y j) := by
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ t, (a t * x t - a t * y t)) =
        ∑ t, a t * (x t - y t) := by
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = ∑ t ∈ ({i, j} : Finset I), a t * (x t - y t) := by
      symm
      apply Finset.sum_subset (by simp)
      intro t _ ht
      have hti : t ≠ i := by
        intro h
        subst t
        exact ht (by simp)
      have htj : t ≠ j := by
        intro h
        subst t
        exact ht (by simp)
      rw [hoff t hti htj, sub_self, mul_zero]
    _ = a i * (x i - y i) + a j * (x j - y j) := by simp [hij]

end

section

open scoped BigOperators ZMod
open Finset

lemma cor57_norm_exponential {N : Nat} [NeZero N]
    (x : ZMod N) : ‖exponential x‖ = 1 := by
  exact AddChar.norm_apply (ZMod.stdAddChar (N := N)) x

end

section

open scoped BigOperators Pointwise ZMod
open Finset

lemma prop121_vector_orthogonality {N p : Nat} [NeZero N]
    (x : Fin p → ZMod N) :
    (∑ u : Fin p → ZMod N, ∏ i, exponential (x i * u i)) =
      if ∀ i, x i = 0 then ((N : Nat) ^ p : Complex) else 0 := by
  calc
    (∑ u : Fin p → ZMod N, ∏ i, exponential (x i * u i)) =
        ∏ i : Fin p, ∑ a : ZMod N, exponential (x i * a) := by
          exact (Fintype.prod_sum (fun i (a : ZMod N) => exponential (x i * a))).symm
    _ = ∏ i : Fin p, if x i = 0 then (N : Complex) else 0 := by
          apply Finset.prod_congr rfl
          intro i _
          rw [fejer_sum_exponential_mul]
    _ = if ∀ i, x i = 0 then ((N : Nat) ^ p : Complex) else 0 := by
          by_cases h : ∀ i, x i = 0
          · rw [if_pos h]
            simp only [h, if_true, Finset.prod_const, Finset.card_univ]
            rw [Fintype.card_fin]
          · rw [if_neg h, Finset.prod_eq_zero_iff]
            push Not at h
            obtain ⟨i, hi⟩ := h
            exact ⟨i, Finset.mem_univ i, if_neg hi⟩

end

section

open scoped BigOperators Pointwise ZMod
open Finset

lemma rangeDeg_exists_det_pair {N : Nat} [NeZero N] [Fact N.Prime]
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (a b : I → ZMod N) (ha : ∀ i, a i ≠ 0)
    (hnot : ¬ ∃ q, ∀ i, b i = q * a i) :
    ∃ i j, i ≠ j ∧ a i * b j - a j * b i ≠ 0 := by
  classical
  by_contra h
  push Not at h
  let i0 : I := Classical.choice inferInstance
  apply hnot
  refine ⟨b i0 / a i0, ?_⟩
  intro j
  have hdet : a i0 * b j - a j * b i0 = 0 := by
    by_cases hij : i0 = j
    · subst j
      ring
    · exact h i0 j hij
  field_simp [ha i0]
  simpa [mul_comm] using sub_eq_zero.mp hdet

end

section

open scoped BigOperators Pointwise ZMod
open Finset

lemma lemma154_card_le_of_fiber_le {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq B] (f : A → B) (k : Nat)
    (h : ∀ b, Fintype.card {a : A // f a = b} ≤ k) :
    Fintype.card A ≤ Fintype.card B * k := by
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv f), Fintype.card_sigma]
  calc
    (∑ b : B, Fintype.card {a : A // f a = b}) ≤ ∑ _ : B, k :=
      Finset.sum_le_sum fun b _ ↦ h b
    _ = Fintype.card B * k := by simp

end

section

open scoped BigOperators ZMod
open Finset

lemma fourier_indicator_norm_le_card {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (r : ZMod N) :
    ‖fourier (indicator A) r‖ <= A.card := by
  classical
  rw [fourier, ZMod.dft_apply]
  calc
    ‖∑ x : ZMod N, ZMod.stdAddChar (-(x * r)) • indicator A x‖ <=
        ∑ x : ZMod N, ‖ZMod.stdAddChar (-(x * r)) • indicator A x‖ :=
      norm_sum_le _ _
    _ = ∑ x : ZMod N, if x ∈ A then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ A <;> simp [indicator, hx]
    _ = A.card := by simp

end

section

open scoped BigOperators ZMod
open Finset

lemma cor58_sum_partition {X R : Type*} [DecidableEq X] {m : Nat}
    [AddCommMonoid R] (P : Fin m → Finset X) (S : Finset X)
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

end

section

open scoped BigOperators ZMod
open Finset

lemma cor25_density_bounds {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) : 0 ≤ density A ∧ density A ≤ 1 := by
  have hcard : A.card ≤ N := by
    calc
      A.card ≤ (Finset.univ : Finset (ZMod N)).card := A.card_le_univ
      _ = N := by simp
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  constructor
  · unfold density
    positivity
  · unfold density
    rw [div_le_one hN]
    exact_mod_cast hcard

end

section

open scoped BigOperators ZMod
open Finset

lemma sum_range_pow_le_two_mul_pow (n d : Nat) (hn : 2 ≤ n) :
    (∑ j ∈ Finset.range (d + 1), n ^ j) ≤ 2 * n ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Finset.sum_range_succ]
      have hstep : 2 * n ^ d ≤ n ^ (d + 1) := by
        rw [pow_succ]
        nlinarith [Nat.zero_le (n ^ d)]
      calc
        (∑ j ∈ Finset.range (d + 1), n ^ j) + n ^ (d + 1) ≤
            2 * n ^ d + n ^ (d + 1) := Nat.add_le_add_right ih _
        _ ≤ n ^ (d + 1) + n ^ (d + 1) := Nat.add_le_add_right hstep _
        _ = 2 * n ^ (d + 1) := by omega

end

section

open scoped BigOperators Pointwise ZMod ComplexConjugate
open Finset

lemma exponential_zero {N : Nat} [NeZero N] :
    exponential (0 : ZMod N) = 1 := by
  exact AddChar.map_zero_eq_one (ZMod.stdAddChar (N := N))

end

section

theorem lemma55_centeredAbs_intCast_le {N : Nat} [NeZero N] (i : Int) :
    centeredAbs (i : ZMod N) ≤ i.natAbs := by
  have hnat (n : Nat) : centeredAbs (n : ZMod N) ≤ n := by
    rw [centeredAbs, ZMod.valMinAbs_natAbs_eq_min, ZMod.val_natCast]
    exact (Nat.min_le_left _ _).trans (Nat.mod_le n N)
  cases i with
  | ofNat n => simpa using hnat n
  | negSucc n =>
      have heq : ((Int.negSucc n : Int) : ZMod N) = -((n + 1 : Nat) : ZMod N) := by
        push_cast
        ring
      rw [heq, centeredAbs, ZMod.natAbs_valMinAbs_neg]
      exact hnat (n + 1)

end

section

open scoped BigOperators

lemma feature_countWhere_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (P : Y → Prop) :
    countWhere P = countWhere (fun x ↦ P (e x)) := by
  classical
  simp_rw [gcs_countWhere_eq_sum_ite]
  exact (e.sum_comp (fun y ↦ if P y then 1 else 0)).symm

end

section

open scoped BigOperators ZMod
open Finset

lemma fourier_indicator_zero {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) : fourier (indicator A) 0 = (A.card : Complex) := by
  classical
  simp [fourier, ZMod.dft_apply, indicator]

end

section

open scoped BigOperators ZMod
open Finset

lemma fourier_indicator_norm_le_card' {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (r : ZMod N) :
    ‖fourier (indicator A) r‖ ≤ A.card := by
  exact fourier_indicator_norm_le_card A r

end

section

open scoped BigOperators Pointwise ZMod
open Finset

lemma natCast_centeredAbs_eq_or_neg {N : Nat} [NeZero N]
    (r : ZMod N) : (centeredAbs r : ZMod N) = r ∨
      (centeredAbs r : ZMod N) = -r := by
  have hcast := ZMod.natCast_natAbs_valMinAbs r
  unfold centeredAbs
  split at hcast
  · exact Or.inl hcast
  · exact Or.inr hcast

end

section

open scoped BigOperators Pointwise ZMod
open Finset

lemma lemma154_level_subtype_card {N k : Nat} [NeZero N]
    (mu : Point N k → ZMod N) (a : ZMod N) :
    Fintype.card {y : Point N k // mu y = a} =
      countWhere fun y : Point N k => mu y = a := by
  classical
  unfold countWhere
  rw [Finset.filter_congr_decidable]
  exact Fintype.card_subtype (fun y : Point N k => mu y = a)

end

section

open scoped BigOperators ZMod
open Finset

lemma cor58_density_eq {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (delta : Real)
    (hcard : (A.card : Real) = delta * N) : density A = delta := by
  rw [density, hcard]
  exact mul_div_cancel_right₀ delta (by exact_mod_cast NeZero.ne N)

end

section

open scoped BigOperators ZMod
open Finset

lemma countWhere_eq_sum_ite {T : Type*} [Fintype T]
    (P : T → Prop) [DecidablePred P] :
    countWhere P = ∑ x : T, if P x then 1 else 0 := by
  classical
  unfold countWhere
  rw [Finset.filter_congr_decidable]
  simp

end

section

open scoped BigOperators Pointwise ZMod
open Finset

lemma context_countWhere_prod {X Y : Type*} [Fintype X] [Fintype Y]
    (P : X → Y → Prop) :
    countWhere (fun z : X × Y ↦ P z.1 z.2) =
      ∑ x : X, countWhere (P x) := by
  classical
  simp_rw [gcs_countWhere_eq_sum_ite]
  rw [Fintype.sum_prod_type]

end

section

open scoped BigOperators ZMod
open Finset

lemma lemma78_indicator_star {N : Nat}
    (A : Finset (ZMod N)) (x : ZMod N) : star (indicator A x) = indicator A x := by
  classical
  by_cases hx : x ∈ A <;> simp [indicator, hx]

end

section

open scoped BigOperators Pointwise ZMod
open Finset

lemma modInterval_one_carrier {N : Nat} (t : ZMod N) :
    (modInterval N t 1).carrier = {t} := by
  classical
  ext x
  simp [modInterval, ModAP.carrier]

end

section

open scoped BigOperators Pointwise ZMod
open Finset

lemma prop141_prod_four {p : Nat} (a b c d : Fin p → Complex) :
    (∏ i, a i) * (∏ i, b i) * (∏ i, c i) * (∏ i, d i) =
      ∏ i, a i * b i * c i * d i := by
  symm
  simp only [Finset.prod_mul_distrib]

end

section

/-- A constant `c ≤ 2^n` is at most `w^n` for `w ≥ 2`. -/
theorem const_le_pow {w c : Real} {n : Nat} (hw : 2 ≤ w) (hc : c ≤ 2 ^ n) : c ≤ w ^ n :=
  hc.trans (pow_le_pow_left₀ (by norm_num) hw n)

end

end LeanProofs.GowersSzemeredi
