/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Dynamics.DenseProductPowerBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem nearInteger_mono {ε δ x : ℝ} (h : NearInteger ε x) (hle : ε ≤ δ) :
    NearInteger δ x := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, hm.trans hle⟩

theorem nearInteger_of_pos_density_const {X : Type*} [Fintype X] {ε x : ℝ}
    (h : 0 < nearIntegerDensity (fun _ : X => x) ε) : NearInteger ε x := by
  by_contra hn
  simp [nearIntegerDensity, hn] at h

theorem expect_dependent_fin_cons {n : ℕ} {X : Fin (n+1) → Type*}
    [∀ i, Fintype (X i)] {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
    (F : (∀ i, X i) → M) :
    (𝔼 x, F x) = 𝔼 a : X 0, 𝔼 y : ∀ i : Fin n, X i.succ, F (Fin.cons a y) := by
  calc
    (𝔼 x, F x) = 𝔼 p : X 0 × (∀ i : Fin n, X i.succ), F (Fin.cons p.1 p.2) := by
      apply Fintype.expect_equiv (Fin.consEquiv X).symm
      intro x
      congr 1
      simp
    _ = _ := by
      simpa using (Finset.expect_product' (Finset.univ : Finset (X 0))
        (Finset.univ : Finset (∀ i : Fin n, X i.succ)) (fun a y => F (Fin.cons a y)))

theorem nearIntegerDensity_product_cons {n : ℕ} {X : Fin (n+1) → Type*}
    [∀ i, Fintype (X i)] (v : ∀ i, X i → ℤ) (θ ε : ℝ) :
    nearIntegerDensity (fun x : ∀ i, X i => θ * ∏ i, (v i (x i) : ℝ)) ε =
      𝔼 y : ∀ i : Fin n, X i.succ,
        nearIntegerDensity (fun a : X 0 =>
          (v 0 a : ℝ) * (θ * ∏ i : Fin n, (v i.succ (y i) : ℝ))) ε := by
  unfold nearIntegerDensity
  rw [expect_dependent_fin_cons, Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro y _
  apply Finset.expect_congr rfl
  intro a _
  congr 2
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

end Erdos3

end

section

namespace Erdos3

theorem dense_product_step_tolerance {B C H K ε : ℝ}
    (hC : 0 < C) (hH : 1 ≤ H) (hK : 0 < K)
    (hcoef : 384*B^2*C ≤ K) (hε : 0 ≤ ε) (hsmall : ε ≤ 1/K) :
    384*B^2*ε/H ≤ 1/C := by
  have hεK : K*ε ≤ 1 := by nlinarith [(le_div_iff₀ hK).mp hsmall]
  calc
    384*B^2*ε/H ≤ 384*B^2*ε := div_le_self (by positivity) hH
    _ ≤ (K/C)*ε := mul_le_mul_of_nonneg_right ((le_div_iff₀ hC).mpr hcoef) hε
    _ = K*ε/C := by ring
    _ ≤ 1/C := div_le_div_of_nonneg_right hεK hC.le

theorem dense_product_error_composition {B C H K P ε : ℝ}
    (hH : 0 < H) (hP : 0 < P) (hcoef : 384*B^2*C ≤ K) (hε : 0 ≤ ε) :
    C*(384*B^2*ε/H)/P ≤ K*ε/(H*P) := by
  calc
    C*(384*B^2*ε/H)/P = (384*B^2*C)*ε/(H*P) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hε)
      (mul_pos hH hP).le

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_common_rational_approximations {I : Type*} [Fintype I] [DecidableEq I]
    (θ : I → ℝ) {Q E : ℝ}
    (h : ∀ i, ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Q ∧ ∃ m : ℤ, |θ i-(m : ℝ)/q| ≤ E) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ Q^Fintype.card I ∧
      ∃ a : I → ℤ, ∀ i, |θ i-(a i : ℝ)/D| ≤ E := by
  choose q hq hqQ m hm using h
  let D := ∏ i, q i
  let rest := fun i => ∏ j ∈ Finset.univ.erase i, q j
  have hrest (i : I) : 0 < rest i := Finset.prod_pos (fun j _ => hq j)
  have hD (i : I) : q i * rest i = D :=
    Finset.mul_prod_erase Finset.univ q (Finset.mem_univ i)
  have hDp : 0 < D := Finset.prod_pos (fun i _ => hq i)
  refine ⟨D,hDp,?_,(fun i => (rest i : ℤ)*m i),?_⟩
  · calc
      (D : ℝ) = ∏ i, (q i : ℝ) := by simp [D]
      _ ≤ ∏ _i : I, Q := Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hqQ i)
      _ = Q^Fintype.card I := by simp
  · intro i
    have hqr : (0 : ℝ) < q i := by exact_mod_cast hq i
    have hrr : (0 : ℝ) < rest i := by exact_mod_cast hrest i
    have hd : (D : ℝ) = (q i : ℝ)*rest i := by exact_mod_cast (hD i).symm
    have he : (((rest i : ℤ)*m i : ℤ) : ℝ)/(D : ℝ) = (m i : ℝ)/q i := by
      push_cast
      rw [hd]
      field_simp
    rw [he]
    exact hm i

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem sum_dependent_fin_cons {n : ℕ} {X : Fin (n + 1) → Type*}
    [∀ i, Fintype (X i)] {M : Type*} [AddCommMonoid M]
    (F : (∀ i, X i) → M) :
    (∑ x, F x) = ∑ a : X 0, ∑ y : ∀ i : Fin n, X i.succ, F (Fin.cons a y) := by
  calc
    _ = ∑ p : X 0 × (∀ i : Fin n, X i.succ), F (Fin.cons p.1 p.2) := by
      apply Fintype.sum_equiv (Fin.consEquiv X).symm
      intro x
      congr 1
      simp
    _ = _ := Fintype.sum_prod_type _

theorem dependent_fin_cons_map {n : ℕ} {X E : Fin (n + 1) → Type*}
    (a : ∀ i, X i → E i) (x : X 0) (y : ∀ i : Fin n, X i.succ) :
    (fun i => a i (Fin.cons x y i)) = Fin.cons (a 0 x) (fun i => a i.succ (y i)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

namespace FiniteProbabilityWeights

theorem complexMean_const {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X) (z : ℂ) :
    p.complexMean (fun _ => z) = z := by
  unfold complexMean
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, p.total, Complex.ofReal_one, one_mul]

theorem complexMean_pi_fin_cons {n : ℕ} {X : Fin (n + 1) → Type*}
    [∀ i, Fintype (X i)] (p : ∀ i, FiniteProbabilityWeights (X i))
    (F : (∀ i, X i) → ℂ) :
    (pi p).complexMean F = (p 0).complexMean (fun a =>
      (pi (fun i : Fin n => p i.succ)).complexMean (fun y => F (Fin.cons a y))) := by
  change (∑ x, ((∏ i, (p i).weight (x i) : ℝ) : ℂ) * F x) =
    ∑ a, ((p 0).weight a : ℂ) *
      (∑ y, ((∏ i : Fin n, (p i.succ).weight (y i) : ℝ) : ℂ) * F (Fin.cons a y))
  rw [sum_dependent_fin_cons]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Complex.ofReal_mul,
    Finset.mul_sum, mul_assoc]

theorem complexMean_empty_tuple {X : Fin 0 → Type*} [∀ i, Fintype (X i)]
    (p : FiniteProbabilityWeights (∀ i, X i)) (F : (∀ i, X i) → ℂ) :
    p.complexMean F = F (fun i => Fin.elim0 i) := by
  have hF : F = fun _ => F (fun i => Fin.elim0 i) := by
    funext x
    exact congrArg F (Subsingleton.elim _ _)
  rw [hF, p.complexMean_const]

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem dense_product_fiber {X Y : Type*} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (v : X → ℤ) (hv : Function.Injective v) (a : Y → ℝ) (B H : ℕ) (hB : 1 ≤ B)
    (hH : 8*B ≤ H) (hcard : H ≤ Fintype.card X) (hbound : ∀ x, |v x| ≤ (H : ℤ))
    {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ 1/(256*(B : ℝ)^2))
    (hdensity : 1/(B : ℝ) ≤ 𝔼 y, nearIntegerDensity (fun x => (v x : ℝ)*a y) ε) :
    ∃ q : ℕ, 0 < q ∧ q ≤ 8*B ∧
      1/(16*(B : ℝ)^2) ≤ nearIntegerDensity (fun y => (q : ℝ)*a y) (384*(B : ℝ)^2*ε/H) := by
  have hBp : (0 : ℝ) < B := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hB)
  obtain ⟨S, hS, hfibers⟩ := exists_dense_level_set
    (fun y => nearIntegerDensity (fun x => (v x : ℝ)*a y) ε)
    (show 0 ≤ 1/(B : ℝ) by positivity) (fun y => nearIntegerDensity_le_one _ _) hdensity
  have hchoice : ∀ y : Y, ∃ q : ℕ, 0 < q ∧ q ≤ 8*B ∧
      (y ∈ S → NearInteger (384*(B : ℝ)^2*ε/H) ((q : ℝ)*a y)) := by
    intro y
    by_cases hy : y ∈ S
    · have hsmall' : ε ≤ 1/(64*((2*B : ℕ) : ℝ)^2) := by
        convert hsmall using 1
        push_cast
        ring
      have hd : 1/((2*B : ℕ) : ℝ) ≤ nearIntegerDensity (fun x => (v x : ℝ)*a y) ε := by
        have he : 1/((2*B : ℕ) : ℝ) = (1/(B : ℝ))/2 := by push_cast; field_simp
        rw [he]
        exact hfibers y hy
      obtain ⟨q, hq, hqB, hnear⟩ := nearInteger_multiples v hv (2*B) H (by omega)
        (by omega) hcard hbound hε hsmall' hd
      refine ⟨q, hq, by omega, fun _ => ?_⟩
      have he : 96*((2*B : ℕ) : ℝ)^2*ε/H = 384*(B : ℝ)^2*ε/H := by push_cast; ring
      rwa [he] at hnear
    · exact ⟨1, by omega, by omega, fun hy' => (hy hy').elim⟩
  choose q hq hqB hnear using hchoice
  have hpigeon : ((8*B : ℕ) : ℝ)*((1/(16*(B : ℝ)^2))*Fintype.card Y) ≤ S.card := by
    have he : ((8*B : ℕ) : ℝ)*((1/(16*(B : ℝ)^2))*Fintype.card Y) =
        (1/(B : ℝ))/2*Fintype.card Y := by push_cast; field_simp; ring
    rw [he]
    exact hS
  obtain ⟨q₀, hq₀, hq₀B, E, hES, hE, hconst⟩ :=
    exists_constant_denominator_fiber S q (by omega : 0 < 8*B)
      (fun y _ => ⟨hq y, hqB y⟩) hpigeon
  refine ⟨q₀, hq₀, hq₀B, ?_⟩
  have hY : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos
  apply ((le_div_iff₀ hY).mpr hE).trans
  apply card_div_le_nearIntegerDensity _ _ E
  intro y hy
  rw [← hconst y hy]
  exact hnear y (hES hy)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem independent_rational_frequencies {D : Type*} [Fintype D] [DecidableEq D]
    {J : D → Type*} (θ : ∀ d, J d → ℝ) (K : D → ℕ) (B E : D → ℝ)
    (h : ∀ d, ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ B d ∧
      ∃ (a : J d → ℤ) (ξ : J d → ℝ), (∀ j, |ξ j| ≤ E d) ∧
        ∀ j, θ d j = (a j : ℝ) / m + ξ j / K d) :
    ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ ∏ d, B d ∧
      ∃ (a : ∀ d, J d → ℤ) (ξ : ∀ d, J d → ℝ),
        (∀ d j, |ξ d j| ≤ E d) ∧ ∀ d j, θ d j = (a d j : ℝ) / M + ξ d j / K d := by
  choose m hm hB a ξ hξ hθ using h
  let M := ∏ d, m d
  let rest := fun d => ∏ e ∈ Finset.univ.erase d, m e
  have hrest (d) : 0 < rest d := Finset.prod_pos (fun e _ => hm e)
  have hM (d) : m d * rest d = M := Finset.mul_prod_erase Finset.univ m (Finset.mem_univ d)
  refine ⟨M, Finset.prod_pos (fun d _ => hm d), ?_,
    (fun d j => (rest d : ℤ) * a d j), ξ, hξ, ?_⟩
  · change ((∏ d, m d : ℕ) : ℝ) ≤ _
    rw [Nat.cast_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun d _ => hB d)
  · intro d j
    have hmR : (0 : ℝ) < m d := by exact_mod_cast hm d
    have hrR : (0 : ℝ) < rest d := by exact_mod_cast hrest d
    have hMR : (M : ℝ) = (m d : ℝ) * rest d := by exact_mod_cast (hM d).symm
    have he : (((rest d : ℤ) * a d j : ℤ) : ℝ) / M = (a d j : ℝ) / m d := by
      push_cast
      rw [hMR]
      field_simp
    rw [he]
    exact hθ d j

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_common_rational_approximations_varying {I : Type*} [Fintype I] [DecidableEq I]
    (θ Q E : I → ℝ)
    (h : ∀ i, ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Q i ∧ ∃ m : ℤ, |θ i - (m : ℝ) / q| ≤ E i) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ ∏ i, Q i ∧
      ∃ a : I → ℤ, ∀ i, |θ i - (a i : ℝ) / D| ≤ E i := by
  choose q hq hqQ m hm using h
  let D := ∏ i, q i
  let rest := fun i => ∏ j ∈ Finset.univ.erase i, q j
  have hrest (i : I) : 0 < rest i := Finset.prod_pos (fun j _ => hq j)
  have hD (i : I) : q i * rest i = D :=
    Finset.mul_prod_erase Finset.univ q (Finset.mem_univ i)
  have hDp : 0 < D := Finset.prod_pos (fun i _ => hq i)
  refine ⟨D, hDp, ?_, (fun i => (rest i : ℤ) * m i), ?_⟩
  · calc
      (D : ℝ) = ∏ i, (q i : ℝ) := by simp [D]
      _ ≤ ∏ i, Q i := Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hqQ i)
  · intro i
    have hqr : (0 : ℝ) < q i := by exact_mod_cast hq i
    have hrr : (0 : ℝ) < rest i := by exact_mod_cast hrest i
    have hd : (D : ℝ) = (q i : ℝ) * rest i := by exact_mod_cast (hD i).symm
    have he : (((rest i : ℤ) * m i : ℤ) : ℝ) / (D : ℝ) = (m i : ℝ) / q i := by
      push_cast
      rw [hd]
      field_simp
    rw [he]
    exact hm i

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem dense_product_approximation (e B : ℕ) (hB : 1 ≤ B)
    {X : Fin e → Type*} [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    (v : ∀ i, X i → ℤ) (hv : ∀ i, Function.Injective (v i)) (N : Fin e → ℕ)
    (hN : ∀ i, denseProductBudget e B ≤ N i)
    (hcard : ∀ i, N i ≤ Fintype.card (X i))
    (hbound : ∀ i x, |v i x| ≤ (N i : ℤ))
    {θ ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ 1/(denseProductBudget e B : ℝ))
    (hdensity : 1/(B : ℝ) ≤
      nearIntegerDensity (fun x : ∀ i, X i => θ * ∏ i, (v i (x i) : ℝ)) ε) :
    ∃ q : ℕ, 0 < q ∧ q ≤ denseProductBudget e B ∧
      NearInteger ((denseProductBudget e B : ℝ)*ε / ∏ i, (N i : ℝ)) ((q : ℝ)*θ) := by
  induction e generalizing B θ ε with
  | zero =>
    have hBp : (0 : ℝ) < B := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hB)
    have hd : 0 < nearIntegerDensity (fun _ : ∀ i, X i => θ) ε := by
      simpa only [Fin.prod_univ_zero, mul_one] using
        (lt_of_lt_of_le (one_div_pos.mpr hBp) hdensity)
    refine ⟨1, by omega, le_rfl, ?_⟩
    simpa only [denseProductBudget, Nat.cast_one, one_mul, Fin.prod_univ_zero, div_one]
      using nearInteger_of_pos_density_const hd
  | succ e ih =>
    let C := denseProductBudget e (16*B^2)
    let K := denseProductBudget (e+1) B
    obtain ⟨h8, hCK, h256, h384, h8C⟩ := denseProductBudget_step_bounds e B hB
    have hB' : 1 ≤ 16*B^2 := by nlinarith
    have hCp : (0 : ℝ) < C := by exact_mod_cast denseProductBudget_pos e (16*B^2) hB'
    have hKp : (0 : ℝ) < K := by exact_mod_cast denseProductBudget_pos (e+1) B hB
    have hNp : ∀ i, (0 : ℝ) < N i := by
      intro i
      exact_mod_cast (lt_of_lt_of_le (denseProductBudget_pos (e+1) B hB) (hN i))
    have hN1 : (1 : ℝ) ≤ N 0 := by
      exact_mod_cast (lt_of_lt_of_le (denseProductBudget_pos (e+1) B hB) (hN 0))
    have hcoef : 384*(B : ℝ)^2*C ≤ K := by exact_mod_cast h384
    have hsmall' : ε ≤ 1/(256*(B : ℝ)^2) := by
      apply hsmall.trans
      apply one_div_le_one_div_of_le
      · have hBp : (0 : ℝ) < B := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hB)
        positivity
      · exact_mod_cast h256
    obtain ⟨q₀, hq₀, hq₀B, hd⟩ := dense_product_fiber (v 0) (hv 0)
      (fun y : ∀ i : Fin e, X i.succ => θ * ∏ i, (v i.succ (y i) : ℝ)) B (N 0) hB
      (h8.trans (hN 0)) (hcard 0) (hbound 0) hε hsmall'
      (by rwa [nearIntegerDensity_product_cons] at hdensity)
    let δ := 384*(B : ℝ)^2*ε/N 0
    have hδ : 0 ≤ δ := by dsimp [δ]; positivity
    have hδsmall : δ ≤ 1/(denseProductBudget e (16*B^2) : ℝ) :=
      dense_product_step_tolerance hCp hN1 hKp hcoef hε hsmall
    have hd' : 1/((16*B^2 : ℕ) : ℝ) ≤ nearIntegerDensity
        (fun y : ∀ i : Fin e, X i.succ => ((q₀ : ℝ)*θ) * ∏ i, (v i.succ (y i) : ℝ)) δ := by
      simpa only [δ, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using hd
    obtain ⟨q₁, hq₁, hq₁C, hnear⟩ := ih (16*B^2) hB'
      (fun i => v i.succ) (fun i => hv i.succ) (fun i => N i.succ)
      (fun i => hCK.trans (hN i.succ)) (fun i => hcard i.succ)
      (fun i => hbound i.succ) hδ hδsmall hd'
    refine ⟨q₁*q₀, Nat.mul_pos hq₁ hq₀, ?_, ?_⟩
    · calc
        q₁*q₀ ≤ C*(8*B) := Nat.mul_le_mul hq₁C hq₀B
        _ = 8*B*C := by ring
        _ ≤ K := h8C
    · have hP : 0 < ∏ i : Fin e, (N i.succ : ℝ) :=
        Finset.prod_pos (fun i _ => hNp i.succ)
      have herror := dense_product_error_composition (hNp 0) hP hcoef hε
      have hresult := nearInteger_mono hnear herror
      simpa only [Nat.cast_mul, Fin.prod_univ_succ, mul_assoc] using hresult

end Erdos3

end

end OAI
