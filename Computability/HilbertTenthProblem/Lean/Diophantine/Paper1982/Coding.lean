import Diophantine.Paper1982.Digits
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Jones 1982, §3–§4: the coding of a polynomial and of its solutions as digits

The polynomial `P(z₀, …, z_ν)` of degree `≤ δ` is encoded (3.5) by the integers
`P_{i₀,…,i_ν}` with `δ! P = Σ* c_i P_i z^i`, where `c_i` is the multinomial coefficient
(3.4) and `Σ*` runs over `i₀ + ⋯ + i_ν ≤ δ`; the index of the r.e. set is the triple
`⟨z, u, y⟩` of (4.1),
`u = Σ_{i=1}^ν (2z)^((δ+1)^i)`, `y = Σ* (z + P_i)(2z)^(L − i₀ − i₁(δ+1) − ⋯ − i_ν(δ+1)^ν)`
with `L = (δ+1)^(ν+1)`.  A solution `z₀ = x, z₁, …, z_ν < b` is encoded as the digits of the
code `c = 1 + Σ_i z_i B^((δ+1)^i)` in base `B`, and (3.10), (M5): the coefficient of
`B^L` in the "polynomial in `B`" `−c^δ D₀`, `D₀ = zλ − e` (U11), is `δ! P(z₀, …, z_ν)`,
while all its coefficients are `< z (ν+2)^δ b^δ` in absolute value.

Here the exponent vectors are the slack-extended `k : Fin (ν+2) → ℕ` with `Σ k = δ`
(`k 0 = δ − Σ i`, `k (j+1) = i_j`), the set `star ν δ`; the polynomial in `B` is an honest
polynomial in `ℤ[X]` (`cpoly`, `epoly`, `lampoly`, `D0poly`, `Hpoly`), and the multinomial
theorem is Mathlib's `Finset.sum_pow_eq_sum_piAntidiag`.  `P_k = (Π_j k_j!) · coeff_i P`
satisfies `c_k P_k = δ! coeff_i P` by `Nat.multinomial_spec`.
-/

namespace Jones1982

open Polynomial Finset

section Coding

variable (ν δ : ℕ)

/-- The index set `*` of (3.3): slack-extended exponent vectors with `Σ k = δ`. -/
def star : Finset (Fin (ν + 2) → ℕ) := (univ : Finset (Fin (ν + 2))).piAntidiag δ

theorem mem_star {k : Fin (ν + 2) → ℕ} : k ∈ star ν δ ↔ ∑ j, k j = δ := by
  simp [star, Finset.mem_piAntidiag]

/-- `e(k) = Σ_j k_{j+1} (δ+1)^j`, the exponent of `B` attached to the monomial `z^k`. -/
def expo (k : Fin (ν + 2) → ℕ) : ℕ := ∑ j : Fin (ν + 1), k j.succ * (δ + 1) ^ (j : ℕ)

/-- `L = (δ+1)^(ν+1)`. -/
abbrev Lexp : ℕ := (δ + 1) ^ (ν + 1)

theorem star_le {k : Fin (ν + 2) → ℕ} (hk : k ∈ star ν δ) (j : Fin (ν + 2)) : k j ≤ δ := by
  rw [mem_star] at hk
  have := Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  omega

theorem expo_lt {k : Fin (ν + 2) → ℕ} (hk : k ∈ star ν δ) : expo ν δ k < Lexp ν δ := by
  have h1 : expo ν δ k ≤ (∑ j ∈ range (ν + 1), (δ + 1) ^ j) * δ := by
    calc expo ν δ k ≤ ∑ j : Fin (ν + 1), δ * (δ + 1) ^ (j : ℕ) :=
          Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (star_le ν δ hk j.succ)
      _ = ∑ j ∈ range (ν + 1), δ * (δ + 1) ^ j :=
          Fin.sum_univ_eq_sum_range (fun j => δ * (δ + 1) ^ j) (ν + 1)
      _ = (∑ j ∈ range (ν + 1), (δ + 1) ^ j) * δ := by rw [Finset.sum_mul]; simp [mul_comm]
  have h2 := geom_sum_mul_add (δ : ℕ) (ν + 1)
  unfold Lexp; omega

/-- `ofDigits b (ofFn f) = Σ_j f j b^j`. -/
theorem ofDigits_ofFn (b : ℕ) : ∀ {n : ℕ} (f : Fin n → ℕ),
    Nat.ofDigits b (List.ofFn f) = ∑ j : Fin n, f j * b ^ (j : ℕ)
  | 0, f => by simp [Nat.ofDigits]
  | n + 1, f => by
    rw [List.ofFn_succ, Nat.ofDigits_cons, ofDigits_ofFn b (fun i => f i.succ), Fin.sum_univ_succ,
      Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

theorem expo_eq_ofDigits (k : Fin (ν + 2) → ℕ) :
    expo ν δ k = Nat.ofDigits (δ + 1) (List.ofFn fun j : Fin (ν + 1) => k j.succ) := by
  rw [ofDigits_ofFn]; rfl

/-- `e` is injective on `*` (base-`(δ+1)` digits). -/
theorem expo_injOn : Set.InjOn (expo ν δ) (star ν δ) := by
  intro k hk k' hk' h
  have hk := Finset.mem_coe.1 hk
  have hk' := Finset.mem_coe.1 hk'
  rcases Nat.eq_zero_or_pos δ with hδ | hδ
  · subst hδ
    funext j
    have h1 := star_le ν 0 hk j
    have h2 := star_le ν 0 hk' j
    omega
  rw [expo_eq_ofDigits, expo_eq_ofDigits] at h
  have hlt : ∀ (k : Fin (ν + 2) → ℕ), k ∈ star ν δ →
      ∀ x ∈ (List.ofFn fun j : Fin (ν + 1) => k j.succ), x < δ + 1 := by
    intro k hk x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨j, rfl⟩ := hx
    have := star_le ν δ hk j.succ
    omega
  have htail := Nat.ofDigits_inj_of_len_eq (b := δ + 1) (by omega) (by simp) (hlt k hk)
    (hlt k' hk') h
  have htail' : ∀ j : Fin (ν + 1), k j.succ = k' j.succ := fun j =>
    congrFun (List.ofFn_injective htail) j
  funext j
  refine Fin.cases ?_ (fun j => htail' j) j
  rw [mem_star, Fin.sum_univ_succ] at hk hk'
  have : ∑ j : Fin (ν + 1), k j.succ = ∑ j : Fin (ν + 1), k' j.succ :=
    Finset.sum_congr rfl fun j _ => htail' j
  omega

/-! ### The polynomials -/

/-- The terms of the code polynomial: `1` and `z_j X^((δ+1)^j)`. -/
noncomputable def cterm (z : Fin (ν + 1) → ℕ) : Fin (ν + 2) → ℤ[X] :=
  Fin.cons (α := fun _ => ℤ[X]) 1 fun j : Fin (ν + 1) => C (z j : ℤ) * X ^ ((δ + 1) ^ (j : ℕ))

/-- The code polynomial `1 + Σ_j z_j X^((δ+1)^j)` (with `z 0 = x`). -/
noncomputable def cpoly (z : Fin (ν + 1) → ℕ) : ℤ[X] := ∑ j : Fin (ν + 2), cterm ν δ z j

theorem cterm_zero (z : Fin (ν + 1) → ℕ) : cterm ν δ z 0 = 1 := rfl

theorem cterm_succ (z : Fin (ν + 1) → ℕ) (j : Fin (ν + 1)) :
    cterm ν δ z j.succ = C (z j : ℤ) * X ^ ((δ + 1) ^ (j : ℕ)) := rfl

theorem cpoly_eq (z : Fin (ν + 1) → ℕ) :
    cpoly ν δ z = 1 + ∑ j : Fin (ν + 1), C (z j : ℤ) * X ^ ((δ + 1) ^ (j : ℕ)) := by
  simp only [cpoly, Fin.sum_univ_succ, cterm_zero, cterm_succ]

/-- The multinomial coefficient `c_k`. -/
def mult (k : Fin (ν + 2) → ℕ) : ℕ := Nat.multinomial univ k

/-- `z^k = Π_j z_j^(k (j+1))`. -/
def zpow (z : Fin (ν + 1) → ℕ) (k : Fin (ν + 2) → ℕ) : ℤ := ∏ j : Fin (ν + 1), (z j : ℤ) ^ k j.succ

theorem zpow_nonneg (z : Fin (ν + 1) → ℕ) (k : Fin (ν + 2) → ℕ) : 0 ≤ zpow ν z k :=
  Finset.prod_nonneg fun j _ => pow_nonneg (by positivity) _

theorem prod_C_mul_X_pow {ι : Type*} (s : Finset ι) (a : ι → ℤ) (n : ι → ℕ) :
    ∏ j ∈ s, (C (a j) * X ^ n j) = C (∏ j ∈ s, a j) * X ^ (∑ j ∈ s, n j) := by
  rw [Finset.prod_mul_distrib, map_prod, Finset.prod_pow_eq_pow_sum]

/-- The multinomial expansion (3.10) of `c^δ`. -/
theorem cpoly_pow (z : Fin (ν + 1) → ℕ) :
    cpoly ν δ z ^ δ = ∑ k ∈ star ν δ, C ((mult ν k : ℤ) * zpow ν z k) * X ^ expo ν δ k := by
  unfold cpoly star
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fin.prod_univ_succ, cterm_zero]
  simp only [cterm_succ, one_pow, one_mul]
  have h : ∀ j : Fin (ν + 1), (C (z j : ℤ) * X ^ ((δ + 1) ^ (j : ℕ))) ^ k j.succ =
      C ((z j : ℤ) ^ k j.succ) * X ^ (k j.succ * (δ + 1) ^ (j : ℕ)) := by
    intro j; rw [mul_pow, ← C_pow, ← pow_mul, mul_comm ((δ + 1) ^ (j : ℕ)) (k j.succ)]
  simp_rw [h]
  rw [prod_C_mul_X_pow, ← C_eq_natCast, ← mul_assoc, ← C_mul]
  rfl

theorem coeff_cpoly_pow (z : Fin (ν + 1) → ℕ) (a : ℕ) :
    (cpoly ν δ z ^ δ).coeff a =
      ∑ k ∈ (star ν δ).filter (fun k => expo ν δ k = a), (mult ν k : ℤ) * zpow ν z k := by
  rw [cpoly_pow, finset_sum_coeff, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_C_mul_X_pow]
  by_cases h : expo ν δ k = a
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]

theorem coeff_cpoly_pow_nonneg (z : Fin (ν + 1) → ℕ) (a : ℕ) :
    0 ≤ (cpoly ν δ z ^ δ).coeff a := by
  rw [coeff_cpoly_pow]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (zpow_nonneg ν z k)

/-- The sum of the coefficients of `c^δ` is `(1 + Σ_j z_j)^δ`. -/
theorem sum_mult_zpow (z : Fin (ν + 1) → ℕ) :
    ∑ k ∈ star ν δ, (mult ν k : ℤ) * zpow ν z k = (1 + ∑ j, (z j : ℤ)) ^ δ := by
  have h1 : (cpoly ν δ z ^ δ).eval 1 = ∑ k ∈ star ν δ, (mult ν k : ℤ) * zpow ν z k := by
    rw [cpoly_pow, eval_finset_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp
  have h2 : (cpoly ν δ z ^ δ).eval 1 = (1 + ∑ j, (z j : ℤ)) ^ δ := by
    rw [eval_pow, cpoly_eq, eval_add, eval_one, eval_finset_sum]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    simp
  rw [← h1, h2]

/-- The coefficients of `c^δ` below `N ≥ L` add up to `(1 + Σ_j z_j)^δ`. -/
theorem sum_coeff_cpoly_pow (z : Fin (ν + 1) → ℕ) {N : ℕ} (hN : Lexp ν δ ≤ N) :
    ∑ a ∈ range N, (cpoly ν δ z ^ δ).coeff a = (1 + ∑ j, (z j : ℤ)) ^ δ := by
  rw [← sum_mult_zpow]
  simp_rw [coeff_cpoly_pow]
  exact Finset.sum_fiberwise_of_maps_to
    (fun k hk => Finset.mem_range.2 (lt_of_lt_of_le (expo_lt ν δ hk) hN)) _

/-- `P_k = (Π_j k_j!) · coeff_i(P)`, so that `c_k P_k = δ! coeff_i(P)`. -/
noncomputable def Pcoef (P : MvPolynomial (Fin (ν + 1)) ℤ) (k : Fin (ν + 2) → ℕ) : ℤ :=
  ((∏ j, (k j).factorial : ℕ) : ℤ) *
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm fun j => k j.succ) P

theorem mult_mul_Pcoef (P : MvPolynomial (Fin (ν + 1)) ℤ) {k : Fin (ν + 2) → ℕ}
    (hk : k ∈ star ν δ) :
    (mult ν k : ℤ) * Pcoef ν P k =
      (δ.factorial : ℤ) * MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm fun j => k j.succ) P := by
  unfold Pcoef mult
  rw [← mul_assoc]
  congr 1
  have := Nat.multinomial_spec (univ : Finset (Fin (ν + 2))) k
  rw [(mem_star ν δ).1 hk] at this
  rw [mul_comm]
  exact_mod_cast this

/-- `Σ* c_k P_k z^k = δ! P(z)` for `P` of total degree `≤ δ`. -/
theorem sum_mult_Pcoef (P : MvPolynomial (Fin (ν + 1)) ℤ) (hP : P.totalDegree ≤ δ)
    (z : Fin (ν + 1) → ℕ) :
    ∑ k ∈ star ν δ, (mult ν k : ℤ) * zpow ν z k * Pcoef ν P k =
      (δ.factorial : ℤ) * MvPolynomial.eval (fun j => (z j : ℤ)) P := by
  rw [MvPolynomial.eval_eq']
  -- reindex the support of `P` by `*`
  have hcong : ∀ k ∈ star ν δ, (mult ν k : ℤ) * zpow ν z k * Pcoef ν P k =
      (δ.factorial : ℤ) * (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm fun j => k j.succ) P *
        zpow ν z k) := by
    intro k hk
    rw [mul_comm ((mult ν k : ℤ)) (zpow ν z k), mul_assoc, mult_mul_Pcoef ν δ P hk]
    ring
  rw [Finset.sum_congr rfl hcong, ← Finset.mul_sum]
  congr 1
  -- the map `k ↦ tail k` is a bijection from `{k ∈ * | coeff ≠ 0}` onto the support
  symm
  obtain ⟨ext, hext⟩ : ∃ ext : (Fin (ν + 1) →₀ ℕ) → (Fin (ν + 2) → ℕ),
      ext = fun d => Fin.cons (α := fun _ => ℕ) (δ - ∑ j, d j) (fun j => d j) := ⟨_, rfl⟩
  have hext0 : ∀ d, ext d 0 = δ - ∑ j, d j := fun d => by rw [hext]; rfl
  have hexts : ∀ d (j : Fin (ν + 1)), ext d j.succ = d j := fun d j => by rw [hext]; rfl
  have htail : ∀ d, (Finsupp.equivFunOnFinite.symm fun j => ext d j.succ) = d := by
    intro d; ext j; simp [hexts]
  have hfg : ∀ d : Fin (ν + 1) →₀ ℕ,
      MvPolynomial.coeff d P * ∏ i, (z i : ℤ) ^ d i =
      MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm fun j => ext d j.succ) P *
        zpow ν z (ext d) := by
    intro d
    rw [htail]
    unfold zpow
    simp only [hexts]
  refine Finset.sum_bij_ne_zero (s := P.support) (t := star ν δ)
    (f := fun d => MvPolynomial.coeff d P * ∏ i, (z i : ℤ) ^ d i)
    (g := fun k => MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm fun j => k j.succ) P *
      zpow ν z k) (fun d _ _ => ext d) ?_ ?_ ?_ ?_
  · intro d hd _
    rw [mem_star, Fin.sum_univ_succ, hext0]
    simp only [hexts]
    have h1 : ∑ j, d j ≤ δ := by
      have := MvPolynomial.le_totalDegree hd
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
      omega
    omega
  · intro d₁ _ _ d₂ _ _ h
    exact Finsupp.ext fun j => by rw [← hexts d₁ j, ← hexts d₂ j, h]
  · intro k hk hne
    have hk0 : ext (Finsupp.equivFunOnFinite.symm fun j => k j.succ) = k := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · rw [hext0]
        rw [mem_star, Fin.sum_univ_succ] at hk
        have : ∑ j : Fin (ν + 1), (Finsupp.equivFunOnFinite.symm fun j => k j.succ) j =
            ∑ j : Fin (ν + 1), k j.succ := Finset.sum_congr rfl fun j _ => rfl
        rw [this]; omega
      · rw [hexts]; rfl
    refine ⟨Finsupp.equivFunOnFinite.symm fun j => k j.succ, ?_, ?_, hk0⟩
    · rw [MvPolynomial.mem_support_iff]
      intro h0
      apply hne
      simp [h0]
    · rw [hfg, hk0]; exact hne
  · intro d _ _
    exact hfg d

/-- The "digit polynomial" of `y`: `Σ* (z + P_k) X^(L − e(k))`, so that `y = epoly(2z)` and
`e = epoly(B)`. -/
noncomputable def epoly (P : MvPolynomial (Fin (ν + 1)) ℤ) (z : ℕ) : ℤ[X] :=
  ∑ k ∈ star ν δ, C ((z : ℤ) + Pcoef ν P k) * X ^ (Lexp ν δ - expo ν δ k)

/-- The "digit polynomial" of `u`: `Σ_{i=1}^ν X^((δ+1)^i)`, so that `u = lpoly(2z)`,
`l = lpoly(B)`. -/
noncomputable def lpoly : ℤ[X] := ∑ i ∈ Finset.Icc 1 ν, X ^ ((δ + 1) ^ i)

/-- `λ = Σ_{i<4L} X^i` (4.3). -/
noncomputable def lampoly : ℤ[X] := ∑ i ∈ range (4 * Lexp ν δ), X ^ i

/-- `D₀ = zλ − e` (U11). -/
noncomputable def D0poly (P : MvPolynomial (Fin (ν + 1)) ℤ) (z : ℕ) : ℤ[X] :=
  C (z : ℤ) * lampoly ν δ - epoly ν δ P z

/-- `H = −c^δ D₀`, the polynomial in `B` whose coefficient of `B^L` is `δ! P(z₀, …, z_ν)`. -/
noncomputable def Hpoly (P : MvPolynomial (Fin (ν + 1)) ℤ) (z : ℕ) (zs : Fin (ν + 1) → ℕ) :
    ℤ[X] :=
  -(cpoly ν δ zs ^ δ * D0poly ν δ P z)

theorem coeff_epoly (P : MvPolynomial (Fin (ν + 1)) ℤ) (z : ℕ) (b : ℕ) :
    (epoly ν δ P z).coeff b =
      ∑ k ∈ (star ν δ).filter (fun k => Lexp ν δ - expo ν δ k = b), ((z : ℤ) + Pcoef ν P k) := by
  unfold epoly
  rw [finset_sum_coeff, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_C_mul_X_pow]
  by_cases h : Lexp ν δ - expo ν δ k = b
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]

theorem coeff_epoly_of_mem (P : MvPolynomial (Fin (ν + 1)) ℤ) (z : ℕ) {k : Fin (ν + 2) → ℕ}
    (hk : k ∈ star ν δ) :
    (epoly ν δ P z).coeff (Lexp ν δ - expo ν δ k) = (z : ℤ) + Pcoef ν P k := by
  rw [coeff_epoly]
  rw [Finset.sum_eq_single k]
  · intro k' hk' hne
    exfalso
    rw [Finset.mem_filter] at hk'
    apply hne
    apply expo_injOn ν δ hk'.1 hk
    have h1 := expo_lt ν δ hk'.1
    have h2 := expo_lt ν δ hk
    omega
  · intro h; exfalso; apply h; rw [Finset.mem_filter]; exact ⟨hk, rfl⟩

theorem coeff_epoly_of_not (P : MvPolynomial (Fin (ν + 1)) ℤ) (z : ℕ) {b : ℕ}
    (hb : ∀ k ∈ star ν δ, Lexp ν δ - expo ν δ k ≠ b) : (epoly ν δ P z).coeff b = 0 := by
  rw [coeff_epoly]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_filter] at hk
  exact absurd hk.2 (hb k hk.1)

theorem coeff_lampoly (b : ℕ) : (lampoly ν δ).coeff b = if b < 4 * Lexp ν δ then 1 else 0 := by
  unfold lampoly
  rw [finset_sum_coeff]
  simp only [coeff_X_pow]
  rw [Finset.sum_ite_eq]
  simp

theorem coeff_D0_of_mem (P : MvPolynomial (Fin (ν + 1)) ℤ) (z : ℕ) {k : Fin (ν + 2) → ℕ}
    (hk : k ∈ star ν δ) :
    (D0poly ν δ P z).coeff (Lexp ν δ - expo ν δ k) = -Pcoef ν P k := by
  unfold D0poly
  rw [coeff_sub, coeff_C_mul, coeff_lampoly, coeff_epoly_of_mem ν δ P z hk]
  have : Lexp ν δ - expo ν δ k < 4 * Lexp ν δ := by
    have h1 := expo_lt ν δ hk
    have h2 : 0 < Lexp ν δ := by positivity
    omega
  rw [if_pos this]; ring

theorem abs_coeff_D0_le (P : MvPolynomial (Fin (ν + 1)) ℤ) {z : ℕ}
    (hP : ∀ k ∈ star ν δ, |Pcoef ν P k| ≤ z) (b : ℕ) : |(D0poly ν δ P z).coeff b| ≤ z := by
  by_cases h : ∃ k ∈ star ν δ, Lexp ν δ - expo ν δ k = b
  · obtain ⟨k, hk, rfl⟩ := h
    rw [coeff_D0_of_mem ν δ P z hk, abs_neg]
    exact hP k hk
  · push Not at h
    unfold D0poly
    rw [coeff_sub, coeff_C_mul, coeff_lampoly, coeff_epoly_of_not ν δ P z h]
    split_ifs <;> simp

/-- (3.10)/(M5): the coefficient of `B^L` in `−c^δ D₀` is `δ! P(z₀, …, z_ν)`. -/
theorem coeff_Hpoly_Lexp (P : MvPolynomial (Fin (ν + 1)) ℤ) (hP : P.totalDegree ≤ δ) (z : ℕ)
    (zs : Fin (ν + 1) → ℕ) :
    (Hpoly ν δ P z zs).coeff (Lexp ν δ) =
      (δ.factorial : ℤ) * MvPolynomial.eval (fun j => (zs j : ℤ)) P := by
  unfold Hpoly
  rw [coeff_neg, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have h1 : ∀ a ∈ range (Lexp ν δ + 1),
      (cpoly ν δ zs ^ δ).coeff a * (D0poly ν δ P z).coeff (Lexp ν δ - a) =
      ∑ k ∈ (star ν δ).filter (fun k => expo ν δ k = a),
        (mult ν k : ℤ) * zpow ν zs k * (D0poly ν δ P z).coeff (Lexp ν δ - expo ν δ k) := by
    intro a _
    rw [coeff_cpoly_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [(Finset.mem_filter.1 hk).2]
  rw [Finset.sum_congr rfl h1]
  rw [Finset.sum_fiberwise_of_maps_to (s := star ν δ) (t := range (Lexp ν δ + 1)) (g := expo ν δ)
    (fun k hk => Finset.mem_range.2 (by have := expo_lt ν δ hk; omega))]
  rw [← sum_mult_Pcoef ν δ P hP zs, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [coeff_D0_of_mem ν δ P z hk]
  ring

/-- The coefficients of `−c^δ D₀` are bounded by `z (1 + Σ_j z_j)^δ`. -/
theorem abs_coeff_Hpoly_le (P : MvPolynomial (Fin (ν + 1)) ℤ) {z : ℕ}
    (hP : ∀ k ∈ star ν δ, |Pcoef ν P k| ≤ z) (zs : Fin (ν + 1) → ℕ) (j : ℕ) :
    |(Hpoly ν δ P z zs).coeff j| ≤ z * (1 + ∑ i, (zs i : ℤ)) ^ δ := by
  unfold Hpoly
  rw [coeff_neg, abs_neg, coeff_mul]
  calc |∑ x ∈ Finset.HasAntidiagonal.antidiagonal j,
          (cpoly ν δ zs ^ δ).coeff x.1 * (D0poly ν δ P z).coeff x.2|
      ≤ ∑ x ∈ Finset.HasAntidiagonal.antidiagonal j,
          |(cpoly ν δ zs ^ δ).coeff x.1 * (D0poly ν δ P z).coeff x.2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ Finset.HasAntidiagonal.antidiagonal j, (cpoly ν δ zs ^ δ).coeff x.1 * z := by
        apply Finset.sum_le_sum
        intro x _
        rw [abs_mul, abs_of_nonneg (coeff_cpoly_pow_nonneg ν δ zs _)]
        exact mul_le_mul_of_nonneg_left (abs_coeff_D0_le ν δ P hP _)
          (coeff_cpoly_pow_nonneg ν δ zs _)
    _ = (∑ a ∈ range (j + 1), (cpoly ν δ zs ^ δ).coeff a) * z := by
        rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul]
    _ ≤ (∑ a ∈ range (j + 1 + Lexp ν δ), (cpoly ν δ zs ^ δ).coeff a) * z := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        intro a _ _
        exact coeff_cpoly_pow_nonneg ν δ zs a
    _ = z * (1 + ∑ i, (zs i : ℤ)) ^ δ := by
        rw [sum_coeff_cpoly_pow ν δ zs (by omega), mul_comm]

/-! ### Degrees -/

theorem natDegree_cpoly_le (zs : Fin (ν + 1) → ℕ) : (cpoly ν δ zs).natDegree ≤ (δ + 1) ^ ν := by
  rw [cpoly_eq]
  refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
  apply natDegree_sum_le_of_forall_le
  intro j _
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  exact Nat.pow_le_pow_right (by omega) (by omega)

theorem natDegree_epoly_le (P : MvPolynomial (Fin (ν + 1)) ℤ) (z : ℕ) :
    (epoly ν δ P z).natDegree ≤ Lexp ν δ := by
  unfold epoly
  apply natDegree_sum_le_of_forall_le
  intro k _
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le _ _)

theorem natDegree_lampoly_le : (lampoly ν δ).natDegree ≤ 4 * Lexp ν δ := by
  unfold lampoly
  apply natDegree_sum_le_of_forall_le
  intro i hi
  rw [Finset.mem_range] at hi
  exact (natDegree_X_pow_le _).trans hi.le

theorem natDegree_D0_le (P : MvPolynomial (Fin (ν + 1)) ℤ) (z : ℕ) :
    (D0poly ν δ P z).natDegree ≤ 4 * Lexp ν δ := by
  unfold D0poly
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact (natDegree_C_mul_le _ _).trans (natDegree_lampoly_le ν δ)
  · exact (natDegree_epoly_le ν δ P z).trans (by omega)

theorem natDegree_Hpoly_lt (P : MvPolynomial (Fin (ν + 1)) ℤ) (z : ℕ) (zs : Fin (ν + 1) → ℕ) :
    (Hpoly ν δ P z zs).natDegree < 8 * Lexp ν δ := by
  unfold Hpoly
  rw [natDegree_neg]
  have h1 : (cpoly ν δ zs ^ δ).natDegree ≤ δ * (δ + 1) ^ ν :=
    (natDegree_pow_le).trans (Nat.mul_le_mul_left _ (natDegree_cpoly_le ν δ zs))
  have h2 : δ * (δ + 1) ^ ν < 4 * Lexp ν δ := by
    unfold Lexp
    rw [pow_succ]
    have : 0 < (δ + 1) ^ ν := by positivity
    nlinarith
  have := natDegree_mul_le (p := cpoly ν δ zs ^ δ) (q := D0poly ν δ P z)
  have := natDegree_D0_le ν δ P z
  omega

/-! ### Evaluations -/

theorem eval_cpoly (zs : Fin (ν + 1) → ℕ) (B : ℤ) :
    (cpoly ν δ zs).eval B = 1 + ∑ j : Fin (ν + 1), (zs j : ℤ) * B ^ ((δ + 1) ^ (j : ℕ)) := by
  rw [cpoly_eq, eval_add, eval_one, eval_finset_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

theorem eval_epoly (P : MvPolynomial (Fin (ν + 1)) ℤ) (z : ℕ) (B : ℤ) :
    (epoly ν δ P z).eval B = ∑ k ∈ star ν δ, ((z : ℤ) + Pcoef ν P k) * B ^ (Lexp ν δ - expo ν δ k) := by
  unfold epoly
  rw [eval_finset_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp

theorem eval_lpoly (B : ℤ) : (lpoly ν δ).eval B = ∑ i ∈ Finset.Icc 1 ν, B ^ ((δ + 1) ^ i) := by
  unfold lpoly
  rw [eval_finset_sum]
  simp

theorem eval_lampoly (B : ℤ) : (lampoly ν δ).eval B = ∑ i ∈ range (4 * Lexp ν δ), B ^ i := by
  unfold lampoly
  rw [eval_finset_sum]
  simp

theorem eval_Hpoly (P : MvPolynomial (Fin (ν + 1)) ℤ) (z : ℕ) (zs : Fin (ν + 1) → ℕ) (B : ℤ) :
    (Hpoly ν δ P z zs).eval B =
      -((cpoly ν δ zs).eval B ^ δ * ((z : ℤ) * (lampoly ν δ).eval B - (epoly ν δ P z).eval B)) := by
  unfold Hpoly D0poly
  rw [eval_neg, eval_mul, eval_pow, eval_sub, eval_mul, eval_C]

/-! ### Digit lists -/

/-- The list of the first `n` coefficients of a polynomial (as natural numbers). -/
noncomputable def coeffList (p : ℤ[X]) (n : ℕ) : List ℕ :=
  (List.range n).map fun i => (p.coeff i).toNat

theorem coeffList_length (p : ℤ[X]) (n : ℕ) : (coeffList p n).length = n := by
  simp [coeffList]

theorem coeffList_getD (p : ℤ[X]) (n i : ℕ) (hi : i < n) :
    (coeffList p n).getD i 0 = (p.coeff i).toNat := by
  unfold coeffList
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

theorem mem_coeffList {p : ℤ[X]} {n x : ℕ} (hx : x ∈ coeffList p n) :
    ∃ i < n, x = (p.coeff i).toNat := by
  unfold coeffList at hx
  rw [List.mem_map] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact ⟨i, List.mem_range.1 hi, rfl⟩

/-- `ofDigits b (coeffList p n) = Σ_{i<n} coeff i b^i` when the coefficients are nonnegative. -/
theorem ofDigits_coeffList (p : ℤ[X]) (hp : ∀ i, 0 ≤ p.coeff i) (b : ℕ) :
    ∀ n : ℕ, ((Nat.ofDigits b (coeffList p n) : ℕ) : ℤ) = ∑ i ∈ range n, p.coeff i * (b : ℤ) ^ i
  | 0 => by simp [coeffList, Nat.ofDigits]
  | n + 1 => by
    rw [Finset.sum_range_succ, ← ofDigits_coeffList p hp b n]
    unfold coeffList
    rw [List.range_succ, List.map_append, Nat.ofDigits_append]
    simp only [List.map_cons, List.map_nil, List.length_map, List.length_range,
      Nat.ofDigits_singleton]
    push_cast
    rw [Int.toNat_of_nonneg (hp n)]
    ring

/-- `ofDigits b (coeffList p n) = p(b)` when the coefficients are nonnegative and
`natDegree p < n`. -/
theorem ofDigits_coeffList_eq_eval (p : ℤ[X]) (hp : ∀ i, 0 ≤ p.coeff i) (b : ℕ) {n : ℕ}
    (hn : p.natDegree < n) : ((Nat.ofDigits b (coeffList p n) : ℕ) : ℤ) = p.eval (b : ℤ) := by
  rw [ofDigits_coeffList p hp b n, eval_eq_sum_range' hn]

end Coding

end Jones1982
