import GowersSzemeredi.Proofs18GenericExponents
import GowersSzemeredi.Proofs18ExponentialCalculus

/-! The modulus threshold of the single-piece step in any dimension is single
exponential in a power of `X = 2/α` (Notes L.7a, F3c).

`GenParams.Tloc` is a maximum of Lemma 15.6's threshold, the nested-width
thresholds, the requirement on `m` (the recurrence threshold and the Bohr
radius), and roots `c^(1/e)` of constants at the polynomially small
exponents of `Proofs18GenericExponents`. Each is `≤ exp(X^(2^μ))`:
* `ex_root`: `c^(1/e) ≤ exp(X^(2^(max j m + 1)))` for `c ≤ 2^(2^j)`, `e⁻¹ ≤ X^(2^m)`;
* `genWThr_le_exp`, `genNestThr_le_exp`: the nested width thresholds;
* `familyRecThr_le_exp`: `(K(q+1))^(2p(q+1)^(2^(k+2)))`;
* `lemma156_gen_le`: Lemma 15.6's threshold in dimension `k ≥ 1`, at most
  `X^(2^(2^(k+4)+4k+13))`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-! ### The nested width thresholds -/

theorem genWThr_le_exp {X : Real} (hX : 2 ≤ X) {E : Real → Real} {k : Nat} {u : Real} {m : Nat}
    (hl0 : 0 < lwE E k u) (hli : (lwE E k u)⁻¹ ≤ X ^ (2 ^ m)) (hkm : k ≤ 2 ^ m) :
    genWThr E k u ≤ Real.exp (X ^ (2 ^ (m + 4))) := by
  unfold genWThr
  have h4 : 4 / lwE E k u ≤ X ^ (2 ^ (max 1 m + 1)) := by
    rw [div_eq_mul_inv]
    exact pw_mul' hX (by norm_num) (inv_pos.mpr hl0).le (four_le_pw_one hX) hli
  have h6 : (6 : Real) ^ (4 / lwE E k u) ≤ Real.exp (X ^ (2 ^ (max 2 (max 1 m + 1) + 1))) :=
    ex_rpow hX (by norm_num) (ex_of_pw (pw_const hX (by norm_num))) (by positivity) h4
  have h16 : (16 : Real) ^ k ≤ Real.exp (X ^ (2 ^ (m + 2))) := by
    refine ex_of_pw ?_
    have h16X : (16 : Real) ≤ X ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num) hX 4; norm_num at this; linarith
    refine (pow_le_pow_left₀ (by norm_num) h16X k).trans ?_
    rw [← pow_mul]
    exact pw_natpow hX (by rw [pow_add]; omega)
  have h := ex_mul' hX (by positivity) h16 h6
  exact ex_mono hX h (by omega)

theorem genNestExp_anti {E : Real → Real} {k : Nat} {C : Real → Real}
    (hE : ∀ s, 0 < s → s ≤ 1 → 0 < E s ∧ E s ≤ 1)
    (hC : ∀ u, 0 < u → u ≤ 1 → 0 < C u ∧ C u ≤ 1) {t : Real} (ht : 0 < t) (ht1 : t ≤ 1) :
    ∀ i r, i ≤ r → genNestExp E k C r t ≤ genNestExp E k C i t := by
  intro i r hir
  induction hir with
  | refl => exact le_rfl
  | step _ ih =>
    rename_i r _
    obtain ⟨n0, -, -, -⟩ := genNest_facts hE k hC r t ht ht1
    obtain ⟨c0, c1⟩ := nestC_pos_le (c := fun _ => C) (fun _ => hC) r t ht ht1
    obtain ⟨-, l1⟩ := lwE_pos_le hE k c0 c1
    show genNestExp E k C r t * lwE E k (nestC (fun _ => C) r t) ≤ _
    exact (mul_le_of_le_one_right n0.le l1).trans ih

theorem genNestThr_le_exp {X : Real} (hX : 2 ≤ X) {E : Real → Real} {k : Nat} {C : Real → Real}
    (hE : ∀ s, 0 < s → s ≤ 1 → 0 < E s ∧ E s ≤ 1)
    (hC : ∀ u, 0 < u → u ≤ 1 → 0 < C u ∧ C u ≤ 1) {t : Real} (ht : 0 < t) (ht1 : t ≤ 1)
    {A B : Nat} :
    ∀ r, (∀ i, i < r → genWThr E k (nestC (fun _ => C) i t) ≤ Real.exp (X ^ (2 ^ A))) →
      (genNestExp E k C r t)⁻¹ ≤ X ^ (2 ^ B) →
      genNestThr E k C r t ≤ Real.exp (X ^ (2 ^ (max A B + 1))) := by
  intro r
  induction r with
  | zero =>
    intro _ _
    show (1 : Real) ≤ _
    exact Real.one_le_exp (by positivity)
  | succ r ih =>
    intro hA hB
    obtain ⟨n0, -, -, -⟩ := genNest_facts hE k hC r t ht ht1
    have hanti := genNestExp_anti (k := k) hE hC ht ht1 r (r + 1) (Nat.le_succ r)
    obtain ⟨n0', -, -, -⟩ := genNest_facts hE k hC (r + 1) t ht ht1
    have hBr : (genNestExp E k C r t)⁻¹ ≤ X ^ (2 ^ B) := (inv_anti₀ n0' hanti).trans hB
    obtain ⟨c0, c1⟩ := nestC_pos_le (c := fun _ => C) (fun _ => hC) r t ht ht1
    have hW1 := one_le_genWThr hE k c0 c1
    show max (genNestThr E k C r t)
      (genWThr E k (nestC (fun _ => C) r t) ^ (1 / genNestExp E k C r t)) ≤ _
    refine max_le (ih (fun i hi => hA i (by omega)) hBr) ?_
    rw [one_div]
    exact ex_rpow hX hW1 (hA r (by omega)) (inv_pos.mpr n0).le hBr

/-! ### The recurrence threshold -/

/-! ### Lemma 15.6's threshold -/

namespace GenParams

variable {alpha : Real}

/-- The log-degree of the modulus threshold. -/
def threshDeg (k μD μ0 μK : Nat) : Nat := max (expDeg k μD μ0 μK + 4) (2 ^ (k + 6) + 5)

/-- The common hypotheses on the standard parameters. -/
structure StdHyp (V : Real) (D k K p μV μD μ0 μK : Nat) : Prop where
  hV : 1 ≤ V
  hVμ : V ≤ 2 ^ (2 ^ μV)
  hμ0 : max μV (fixDeg k) + 2 ≤ μ0
  hD : D ≤ 2 ^ μD
  hkD : k + 1 ≤ D
  hk0 : k ≤ 2 ^ μ0
  hK : 2 ≤ K
  hKμ : K ≤ 2 ^ (2 ^ μK)
  hp : 0 < p
  hpμ : p ≤ 2 ^ (2 ^ μK)

/-- **The requirement on `m`.** -/
theorem MReq_le_exp {V : Real} {D k K p μV μD μ0 μK : Nat} (H : StdHyp V D k K p μV μD μ0 μK)
    (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    1 ≤ (std V D k K p μ0).MReq alpha ∧
      (std V D k K p μ0).MReq alpha ≤
        Real.exp ((2 / alpha) ^ (2 ^ max (expDeg k μD μ0 μK + 3) (2 ^ (k + 6) + 4))) := by
  obtain ⟨hV, hVμ, hμ0, hD, hkD, hk0, hK, hKμ, hp, hpμ⟩ := H
  have hX := two_div_ge_two ha ha2
  have hX1 : (1 : Real) ≤ 2 / alpha := by linarith
  set E := expDeg k μD μ0 μK with hEdef
  set Z := 2 ^ (k + 6) + 1 with hZdef
  have hZ2 : 2 ≤ Z := by rw [hZdef]; have := Nat.one_le_two_pow (n := k + 6); omega
  have hρE : rhoDeg k μD μ0 + μD + k + 7 ≤ E := by
    rw [hEdef]; unfold expDeg; exact (le_max_left _ _).trans (le_max_right _ _)
  have hKE : μK + 2 ≤ E := by
    rw [hEdef]; unfold expDeg; exact (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨-, hQM, hBx⟩ := spectrum_exps_inv_le (K := K) ha ha2 hV hVμ hμ0 hD hkD hk0 hpμ
  -- the recurrence threshold
  have hthr := familyRecThr_le_exp (k := k) hX (by omega) hKμ hpμ hQM
  have hthr' : (familyRecThr k K p ((std V D k K p μ0).QM alpha) : Real) ≤
      Real.exp ((2 / alpha) ^ (2 ^ (E + 3))) := ex_mono hX hthr (by omega)
  have hthr1 : (1 : Real) ≤ (familyRecThr k K p ((std V D k K p μ0).QM alpha) : Real) :=
    Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr
      (familyRecThr_pos (k := k) (p := p) (by omega) _).ne')
  -- the Bohr radius and `ρ`
  obtain ⟨hz0, hzi⟩ := zeta_gen_bounds k ha ha2
  have hz1 : section16Zeta alpha (alpha / 2) k ≤ 1 / 2 :=
    (section16Zeta_pos_le_half k ha (by linarith) (half_pos ha) (by linarith)).2
  have hzeq : (std V D k K p μ0).Zeta alpha = section16Zeta alpha (alpha / 2) k := rfl
  obtain ⟨ht0, ht1, -⟩ := T2_gen_bounds k ha ha2
  have hC : ∀ u, 0 < u → u ≤ 1 →
      0 < (std V D k K p μ0).C alpha u ∧ (std V D k K p μ0).C alpha u ≤ 1 :=
    genC_pos_le hX1 _ _ _ _
  obtain ⟨hr0, hr1⟩ : 0 < (std V D k K p μ0).Rho1 alpha ∧ (std V D k K p μ0).Rho1 alpha ≤ 1 :=
    nestC_pos_le (c := fun _ => (std V D k K p μ0).C alpha) (fun _ => hC) _ _ ht0 ht1
  have hri := rho1_inv_le (V := V) (K := K) (p := p) ha ha2 hD hkD hk0
  have hρ1 : 1 ≤ rhoDeg k μD μ0 := by
    unfold rhoDeg; have := le_max_left (μD + μ0 + 2) (fixDeg k); omega
  obtain ⟨hR0, hR1, hRi⟩ := rho_step hX hr0 hr1 hri hρ1
  have hReq : (std V D k K p μ0).Rho alpha =
      (std V D k K p μ0).Rho1 alpha / 2 * ((std V D k K p μ0).Rho1 alpha / 2 / 2) := rfl
  rw [← hReq] at hR0 hR1 hRi
  have hBpos : 0 < (std V D k K p μ0).Bexp alpha := by
    have := familyRecExp_pos k p ((std V D k K p μ0).QM alpha) hp
    show 0 < familyRecExp k p _ / 2; positivity
  -- the three Bohr-radius terms
  set z := (std V D k K p μ0).Zeta alpha with hzdef
  set R := (std V D k K p μ0).Rho alpha with hRdef
  set B := (std V D k K p μ0).Bexp alpha with hBdef
  rw [← hzeq] at hz0 hzi hz1
  have h8 : (8 : Real) ≤ Real.exp ((2 / alpha) ^ (2 ^ 2)) := ex_of_pw (pw_const hX (by norm_num))
  have hzi' : z⁻¹ ≤ Real.exp ((2 / alpha) ^ (2 ^ Z)) := hzi
  have h8z : 8 / z ≤ Real.exp ((2 / alpha) ^ (2 ^ (Z + 1))) := by
    rw [div_eq_mul_inv]
    exact ex_mono hX (ex_mul' hX (inv_pos.mpr hz0).le h8 hzi') (by omega)
  have h16 : (16 : Real) ≤ Real.exp ((2 / alpha) ^ (2 ^ 2)) := ex_of_pw (pw_const hX (by norm_num))
  have h16z : 16 / z ≤ Real.exp ((2 / alpha) ^ (2 ^ (Z + 1))) := by
    rw [div_eq_mul_inv]
    exact ex_mono hX (ex_mul' hX (inv_pos.mpr hz0).le h16 hzi') (by omega)
  have hR3 : (R ^ 3)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDeg k μD μ0 + 2 + 2)) := by
    rw [← inv_pow]; exact pw_pow hX (inv_pos.mpr hR0).le hRi (by norm_num)
  have h4zr : 4 / (z * R ^ 3) ≤ Real.exp ((2 / alpha) ^ (2 ^ (max (Z + 1) (rhoDeg k μD μ0 + 4) + 1))) := by
    rw [div_eq_mul_inv, mul_inv, ← mul_assoc]
    have h4z : 4 * z⁻¹ ≤ Real.exp ((2 / alpha) ^ (2 ^ (Z + 1))) := by
      have h4 : (4 : Real) ≤ Real.exp ((2 / alpha) ^ (2 ^ 2)) := ex_of_pw (pw_const hX (by norm_num))
      exact ex_mono hX (ex_mul' hX (inv_pos.mpr hz0).le h4 hzi') (by omega)
    exact ex_mul' hX (inv_pos.mpr (pow_pos hR0 3)).le h4z (ex_of_pw hR3)
  have hz1' : 1 ≤ z⁻¹ := by rw [one_le_inv₀ hz0]; linarith
  have h8z1 : 1 ≤ 8 / z := by rw [le_div_iff₀ hz0]; linarith
  have h16z1 : 1 ≤ 16 / z := by rw [le_div_iff₀ hz0]; linarith
  have h4zr1 : 1 ≤ 4 / (z * R ^ 3) := by
    rw [le_div_iff₀ (by positivity)]
    have : R ^ 3 ≤ 1 := pow_le_one₀ hR0.le hR1
    have : z * R ^ 3 ≤ 1 / 2 * 1 := mul_le_mul hz1 this (by positivity) (by norm_num)
    linarith
  have hBe : 1 / B ≤ (2 / alpha) ^ (2 ^ E) := by rw [one_div]; exact hBx
  have hBe2 : 2 / B ≤ (2 / alpha) ^ (2 ^ (E + 1)) := by
    rw [div_eq_mul_inv]
    exact pw_mul hX (by norm_num) (inv_pos.mpr hBpos).le (hX.trans (pw_X hX _)) hBx
  have hT := max (E + 3) (2 ^ (k + 6) + 4)
  have e1 := ex_rpow hX h8z1 h8z (by positivity) hBe
  have e2 := ex_rpow hX h4zr1 h4zr (by positivity) hBe
  have e3 := ex_rpow hX h16z1 h16z (by positivity) hBe2
  have hρE' : rhoDeg k μD μ0 + 5 ≤ E := by omega
  refine ⟨hthr1.trans (le_max_left _ _), ?_⟩
  show max (familyRecThr k K p ((std V D k K p μ0).QM alpha) : Real)
    (max ((8 / z) ^ (1 / B)) (max ((4 / (z * R ^ 3)) ^ (1 / B)) ((16 / z) ^ (2 / B)))) ≤ _
  refine max_le (ex_mono hX hthr' (le_max_left _ _)) (max_le ?_ (max_le ?_ ?_))
  · exact ex_mono hX e1 (by rw [hZdef]; have := Nat.one_le_two_pow (n := k + 6); omega)
  · exact ex_mono hX e2 (by rw [hZdef]; have := Nat.one_le_two_pow (n := k + 6); omega)
  · exact ex_mono hX e3 (by rw [hZdef]; have := Nat.one_le_two_pow (n := k + 6); omega)

/-- **The modulus threshold of the step is single exponential.** -/
theorem Tloc_le_exp {V : Real} {D k K p μV μD μ0 μK : Nat} (H : StdHyp V D k K p μV μD μ0 μK)
    (hk : 1 ≤ k) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    (std V D k K p μ0).Tloc alpha ≤ Real.exp ((2 / alpha) ^ (2 ^ threshDeg k μD μ0 μK)) := by
  have H' := H
  obtain ⟨hV, hVμ, hμ0, hD, hkD, hk0, hK, hKμ, hp, hpμ⟩ := H'
  have hX := two_div_ge_two ha ha2
  have hX1 : (1 : Real) ≤ 2 / alpha := by linarith
  set E := expDeg k μD μ0 μK with hEdef
  set T := threshDeg k μD μ0 μK with hTdef
  have hET : E + 4 ≤ T := by rw [hTdef]; unfold threshDeg; exact le_max_left _ _
  have hZT : 2 ^ (k + 6) + 5 ≤ T := by rw [hTdef]; unfold threshDeg; exact le_max_right _ _
  have hρE : rhoDeg k μD μ0 + μD + k + 7 ≤ E := by
    rw [hEdef]; unfold expDeg; exact (le_max_left _ _).trans (le_max_right _ _)
  have hρE2 : rhoDeg k μD μ0 + 2 * μD + 9 ≤ E := by
    rw [hEdef]; unfold expDeg; exact le_max_left _ _
  have hρ2 : fixDeg k + 1 ≤ rhoDeg k μD μ0 := by
    unfold rhoDeg; have := le_max_right (μD + μ0 + 2) (fixDeg k); omega
  have hρ0 : μD + μ0 + 3 ≤ rhoDeg k μD μ0 := by
    unfold rhoDeg; have := le_max_left (μD + μ0 + 2) (fixDeg k); omega
  -- the exponents
  obtain ⟨hEl0, hEli⟩ := Eloc_inv_le (K := K) ha ha2 hV hVμ hμ0 hD hkD hk0 hp hpμ
  obtain ⟨hEm, -, -⟩ := spectrum_exps_inv_le (K := K) ha ha2 hV hVμ hμ0 hD hkD hk0 hpμ
  have hNE := nestExp_inv_le (K := K) (p := p) ha ha2 hV hVμ hμ0 hD hkD hk0
  obtain ⟨-, -, -, -, -, -, -, ⟨hEm0, -⟩, -, -, ⟨hN0, -, -⟩, -, -, hEw, hC⟩ :=
    (std V D k K p μ0).ranges hV hp ha ha2
  have hNE' : ((std V D k K p μ0).NestExp alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ E) :=
    pw_mono hX hNE (by omega)
  have hEm' : ((std V D k K p μ0).Em alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ E) := pw_mono hX hEm (by omega)
  have hMx : ((std V D k K p μ0).MExp alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (E + 2)) := by
    show ((std V D k K p μ0).NestExp alpha * ((std V D k K p μ0).Em alpha / 2))⁻¹ ≤ _
    rw [show ((std V D k K p μ0).NestExp alpha * ((std V D k K p μ0).Em alpha / 2))⁻¹ =
      2 * (((std V D k K p μ0).NestExp alpha)⁻¹ * ((std V D k K p μ0).Em alpha)⁻¹) by
        field_simp]
    have p1 := pw_mul hX (inv_pos.mpr hN0).le (inv_pos.mpr hEm0).le hNE' hEm'
    exact pw_mul hX (by norm_num) (by positivity) (hX.trans (pw_X hX _)) p1
  have hMx0 : 0 < (std V D k K p μ0).MExp alpha := by
    show 0 < (std V D k K p μ0).NestExp alpha * ((std V D k K p μ0).Em alpha / 2)
    positivity
  -- the nested width threshold
  obtain ⟨ht0, ht1, -⟩ := T2_gen_bounds k ha ha2
  have hb1 : 1 ≤ (std V D k K p μ0).b := by show 1 ≤ D + 1 + k; omega
  obtain ⟨hr0, -⟩ : 0 < (std V D k K p μ0).Rho1 alpha ∧ (std V D k K p μ0).Rho1 alpha ≤ 1 :=
    nestC_pos_le (c := fun _ => (std V D k K p μ0).C alpha) (fun _ => hC) _ _ ht0 ht1
  have hri := rho1_inv_le (V := V) (K := K) (p := p) ha ha2 hD hkD hk0
  have hlevW : ∀ i, i < 2 ^ k - 1 →
      genWThr ((std V D k K p μ0).Ew alpha) k
        (nestC (fun _ => (std V D k K p μ0).C alpha) i ((std V D k K p μ0).T2 alpha)) ≤
        Real.exp ((2 / alpha) ^ (2 ^ (rhoDeg k μD μ0 + μD + 3 + 4))) := by
    intro i hi
    obtain ⟨u0, u1⟩ := nestC_pos_le (c := fun _ => (std V D k K p μ0).C alpha) (fun _ => hC) i _
      ht0 ht1
    have hu := nestC_genC_anti (a := (std V D k K p μ0).a) hX1 hb1 ((std V D k K p μ0).baseC alpha)
      k ht0 ht1 i _ hi.le
    have hui := (inv_anti₀ hr0 hu).trans hri
    have hl := lw_level_inv_le ha ha2 hV hVμ hμ0 hD u0 u1 hui hρ2 (by omega)
    obtain ⟨hl0, -⟩ := lwE_pos_le hEw k u0 u1
    refine genWThr_le_exp hX hl0 hl ?_
    have := Nat.lt_two_pow_self (n := rhoDeg k μD μ0 + μD + 3)
    unfold fixDeg at hρ2
    have : k ≤ 2 ^ (k + 5) := by have := Nat.lt_two_pow_self (n := k + 5); omega
    omega
  have hNT := genNestThr_le_exp hX hEw hC ht0 ht1 (2 ^ k - 1) hlevW hNE'
  have hNT' : (std V D k K p μ0).NestThr alpha ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) :=
    ex_mono hX hNT (by omega)
  -- the roots
  have h64 : (64 : Real) ^ (1 / (std V D k K p μ0).NestExp alpha) ≤
      Real.exp ((2 / alpha) ^ (2 ^ T)) :=
    ex_mono hX (ex_root (j := 3) hX (by norm_num) (by norm_num) hN0 hNE') (by omega)
  have h4 : (4 : Real) ^ (1 / (std V D k K p μ0).NestExp alpha) ≤
      Real.exp ((2 / alpha) ^ (2 ^ T)) :=
    ex_mono hX (ex_root (j := 2) hX (by norm_num) (by norm_num) hN0 hNE') (by omega)
  have h6 : (6 : Real) ^ (1 / (std V D k K p μ0).Eloc alpha) ≤
      Real.exp ((2 / alpha) ^ (2 ^ T)) :=
    ex_mono hX (ex_root (j := 2) hX (by norm_num) (by norm_num) hEl0 hEli) (by omega)
  have hF : (std V D k K p μ0).F alpha = 8 * (std V D k K p μ0).Eloc alpha := by
    show (std V D k K p μ0).F alpha = 8 * ((std V D k K p μ0).F alpha / 8); ring
  have h8 : (8 : Real) ^ (2 / (std V D k K p μ0).F alpha) ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) := by
    have hle : 2 / (std V D k K p μ0).F alpha ≤ 1 / (std V D k K p μ0).Eloc alpha := by
      rw [hF, div_le_div_iff₀ (by positivity) hEl0]; nlinarith
    refine (Real.rpow_le_rpow_of_exponent_le (by norm_num) hle).trans ?_
    exact ex_mono hX (ex_root (j := 2) hX (by norm_num) (by norm_num) hEl0 hEli) (by omega)
  -- the requirement on `m`
  obtain ⟨hR1, hR⟩ := MReq_le_exp H ha ha2
  have hMR : (std V D k K p μ0).MReq alpha ^ (1 / (std V D k K p μ0).MExp alpha) ≤
      Real.exp ((2 / alpha) ^ (2 ^ T)) := by
    rw [one_div]
    refine ex_mono hX (ex_rpow hX hR1 hR (inv_pos.mpr hMx0).le hMx) ?_
    rw [hTdef]; unfold threshDeg; omega
  have hMT : (std V D k K p μ0).MThr alpha ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) :=
    max_le hNT' h64
  -- Lemma 15.6
  have hL := lemma156_gen_le hk ha ha2
  have hL' : lemma156ExplicitThreshold k (alpha / 2) (alpha / 2) ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) := by
    refine ex_of_pw (pw_mono hX hL ?_)
    have : 2 ^ (k + 4) + 4 * k + 13 ≤ 2 ^ (k + 6) + 5 := by
      have h := Nat.lt_two_pow_self (n := k)
      have h4 : 2 ^ (k + 4) = 16 * 2 ^ k := by rw [pow_add]; ring
      have : 2 ^ (k + 6) = 64 * 2 ^ k := by rw [pow_add]; ring
      omega
    omega
  have h3 : (3 : Real) ≤ Real.exp ((2 / alpha) ^ (2 ^ T)) :=
    ex_of_pw (pw_const hX (by
      calc (3 : Real) ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 ^ T) := pow_le_pow_right₀ (by norm_num) (by
            have := Nat.lt_two_pow_self (n := T); omega)))
  show max (max 3 (lemma156ExplicitThreshold k (alpha / 2) (alpha / 2)))
    (max ((std V D k K p μ0).MThr alpha)
      (max (4 ^ (1 / (std V D k K p μ0).NestExp alpha))
        (max ((std V D k K p μ0).MReq alpha ^ (1 / (std V D k K p μ0).MExp alpha))
          (max (6 ^ (1 / (std V D k K p μ0).Eloc alpha)) (8 ^ (2 / (std V D k K p μ0).F alpha)))))) ≤ _
  exact max_le (max_le h3 hL') (max_le hMT (max_le h4 (max_le hMR (max_le h6 h8))))

end GenParams

end LeanProofs.GowersSzemeredi
