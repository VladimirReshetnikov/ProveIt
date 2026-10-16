import GowersSzemeredi.Proofs16SplitAllDimensions

/-! Uniform polynomial covers in every dimension up to `k` (Notes L.7a, F3b).

The single-piece inverse step at dimension `k` needs `PolyCoverAt l` for
every `1 ≤ l ≤ k`. Here all of them are weakened to one control,
`uCount V D = (4V/(γθρ))^D` for the count and its inverse `uExp V D` for the
width exponent:
* `PolyCoverAt.weaken`: larger counts and smaller exponents;
* `polyCoverAt_one_uniform`: dimension one (`polyCoverAt_one`) at any
  `D ≥ 2^132`;
* `uniformCovers_of_classes`: dimensions `2 … k` from the split classes
  (`splitUniformClass_all`), at `V = classV Kc pc k` and
  `D = 2^(76·2^k)`.

One control for every dimension makes the lift densities and widths of the
step closed forms in `(V, D, k)`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-- The uniform count control `(4V/(γθρ))^D`, at least `1` everywhere. -/
def uCount (V : Real) (D : Nat) : Real → Real → Real → Real :=
  fun gamma theta rho => max 1 (uniformBase V 1 theta gamma rho ^ D)

/-- The uniform width-exponent control `(4V/(γθρ))^(-D)`, in `(0, 1]` everywhere. -/
def uExp (V : Real) (D : Nat) : Real → Real → Real → Real :=
  fun gamma theta rho => (uCount V D gamma theta rho)⁻¹

/-- **Polynomial covers in every dimension `1 ≤ l ≤ k`**, with one control. -/
def UniformCovers (k : Nat) (V : Real) (D : Nat) : Prop :=
  ∀ l, 1 ≤ l → l ≤ k → PolyCoverAt l (uCount V D) (uExp V D)

theorem PolyCoverAt.weaken {l : Nat} {Q E Q' E' : Real → Real → Real → Real}
    (h : PolyCoverAt l Q E)
    (hQ : ∀ g t s, 0 < g → g ≤ 1 → 0 < t → t ≤ 1 → 0 < s → s ≤ 1 → Q g t s ≤ Q' g t s)
    (hE0 : ∀ g t s, 0 < g → g ≤ 1 → 0 < t → t ≤ 1 → 0 < s → s ≤ 1 → 0 < E' g t s)
    (hE : ∀ g t s, 0 < g → g ≤ 1 → 0 < t → t ≤ 1 → 0 < s → s ≤ 1 → E' g t s ≤ E g t s) :
    PolyCoverAt l Q' E' := by
  intro N _ _ gamma theta hg hg1 ht ht1 Gamma hsize hprod
  obtain ⟨J, hJ, hML⟩ := h N gamma theta hg hg1 ht ht1 Gamma hsize hprod
  exact ⟨J, hJ, hML.weaken (fun s hs hs1 => hQ gamma theta s hg hg1 ht ht1 hs hs1)
    (fun s hs hs1 => hE0 gamma theta s hg hg1 ht ht1 hs hs1)
    (fun s hs hs1 => hE gamma theta s hg hg1 ht ht1 hs hs1)⟩

/-! ### The uniform controls -/

theorem two_div_le_uniformBase {V : Real} (hV : 1 ≤ V) {gamma theta rho : Real}
    (hg : 0 < gamma) (ht : 0 < theta) (hr : 0 < rho) :
    2 / (gamma * theta * rho) ≤ uniformBase V 1 theta gamma rho := by
  unfold uniformBase
  have hw : 0 ≤ 2 / (gamma * theta * rho) := by positivity
  have h2V : (1 : Real) ≤ ((1 : Nat) + 1) * V := by push_cast; linarith
  calc 2 / (gamma * theta * rho) = 1 * (2 / (gamma * theta * rho)) := (one_mul _).symm
    _ ≤ ((1 : Nat) + 1) * V * (2 / (gamma * theta * rho)) :=
        mul_le_mul_of_nonneg_right h2V hw

theorem uCount_mono {V V' : Real} (hV : 1 ≤ V) (hVV : V ≤ V') {D D' : Nat} (hD : D ≤ D')
    {gamma theta rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1) :
    uCount V D gamma theta rho ≤ uCount V' D' gamma theta rho := by
  have h2 := uniformBase_two_le hV 1 ht ht1 hg hg1 hr hr1
  have h2' := uniformBase_two_le (hV.trans hVV) 1 ht ht1 hg hg1 hr hr1
  have hm := uniformBase_mono_V hVV 1 ht hg hr.le
  unfold uCount
  exact max_le_max le_rfl
    ((pow_le_pow_left₀ (by linarith) hm D).trans (pow_le_pow_right₀ (by linarith) hD))

theorem one_le_uCount (V : Real) (D : Nat) (gamma theta rho : Real) :
    1 ≤ uCount V D gamma theta rho := le_max_left _ _

theorem uExp_pos_le (V : Real) (D : Nat) (gamma theta rho : Real) :
    0 < uExp V D gamma theta rho ∧ uExp V D gamma theta rho ≤ 1 := by
  have h1 := one_le_uCount V D gamma theta rho
  exact ⟨inv_pos.mpr (lt_of_lt_of_le zero_lt_one h1), inv_le_one_of_one_le₀ h1⟩

theorem uExp_pos {V : Real} (_hV : 1 ≤ V) (D : Nat) {gamma theta rho : Real}
    (_hg : 0 < gamma) (_hg1 : gamma ≤ 1) (_ht : 0 < theta) (_ht1 : theta ≤ 1) (_hr : 0 < rho)
    (_hr1 : rho ≤ 1) : 0 < uExp V D gamma theta rho ∧ uExp V D gamma theta rho ≤ 1 :=
  uExp_pos_le V D gamma theta rho

/-- On the range, `uCount` is the power itself. -/
theorem uCount_eq {V : Real} (hV : 1 ≤ V) (D : Nat) {gamma theta rho : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho)
    (hr1 : rho ≤ 1) : uCount V D gamma theta rho = uniformBase V 1 theta gamma rho ^ D := by
  have h2 := uniformBase_two_le hV 1 ht ht1 hg hg1 hr hr1
  unfold uCount
  exact max_eq_right (one_le_pow₀ (by linarith))

/-- `uCount` decreases in `ρ`, so `uExp` increases. -/
theorem uExp_mono_rho {V : Real} (hV : 1 ≤ V) (D : Nat) {gamma theta : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∀ s s', 0 < s → s ≤ s' → s' ≤ 1 → uExp V D gamma theta s ≤ uExp V D gamma theta s' := by
  intro s s' hs hss hs1
  have hs' : 0 < s' := lt_of_lt_of_le hs hss
  have hle : uCount V D gamma theta s' ≤ uCount V D gamma theta s := by
    rw [uCount_eq hV D hg hg1 ht ht1 hs' hs1, uCount_eq hV D hg hg1 ht ht1 hs (hss.trans hs1)]
    have h2 := uniformBase_two_le hV 1 ht ht1 hg hg1 hs' hs1
    refine pow_le_pow_left₀ (by linarith) ?_ D
    unfold uniformBase
    have hgt : 0 < gamma * theta := mul_pos hg ht
    have hdiv : 2 / (gamma * theta * s') ≤ 2 / (gamma * theta * s) :=
      div_le_div_of_nonneg_left (by norm_num) (mul_pos hgt hs)
        (mul_le_mul_of_nonneg_left hss hgt.le)
    exact mul_le_mul_of_nonneg_left hdiv (by positivity)
  exact inv_anti₀ (lt_of_lt_of_le zero_lt_one (one_le_uCount V D gamma theta s')) hle

theorem uExp_anti {V V' : Real} (hV : 1 ≤ V) (hVV : V ≤ V') {D D' : Nat} (hD : D ≤ D')
    {gamma theta rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1) :
    uExp V' D' gamma theta rho ≤ uExp V D gamma theta rho := by
  have h1 := one_le_uCount V D gamma theta rho
  show (uCount V' D' gamma theta rho)⁻¹ ≤ (uCount V D gamma theta rho)⁻¹
  exact inv_anti₀ (lt_of_lt_of_le zero_lt_one h1) (uCount_mono hV hVV hD hg hg1 ht ht1 hr hr1)

theorem PolyCoverAt.uniform_mono {l : Nat} {V V' : Real} {D D' : Nat} (hV : 1 ≤ V)
    (hVV : V ≤ V') (hD : D ≤ D') (h : PolyCoverAt l (uCount V D) (uExp V D)) :
    PolyCoverAt l (uCount V' D') (uExp V' D') :=
  h.weaken (fun _ _ _ hg hg1 ht ht1 hr hr1 => uCount_mono hV hVV hD hg hg1 ht ht1 hr hr1)
    (fun _ _ _ hg hg1 ht ht1 hr hr1 => (uExp_pos (hV.trans hVV) D' hg hg1 ht ht1 hr hr1).1)
    (fun _ _ _ hg hg1 ht ht1 hr hr1 => uExp_anti hV hVV hD hg hg1 ht ht1 hr hr1)

theorem UniformCovers.mono {k k' : Nat} {V V' : Real} {D D' : Nat} (hV : 1 ≤ V)
    (h : UniformCovers k V D) (hk : k' ≤ k) (hVV : V ≤ V') (hD : D ≤ D') :
    UniformCovers k' V' D' :=
  fun l hl1 hlk => (h l hl1 (hlk.trans hk)).uniform_mono hV hVV hD

/-! ### Dimension one -/

/-- **Dimension one with the uniform control**, at any `D ≥ 2^132`. -/
theorem polyCoverAt_one_uniform {V : Real} (hV : 1 ≤ V) {D : Nat} (hD : 2 ^ 132 ≤ D) :
    PolyCoverAt 1 (uCount V D) (uExp V D) := by
  have hw2 : ∀ gamma theta rho : Real, 0 < gamma → gamma ≤ 1 → 0 < theta → theta ≤ 1 →
      0 < rho → rho ≤ 1 → (2 : Real) ≤ 2 / (gamma * theta * rho) := by
    intro gamma theta rho hg hg1 ht ht1 hr hr1
    obtain ⟨hv2, hvw, -⟩ := prod_scale_radius_bounds hg hg1 ht ht1 hr hr1
    exact hv2.trans hvw
  refine polyCoverAt_one.weaken ?_ ?_ ?_
  · intro gamma theta rho hg hg1 ht ht1 hr hr1
    have hw := two_div_le_uniformBase hV hg ht hr
    have hw2' := hw2 gamma theta rho hg hg1 ht ht1 hr hr1
    have hw0 : (0 : Real) ≤ 2 / (gamma * theta * rho) := le_trans zero_le_two hw2'
    have hu1 : (1 : Real) ≤ uniformBase V 1 theta gamma rho :=
      le_trans one_le_two (hw2'.trans hw)
    have hmono : (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 90) ≤ uCount V D gamma theta rho := by
      unfold uCount
      exact le_max_of_le_right ((pow_le_pow_left₀ hw0 hw _).trans
        (pow_le_pow_right₀ hu1 ((show (2 : Nat) ^ 90 ≤ 2 ^ 132 by norm_num).trans hD)))
    have h := sixQb_le_power 1 hg hg1 ht ht1 hr hr1
    rw [sixQb, if_pos rfl] at h
    exact h.trans hmono
  · intro gamma theta rho hg hg1 ht ht1 hr hr1
    exact (uExp_pos hV D hg hg1 ht ht1 hr hr1).1
  · intro gamma theta rho hg hg1 ht ht1 hr hr1
    have hw := two_div_le_uniformBase hV hg ht hr
    have hw2' := hw2 gamma theta rho hg hg1 ht ht1 hr hr1
    have hw0 : (0 : Real) ≤ 2 / (gamma * theta * rho) := le_trans zero_le_two hw2'
    have hu1 : (1 : Real) ≤ uniformBase V 1 theta gamma rho :=
      le_trans one_le_two (hw2'.trans hw)
    have hK : ((1 : Nat) : Real) ≤ (2 / (gamma * theta * rho)) ^ 3 := by
      rw [Nat.cast_one]; exact one_le_pow₀ (le_trans one_le_two hw2')
    have hpos : 0 < cubicBaseExponent (section16BaseFamilyBound gamma theta) rho :=
      cubicBaseExponent_pos (section16BaseFamilyBound_pos gamma theta) hr
    have hmono : (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 132) ≤ uCount V D gamma theta rho := by
      unfold uCount
      exact le_max_of_le_right ((pow_le_pow_left₀ hw0 hw _).trans (pow_le_pow_right₀ hu1 hD))
    have h := sixEb_inv_le_power 1 (K1 := 1) (p1 := 1) one_pos one_pos hg hg1 ht ht1 hr hr1 hK hK
    rw [sixEb, if_pos rfl] at h
    have hB := h.trans hmono
    have := inv_anti₀ (inv_pos.mpr hpos) hB
    rw [inv_inv] at this
    exact this

/-! ### Every dimension up to `k` -/

theorem classV_mono (Kc pc : Nat → Nat) {j k : Nat} (h : j ≤ k) :
    classV Kc pc j ≤ classV Kc pc k := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (classV_le_succ Kc pc _)

/-- The uniform degree in dimension `k`. -/
def uDeg (k : Nat) : Nat := 2 ^ (76 * 2 ^ k)

/-- The split degrees fit the uniform degree. -/
theorem split_pair_le_uDeg {l : Nat} (hl : 2 ≤ l) :
    (splitPair l).1 + (splitPair l).2 + l + 1 ≤ uDeg l := by
  obtain ⟨-, -, hA, hD⟩ := split_pair_bounds l hl
  have ha : (splitPair l).1 ≤ 2 ^ (35 * 2 ^ l) :=
    le_trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)) hA
  have h3575 : 2 ^ (35 * 2 ^ l) ≤ 2 ^ (75 * 2 ^ l) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlA : l + 1 ≤ 2 ^ (75 * 2 ^ l) := by
    have h1 : l + 1 ≤ 2 ^ (l + 1) := Nat.lt_two_pow_self.le
    have h2 : l + 1 ≤ 75 * 2 ^ l := by
      have := Nat.lt_two_pow_self (n := l); omega
    exact h1.trans (Nat.pow_le_pow_right (by norm_num) h2)
  unfold uDeg
  have h76 : 2 ^ (76 * 2 ^ l) = 2 ^ (75 * 2 ^ l) * 2 ^ (2 ^ l) := by
    rw [← pow_add]; congr 1; ring
  have h4 : 4 ≤ 2 ^ (2 ^ l) := by
    have : 2 ≤ 2 ^ l := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 ^ l) := Nat.pow_le_pow_right (by norm_num) this
  rw [h76]
  nlinarith [Nat.zero_le (2 ^ (75 * 2 ^ l))]

/-- **Uniform covers in every dimension up to `k`**, from the family lemmas. -/
theorem uniformCovers_of_classes (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))))
    (k : Nat) : UniformCovers k (classV Kc pc k) (uDeg k) := by
  intro l hl1 hlk
  have hVk := one_le_classV Kc pc k
  rcases Nat.lt_or_ge l 2 with hl | hl
  · obtain rfl : l = 1 := by omega
    refine polyCoverAt_one_uniform hVk ?_
    unfold uDeg
    have : 132 ≤ 76 * 2 ^ k := by
      have : 2 ≤ 2 ^ k := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact Nat.pow_le_pow_right (by norm_num) this
  · obtain ⟨C⟩ := splitUniformClass_all Kc pc hK hp hlem l hl
    have hVl := one_le_classV Kc pc l
    have hfit := split_pair_le_uDeg hl
    have P0 := (C.toPower hVl).polyCoverAt (by omega) hVl (D := uDeg l) (by omega) (by omega)
      (by omega)
    have P : PolyCoverAt l (uCount (classV Kc pc l) (uDeg l)) (uExp (classV Kc pc l) (uDeg l)) := by
      refine P0.weaken ?_ ?_ ?_
      · intro g t s hg hg1 ht ht1 hs hs1
        rw [uCount_eq hVl _ hg hg1 ht ht1 hs hs1]
      · intro g t s _ _ _ _ _ _
        exact (uExp_pos_le _ _ g t s).1
      · intro g t s hg hg1 ht ht1 hs hs1
        show (uCount _ _ g t s)⁻¹ ≤ _
        rw [uCount_eq hVl _ hg hg1 ht ht1 hs hs1]
    exact P.uniform_mono hVl (classV_mono Kc pc hlk)
      (Nat.pow_le_pow_right (by norm_num)
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hlk)))

end LeanProofs.GowersSzemeredi
