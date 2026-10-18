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
The last two are in `Proofs18UniformCoversSide`, outside the final route.

One control for every dimension makes the lift densities and widths of the
step closed forms in `(V, D, k)`.

`uDeg` and `uExp_mono_rho` are in `Proofs18UniformCoversSide`, outside the final
route. -/
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

/-! ### Every dimension up to `k` -/

theorem classV_mono (Kc pc : Nat → Nat) {j k : Nat} (h : j ≤ k) :
    classV Kc pc j ≤ classV Kc pc k := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (classV_le_succ Kc pc _)

end LeanProofs.GowersSzemeredi
