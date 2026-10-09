import GowersSzemeredi.Proofs16AbstractBSGCore
import GowersSzemeredi.Proofs16RefinementKernel
import GowersSzemeredi.Proofs16BohrBohrSections

/-! The abstract Balog–Szemerédi–Gowers engine for column systems in `ℤ/N`,
with exact zero relations.

A *column system* assigns to each `x ∈ X` a spectrum `T x` of size at most
`D` and a normalized map `L x`, Freiman-linear on `B(T x; ρ₀)`. The
quadruple family at level `n + 1` (`columnZeroQ`) is: the columns lie in
`X`, `a₁ − a₂ = a₃ − a₄`, and the alternating combination
`L a₁ − L a₂ − L a₃ + L a₄` vanishes on
`B(T a₁ ∪ T a₂ ∪ T a₃ ∪ T a₄; ρ_n)`. Level `0` is empty. The radii
`ρ_{n+1} = refinementKernelRadius (4D) (2D) ρ₀ ρ_n` (`zeroLadderRadius`)
shrink once per level.

* `columnZeroQ_S1`, `columnZeroQ_S2`, `columnZeroQ_S3`: the three symmetries.
* `columnZeroQ_weakTransitive`: weak transitivity up to level `16`, with
  *any* constant `c′ > 0`. A single bridge suffices: the two zero relations
  add on the six-column domain, and `freiman_zero_remove_frequencies`
  removes the bridge's frequencies. This needs
  `refinementKernelCap (4D) (2D) ρ₀ ρ₁₄ < N`.
* `column_bsg_core`: for `N` an odd prime, `abstract_bsg_core` applies to
  column systems. The constraints on `c′` disappear, because `c′` can be
  chosen freely. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped Pointwise

/-- The alternating combination of four column maps. -/
def columnAlt {N : Nat} (L : ZMod N → ZMod N → ZMod N) (a₁ a₂ a₃ a₄ y : ZMod N) : ZMod N :=
  L a₁ y - L a₂ y - L a₃ y + L a₄ y

/-- The union of four column spectra. -/
def quadSpec {N : Nat} (T : ZMod N → Finset (ZMod N)) (a₁ a₂ a₃ a₄ : ZMod N) :
    Finset (ZMod N) :=
  T a₁ ∪ T a₂ ∪ T a₃ ∪ T a₄

/-- The radius schedule of the zero ladder. -/
def zeroLadderRadius (D : Nat) (ρ₀ ρ₁ : Real) : Nat → Real
  | 0 => ρ₁
  | n + 1 => refinementKernelRadius (4 * D) (2 * D) ρ₀ (zeroLadderRadius D ρ₀ ρ₁ n)

/-- The exact zero-relation ladder of a column system. -/
def columnZeroQ {N : Nat} [NeZero N] (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (D : Nat) (ρ₀ ρ₁ : Real) :
    Nat → ZMod N → ZMod N → ZMod N → ZMod N → Prop
  | 0, _, _, _, _ => False
  | n + 1, a₁, a₂, a₃, a₄ => a₁ ∈ X ∧ a₂ ∈ X ∧ a₃ ∈ X ∧ a₄ ∈ X ∧ a₁ - a₂ = a₃ - a₄ ∧
      ∀ y ∈ bohr (quadSpec T a₁ a₂ a₃ a₄) (zeroLadderRadius D ρ₀ ρ₁ n),
        columnAlt L a₁ a₂ a₃ a₄ y = 0

theorem zeroLadderRadius_pos {D : Nat} {ρ₀ ρ₁ : Real} (h₀ : 0 < ρ₀) (h₁ : 0 < ρ₁) (n : Nat) :
    0 < zeroLadderRadius D ρ₀ ρ₁ n := by
  induction n with
  | zero => exact h₁
  | succ n ih => exact refinementKernelRadius_pos _ _ h₀ ih

theorem refinementKernelRadius_le_base (d e : Nat) {ρ r : Real} (hρ : 0 < ρ) (hr : 0 < r) :
    refinementKernelRadius d e ρ r ≤ ρ := by
  have hK : (1 : Real) ≤ refinementKernelCap d e ρ r := by
    exact_mod_cast refinementKernelCap_pos d e hρ hr
  unfold refinementKernelRadius
  rw [div_le_iff₀ (by linarith)]
  nlinarith

theorem zeroLadderRadius_le {D : Nat} {ρ₀ ρ₁ : Real} (h₀ : 0 < ρ₀) (h₁ : 0 < ρ₁)
    (h₁₀ : ρ₁ ≤ ρ₀) (n : Nat) : zeroLadderRadius D ρ₀ ρ₁ n ≤ ρ₀ := by
  cases n with
  | zero => exact h₁₀
  | succ n => exact refinementKernelRadius_le_base _ _ h₀ (zeroLadderRadius_pos h₀ h₁ n)

theorem refinementKernelCap_anti (d e : Nat) {ρ r r' : Real} (hr : 0 < r) (h : r ≤ r') :
    refinementKernelCap d e ρ r' ≤ refinementKernelCap d e ρ r := by
  unfold refinementKernelCap
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  exact Nat.ceil_mono (one_div_le_one_div_of_le hr h)

theorem refinementKernelRadius_mono (d e : Nat) {ρ r r' : Real} (hρ : 0 < ρ) (hr : 0 < r)
    (h : r ≤ r') : refinementKernelRadius d e ρ r ≤ refinementKernelRadius d e ρ r' := by
  unfold refinementKernelRadius
  have h1 : (0 : Real) < refinementKernelCap d e ρ r' := by
    exact_mod_cast refinementKernelCap_pos d e hρ (hr.trans_le h)
  apply div_le_div_of_nonneg_left (by positivity) h1
  exact_mod_cast refinementKernelCap_anti d e hr h

theorem refinementKernelRadius_le_self {d e : Nat} {ρ r : Real} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2)
    (hr : 0 < r) (hde : 1 ≤ d + e) : refinementKernelRadius d e ρ r ≤ r := by
  have hP : (1 : Real) ≤ denseLevelCells ρ := by
    exact_mod_cast (Nat.ceil_pos.mpr (by positivity) : 0 < denseLevelCells ρ)
  have hQ : 1 / r ≤ (refinementCells r : Real) := Nat.le_ceil _
  have hQ1 : (1 : Real) ≤ refinementCells r := by
    exact_mod_cast (Nat.ceil_pos.mpr (by positivity) : 0 < refinementCells r)
  have hcap : 1 / r ≤ (refinementKernelCap d e ρ r : Real) := by
    unfold refinementKernelCap
    push_cast
    calc 1 / r ≤ (refinementCells r : Real) := hQ
      _ = (refinementCells r : Real) ^ 1 := (pow_one _).symm
      _ ≤ (refinementCells r : Real) ^ (d + e) := pow_le_pow_right₀ hQ1 hde
      _ = 1 * (refinementCells r : Real) ^ (d + e) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (one_le_pow₀ hP) (by positivity)
  unfold refinementKernelRadius
  have hcpos : (0 : Real) < refinementKernelCap d e ρ r := (by positivity : (0 : Real) < 1 / r).trans_le hcap
  rw [div_le_iff₀ hcpos]
  have : r * (1 / r) = 1 := by field_simp
  nlinarith

theorem zeroLadderRadius_anti {D : Nat} (hD : 1 ≤ D) {ρ₀ ρ₁ : Real} (h₀ : 0 < ρ₀) (h₀2 : ρ₀ ≤ 2)
    (h₁ : 0 < ρ₁) {m n : Nat} (hmn : m ≤ n) :
    zeroLadderRadius D ρ₀ ρ₁ n ≤ zeroLadderRadius D ρ₀ ρ₁ m := by
  induction hmn with
  | refl => exact le_rfl
  | step _ ih =>
    exact (refinementKernelRadius_le_self h₀ h₀2 (zeroLadderRadius_pos h₀ h₁ _)
      (by omega)).trans ih

theorem quadSpec_perm₁ {N : Nat} (T : ZMod N → Finset (ZMod N)) (a₁ a₂ a₃ a₄ : ZMod N) :
    quadSpec T a₃ a₄ a₁ a₂ = quadSpec T a₁ a₂ a₃ a₄ := by
  unfold quadSpec; ext; simp only [Finset.mem_union]; tauto

theorem quadSpec_perm₂ {N : Nat} (T : ZMod N → Finset (ZMod N)) (a₁ a₂ a₃ a₄ : ZMod N) :
    quadSpec T a₂ a₁ a₄ a₃ = quadSpec T a₁ a₂ a₃ a₄ := by
  unfold quadSpec; ext; simp only [Finset.mem_union]; tauto

theorem quadSpec_perm₃ {N : Nat} (T : ZMod N → Finset (ZMod N)) (a₁ a₂ a₃ a₄ : ZMod N) :
    quadSpec T a₁ a₃ a₂ a₄ = quadSpec T a₁ a₂ a₃ a₄ := by
  unfold quadSpec; ext; simp only [Finset.mem_union]; tauto

section Symmetries
variable {N : Nat} [NeZero N] (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
  (L : ZMod N → ZMod N → ZMod N) (D : Nat) (ρ₀ ρ₁ : Real)

theorem columnZeroQ_S1 (n : Nat) (a₁ a₂ a₃ a₄ : ZMod N)
    (h : columnZeroQ X T L D ρ₀ ρ₁ n a₁ a₂ a₃ a₄) : columnZeroQ X T L D ρ₀ ρ₁ n a₃ a₄ a₁ a₂ := by
  cases n with
  | zero => exact h.elim
  | succ n =>
    obtain ⟨h1, h2, h3, h4, hadd, hz⟩ := h
    refine ⟨h3, h4, h1, h2, hadd.symm, fun y hy => ?_⟩
    rw [quadSpec_perm₁] at hy
    have := hz y hy
    unfold columnAlt at this ⊢
    linear_combination -this

theorem columnZeroQ_S2 (n : Nat) (a₁ a₂ a₃ a₄ : ZMod N)
    (h : columnZeroQ X T L D ρ₀ ρ₁ n a₁ a₂ a₃ a₄) : columnZeroQ X T L D ρ₀ ρ₁ n a₂ a₁ a₄ a₃ := by
  cases n with
  | zero => exact h.elim
  | succ n =>
    obtain ⟨h1, h2, h3, h4, hadd, hz⟩ := h
    refine ⟨h2, h1, h4, h3, by linear_combination -hadd, fun y hy => ?_⟩
    rw [quadSpec_perm₂] at hy
    have := hz y hy
    unfold columnAlt at this ⊢
    linear_combination -this

theorem columnZeroQ_S3 (n : Nat) (a₁ a₂ a₃ a₄ : ZMod N)
    (h : columnZeroQ X T L D ρ₀ ρ₁ n a₁ a₂ a₃ a₄) : columnZeroQ X T L D ρ₀ ρ₁ n a₁ a₃ a₂ a₄ := by
  cases n with
  | zero => exact h.elim
  | succ n =>
    obtain ⟨h1, h2, h3, h4, hadd, hz⟩ := h
    refine ⟨h1, h3, h2, h4, by linear_combination hadd, fun y hy => ?_⟩
    rw [quadSpec_perm₃] at hy
    have := hz y hy
    unfold columnAlt at this ⊢
    linear_combination this

end Symmetries

theorem IsFreimanLinearOn.alt {N : Nat} {B : Finset (ZMod N)} {f₁ f₂ f₃ f₄ : ZMod N → ZMod N}
    (h₁ : IsFreimanLinearOn B f₁) (h₂ : IsFreimanLinearOn B f₂) (h₃ : IsFreimanLinearOn B f₃)
    (h₄ : IsFreimanLinearOn B f₄) :
    IsFreimanLinearOn B fun y => f₁ y - f₂ y - f₃ y + f₄ y := by
  intro y₁ y₂ y₃ y₄ m₁ m₂ m₃ m₄ hs
  have e₁ := h₁ y₁ y₂ y₃ y₄ m₁ m₂ m₃ m₄ hs
  have e₂ := h₂ y₁ y₂ y₃ y₄ m₁ m₂ m₃ m₄ hs
  have e₃ := h₃ y₁ y₂ y₃ y₄ m₁ m₂ m₃ m₄ hs
  have e₄ := h₄ y₁ y₂ y₃ y₄ m₁ m₂ m₃ m₄ hs
  linear_combination e₁ - e₂ - e₃ + e₄

/-- **Weak transitivity of the zero ladder, with a single bridge.** -/
theorem columnZeroQ_weakTransitive {N : Nat} [NeZero N] [Fact N.Prime]
    {A X : Finset (ZMod N)} (hX : X.Nonempty) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {D : Nat} (hD : 1 ≤ D) {ρ₀ ρ₁ : Real}
    (h₀ : 0 < ρ₀) (h₀1 : ρ₀ ≤ 1) (h₁ : 0 < ρ₁) (h₁₀ : ρ₁ ≤ ρ₀)
    (hcol : ∀ x ∈ X, (T x).card ≤ D ∧ IsFreimanLinearOn (bohr (T x) ρ₀) (L x) ∧ L x 0 = 0)
    (hN : refinementKernelCap (4 * D) (2 * D) ρ₀ (zeroLadderRadius D ρ₀ ρ₁ 14) < N)
    {c' : Real} (hc' : 0 < c') :
    ∀ i j, i + j ≤ 16 → ∀ a₁ a₂ a₃ a₄, c' * X.card ≤ (((A ×ˢ A).filter fun p =>
      columnZeroQ X T L D ρ₀ ρ₁ i a₁ a₂ p.1 p.2 ∧
        columnZeroQ X T L D ρ₀ ρ₁ j p.1 p.2 a₃ a₄).card : Real) →
      columnZeroQ X T L D ρ₀ ρ₁ (i + j) a₁ a₂ a₃ a₄ := by
  intro i j hij a₁ a₂ a₃ a₄ hcount
  have hpos : 0 < ((A ×ˢ A).filter fun p => columnZeroQ X T L D ρ₀ ρ₁ i a₁ a₂ p.1 p.2 ∧
      columnZeroQ X T L D ρ₀ ρ₁ j p.1 p.2 a₃ a₄).card := by
    have : (0 : Real) < c' * X.card := mul_pos hc' (by exact_mod_cast hX.card_pos)
    exact_mod_cast this.trans_le hcount
  obtain ⟨⟨b, b'⟩, hb⟩ := Finset.card_pos.mp hpos
  obtain ⟨-, hQi, hQj⟩ := Finset.mem_filter.mp hb
  cases i with
  | zero => exact hQi.elim
  | succ i =>
  cases j with
  | zero => exact hQj.elim
  | succ j =>
  obtain ⟨m₁, m₂, mb, mb', hadd₁, hz₁⟩ := hQi
  obtain ⟨-, -, m₃, m₄, hadd₂, hz₂⟩ := hQj
  rw [show i + 1 + (j + 1) = (i + j + 1) + 1 by omega]
  refine ⟨m₁, m₂, m₃, m₄, hadd₁.trans hadd₂, ?_⟩
  -- the radii involved
  let r := min (zeroLadderRadius D ρ₀ ρ₁ i) (zeroLadderRadius D ρ₀ ρ₁ j)
  have hr : 0 < r := lt_min (zeroLadderRadius_pos h₀ h₁ i) (zeroLadderRadius_pos h₀ h₁ j)
  have hrρ : r ≤ ρ₀ := (min_le_left _ _).trans (zeroLadderRadius_le h₀ h₁ h₁₀ i)
  have hmid : zeroLadderRadius D ρ₀ ρ₁ (i + j) ≤ r :=
    le_min (zeroLadderRadius_anti hD h₀ (by linarith) h₁ (by omega))
      (zeroLadderRadius_anti hD h₀ (by linarith) h₁ (by omega))
  let T4 := quadSpec T a₁ a₂ a₃ a₄
  let U := T b ∪ T b'
  -- the combination is Freiman-linear and normalized on the four-column domain
  have hsub : ∀ x, x = a₁ ∨ x = a₂ ∨ x = a₃ ∨ x = a₄ → T x ⊆ T4 := by
    rintro x (rfl | rfl | rfl | rfl) <;> intro t ht <;>
      simp only [T4, quadSpec, Finset.mem_union] <;> tauto
  have hF : ∀ x, x ∈ X → (x = a₁ ∨ x = a₂ ∨ x = a₃ ∨ x = a₄) →
      IsFreimanLinearOn (bohr T4 ρ₀) (L x) := fun x hx hx' =>
    (hcol x hx).2.1.mono (bohr_anti (hsub x hx') ρ₀)
  have hf : IsFreimanLinearOn (bohr T4 ρ₀) (columnAlt L a₁ a₂ a₃ a₄) :=
    IsFreimanLinearOn.alt (hF a₁ m₁ (by tauto)) (hF a₂ m₂ (by tauto)) (hF a₃ m₃ (by tauto))
      (hF a₄ m₄ (by tauto))
  have hf0 : columnAlt L a₁ a₂ a₃ a₄ 0 = 0 := by
    unfold columnAlt
    rw [(hcol a₁ m₁).2.2, (hcol a₂ m₂).2.2, (hcol a₃ m₃).2.2, (hcol a₄ m₄).2.2]
    ring
  have hT4 : T4.card ≤ 4 * D := by
    have := Finset.card_union_le (T a₁ ∪ T a₂ ∪ T a₃) (T a₄)
    have := Finset.card_union_le (T a₁ ∪ T a₂) (T a₃)
    have := Finset.card_union_le (T a₁) (T a₂)
    have := (hcol a₁ m₁).1; have := (hcol a₂ m₂).1
    have := (hcol a₃ m₃).1; have := (hcol a₄ m₄).1
    simp only [T4, quadSpec]
    omega
  have hU : U.card ≤ 2 * D := by
    have := Finset.card_union_le (T b) (T b')
    have := (hcol b mb).1; have := (hcol b' mb').1
    simp only [U]
    omega
  -- zero on the six-column domain
  have hzero : ∀ y ∈ bohr (T4 ∪ U) r, columnAlt L a₁ a₂ a₃ a₄ y = 0 := by
    intro y hy
    have hy₁ : y ∈ bohr (quadSpec T a₁ a₂ b b') (zeroLadderRadius D ρ₀ ρ₁ i) := by
      refine bohr_mono_radius _ (min_le_left _ _) (bohr_anti ?_ r hy)
      intro t ht
      simp only [T4, U, quadSpec, Finset.mem_union] at ht ⊢
      tauto
    have hy₂ : y ∈ bohr (quadSpec T b b' a₃ a₄) (zeroLadderRadius D ρ₀ ρ₁ j) := by
      refine bohr_mono_radius _ (min_le_right _ _) (bohr_anti ?_ r hy)
      intro t ht
      simp only [T4, U, quadSpec, Finset.mem_union] at ht ⊢
      tauto
    have e₁ := hz₁ y hy₁
    have e₂ := hz₂ y hy₂
    unfold columnAlt at e₁ e₂ ⊢
    linear_combination e₁ + e₂
  -- remove the bridge's frequencies
  have hcap : refinementKernelCap (4 * D) (2 * D) ρ₀ r < N := by
    refine lt_of_le_of_lt ?_ hN
    apply refinementKernelCap_anti _ _ (zeroLadderRadius_pos h₀ h₁ 14)
    exact (zeroLadderRadius_anti hD h₀ (by linarith) h₁ (by omega)).trans hmid
  have hkernel := freiman_zero_remove_frequencies T4 U (columnAlt L a₁ a₂ a₃ a₄) h₀ hr hrρ
    hT4 hU hf hf0 hzero hcap
  intro y hy
  apply hkernel
  refine bohr_mono_radius _ ?_ hy
  exact refinementKernelRadius_mono _ _ h₀ (zeroLadderRadius_pos h₀ h₁ _) hmid

/-- An odd prime cyclic group has no `2`-torsion. -/
theorem zmod_two_torsion_free {N : Nat} [Fact N.Prime] (hN2 : N ≠ 2) (d : ZMod N)
    (h : d + d = 0) : d = 0 := by
  have h2 : (2 : ZMod N) ≠ 0 := by
    intro h0
    have hdvd : N ∣ 2 := (ZMod.natCast_eq_zero_iff 2 N).mp (by exact_mod_cast h0)
    have hp := (Fact.out : N.Prime)
    rcases (Nat.prime_two.eq_one_or_self_of_dvd N hdvd) with h1 | h1
    · exact hp.one_lt.ne' h1
    · exact hN2 h1
  have : (2 : ZMod N) * d = 0 := by rw [two_mul]; exact h
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd h' h2
  · exact h'

/-- **The abstract BSG core for column systems in `ℤ/N`.** -/
theorem column_bsg_core {N : Nat} [NeZero N] [Fact N.Prime] (hN2 : N ≠ 2)
    {A X : Finset (ZMod N)} (hAX : A ⊆ X) (hX : X.Nonempty)
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N) {D : Nat} (hD : 1 ≤ D)
    {ρ₀ ρ₁ : Real} (h₀ : 0 < ρ₀) (h₀1 : ρ₀ ≤ 1) (h₁ : 0 < ρ₁) (h₁₀ : ρ₁ ≤ ρ₀)
    (hcol : ∀ x ∈ X, (T x).card ≤ D ∧ IsFreimanLinearOn (bohr (T x) ρ₀) (L x) ∧ L x 0 = 0)
    (hN : refinementKernelCap (4 * D) (2 * D) ρ₀ (zeroLadderRadius D ρ₀ ρ₁ 14) < N)
    {c K θ : Real} (hc0 : 0 < c) (hK : 0 < K) (hdoub : ((X - X).card : Real) ≤ K * X.card)
    (hgood : c * (X.card : Real) ^ 3 ≤
      ∑ d ∈ X - X, (diffGoodCount A (columnZeroQ X T L D ρ₀ ρ₁ 1) d : Real))
    (hcX : 4 ≤ c * X.card) (hθ : θ < absBsgKappa c K / 2) :
    ∃ B B' : Finset (ZMod N), B' ⊆ B ∧ B ⊆ A ∧ absBsgEps c K * X.card ≤ (B'.card : Real) ∧
      ∀ a ∈ B', θ * (X.card : Real) ^ 2 ≤ richCount B (columnZeroQ X T L D ρ₀ ρ₁ 16) a := by
  have hδ : 0 < absBsgDelta c K := by unfold absBsgDelta; positivity
  have hκ : 0 < absBsgKappa c K := by
    unfold absBsgKappa absBsgEps absBsgEta absBsgDelta2; positivity
  let c' := min (absBsgDelta c K ^ 5 / 16384 / 8) (absBsgKappa c K / 16)
  have hc' : 0 < c' := lt_min (by positivity) (by positivity)
  have hc'1 : 8 * c' ≤ absBsgDelta c K ^ 5 / 16384 := by
    have := min_le_left (absBsgDelta c K ^ 5 / 16384 / 8) (absBsgKappa c K / 16)
    linarith
  have hc'2 : 16 * c' ≤ absBsgKappa c K := by
    have := min_le_right (absBsgDelta c K ^ 5 / 16384 / 8) (absBsgKappa c K / 16)
    linarith
  exact abstract_bsg_core (zmod_two_torsion_free hN2) hAX hX (columnZeroQ X T L D ρ₀ ρ₁)
    (columnZeroQ_S1 X T L D ρ₀ ρ₁ 1) (columnZeroQ_S2 X T L D ρ₀ ρ₁ 4)
    (fun i => columnZeroQ_S3 X T L D ρ₀ ρ₁ i) hc0 hc'
    (columnZeroQ_weakTransitive hX T L hD h₀ h₀1 h₁ h₁₀ hcol hN hc')
    hK (by convert hdoub) (by convert hgood) hcX hc'1 hc'2 hθ

end LeanProofs.GowersSzemeredi
