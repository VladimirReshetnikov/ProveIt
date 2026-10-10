import GowersSzemeredi.Proofs16ProperBohrProgression
import OAI.Combinatorics.Progressions.Estimates.LocalizedSiftingAlmostPeriods

/-! **Lemma 7.8 at Sanders strength**: the linear part of a Freiman
8-homomorphism on a set of density `e^(−p)` lives on a Bohr set of rank
`≤ 1 + C(p+1)⁴`. This is the low-rank half of Milićević's Theorem 2.26
(arXiv:2601.01682), which J.5c Further question 3 needs.

The corpus's Lemma 7.8 puts the linear part on a Fourier-spectrum Bohr set
of rank `16α^(−2)`. That is too large when `α` is already `exp(−poly)`, as
in Claims 9.4/9.5. Here the domain comes instead from the ported
Croot–Sisask/Sanders estimate
`OAI.Erdos3.CyclicCrootSisask.exists_quartic_bogolyubov`, a rank-regular Bohr
set inside `2A − 2A`.
* `quadSumExt A f`: on `2A − 2A`,
  `ψ(a₁ + a₂ − a₃ − a₄) = f a₁ + f a₂ − f a₃ − f a₄`. It is well defined for a
  Freiman 4-homomorphism (`quadSumExt_spec`), and Freiman-linear on `2A − 2A`
  for a Freiman 8-homomorphism (`quadSumExt_freimanLinear`).
* `quadSumExt_sub`: `f a − f a′ = ψ(a − a′)` for *all* `a, a′ ∈ A`.
* `bohr_subset_oai_carrier`: the corpus Bohr set `bohr Γ (ρ/(2π))` lies in
  the OAI chord-radius set with frequencies `Γ` and radius `ρ`.
* `sanders_linear_part`: the combination. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped Pointwise

/-- The phase bound `‖e(x) − 1‖ ≤ 2π|x|/N`. -/
theorem phase_norm_le_two_pi_centeredAbs {N : Nat} [NeZero N] (x : ZMod N) :
    ‖exponential x - 1‖ ≤ 2 * Real.pi * centeredAbs x / N := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have habsval : |(x.valMinAbs : Real)| = (centeredAbs x : Real) := by
    rw [centeredAbs, ← Int.cast_abs, Int.abs_eq_natAbs]
    rfl
  rw [exponential_eq_exp_valMinAbs]
  calc ‖Complex.exp (Complex.I * (2 * Real.pi * (x.valMinAbs : Real) / N : Real)) - 1‖
      ≤ ‖2 * Real.pi * (x.valMinAbs : Real) / N‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * centeredAbs x / N := by
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : Real) ≤ 2), abs_of_pos Real.pi_pos, habsval,
        abs_of_pos hN]

/-- A corpus Bohr set at radius `ρ/(2π)` lies inside the OAI chord-radius set. -/
theorem bohr_subset_oai_carrier {N : Nat} [NeZero N] (R : OAI.Erdos3.CyclicBohr.Set N) :
    bohr R.frequencies (R.radius / (2 * Real.pi)) ⊆ R.carrier := by
  intro x hx
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  refine OAI.Erdos3.CyclicBohr.Set.mem_carrier.mpr fun r hr => ?_
  have hb := (Finset.mem_filter.mp hx).2 r hr
  rw [oai_character_eq_exponential, norm_sub_rev]
  calc ‖exponential (r * x) - 1‖ ≤ 2 * Real.pi * centeredAbs (r * x) / N :=
        phase_norm_le_two_pi_centeredAbs _
    _ ≤ 2 * Real.pi * (R.radius / (2 * Real.pi) * N) / N := by
        gcongr
    _ = R.radius := by field_simp

/-- The four-term sums `a₁ + a₂ − a₃ − a₄` of `A`. -/
def quadSumSet {N : Nat} (A : Finset (ZMod N)) : Set (ZMod N) :=
  {x | ∃ a₁ ∈ A, ∃ a₂ ∈ A, ∃ a₃ ∈ A, ∃ a₄ ∈ A, x = a₁ + a₂ - a₃ - a₄}

/-- The extension of `f` to four-term sums. -/
def quadSumExt {N : Nat} (A : Finset (ZMod N)) (f : ZMod N → ZMod N) (x : ZMod N) : ZMod N :=
  if h : x ∈ quadSumSet A then
    f h.choose + f h.choose_spec.2.choose - f h.choose_spec.2.choose_spec.2.choose -
      f h.choose_spec.2.choose_spec.2.choose_spec.2.choose
  else 0

theorem freimanHom_eq_of_sum {N : Nat} {k : Nat} {A : Finset (ZMod N)} {f : ZMod N → ZMod N}
    (hf : FreimanHom k A f) {s t : Multiset (ZMod N)} (hs : ∀ x ∈ s, x ∈ A)
    (ht : ∀ x ∈ t, x ∈ A) (hsk : s.card = k) (htk : t.card = k) (hst : s.sum = t.sum) :
    (s.map f).sum = (t.map f).sum :=
  IsAddFreimanHom.map_sum_eq_map_sum hf hs ht hsk htk hst

/-- Well-definedness on four-term sums, for a Freiman 4-homomorphism. -/
theorem quadSumExt_spec {N : Nat} {A : Finset (ZMod N)} {f : ZMod N → ZMod N}
    (hf : FreimanHom 4 A f) {a₁ a₂ a₃ a₄ : ZMod N} (h₁ : a₁ ∈ A) (h₂ : a₂ ∈ A) (h₃ : a₃ ∈ A)
    (h₄ : a₄ ∈ A) : quadSumExt A f (a₁ + a₂ - a₃ - a₄) = f a₁ + f a₂ - f a₃ - f a₄ := by
  have hmem : a₁ + a₂ - a₃ - a₄ ∈ quadSumSet A := ⟨a₁, h₁, a₂, h₂, a₃, h₃, a₄, h₄, rfl⟩
  rw [quadSumExt, dif_pos hmem]
  obtain ⟨b₁m, hb⟩ := hmem.choose_spec
  obtain ⟨b₂m, hb⟩ := hb.choose_spec
  obtain ⟨b₃m, hb⟩ := hb.choose_spec
  obtain ⟨b₄m, he⟩ := hb.choose_spec
  set b₁ := hmem.choose
  set b₂ := hmem.choose_spec.2.choose
  set b₃ := hmem.choose_spec.2.choose_spec.2.choose
  set b₄ := hmem.choose_spec.2.choose_spec.2.choose_spec.2.choose
  have key := freimanHom_eq_of_sum hf (s := {a₁, a₂, b₃, b₄}) (t := {b₁, b₂, a₃, a₄})
    (by intro x hx; simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
      Multiset.mem_singleton] at hx; rcases hx with rfl | rfl | rfl | rfl <;> assumption)
    (by intro x hx; simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
      Multiset.mem_singleton] at hx; rcases hx with rfl | rfl | rfl | rfl <;> assumption)
    (by simp) (by simp)
    (by simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
        linear_combination he)
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton] at key
  linear_combination -key

/-- Differences: `f a − f a′ = ψ(a − a′)` for all `a, a′ ∈ A`. -/
theorem quadSumExt_sub {N : Nat} {A : Finset (ZMod N)} {f : ZMod N → ZMod N}
    (hf : FreimanHom 4 A f) {a a' : ZMod N} (ha : a ∈ A) (ha' : a' ∈ A) :
    quadSumExt A f (a - a') = f a - f a' := by
  have h := quadSumExt_spec hf ha ha' ha' ha'
  rw [show a + a' - a' - a' = a - a' by ring] at h
  rw [h]; ring

theorem quadSumExt_zero {N : Nat} {A : Finset (ZMod N)} {f : ZMod N → ZMod N}
    (hf : FreimanHom 4 A f) (hA : A.Nonempty) : quadSumExt A f 0 = 0 := by
  obtain ⟨a, ha⟩ := hA
  have h := quadSumExt_sub hf ha ha
  rw [sub_self, sub_self] at h
  exact h

/-- The extension is Freiman-linear on the four-term sums. -/
theorem quadSumExt_freimanLinear {N : Nat} {A : Finset (ZMod N)} {f : ZMod N → ZMod N}
    (hf : FreimanHom 8 A f) (S : Finset (ZMod N)) (hS : ∀ x ∈ S, x ∈ quadSumSet A) :
    IsFreimanLinearOn S (quadSumExt A f) := by
  have hf4 : FreimanHom 4 A f := IsAddFreimanHom.mono (by decide : 4 ≤ 8) hf
  intro y₁ y₂ y₃ y₄ hy₁ hy₂ hy₃ hy₄ he
  obtain ⟨a₁, h₁, a₂, h₂, a₃, h₃, a₄, h₄, rfl⟩ := hS y₁ hy₁
  obtain ⟨b₁, g₁, b₂, g₂, b₃, g₃, b₄, g₄, rfl⟩ := hS y₂ hy₂
  obtain ⟨c₁, k₁, c₂, k₂, c₃, k₃, c₄, k₄, rfl⟩ := hS y₃ hy₃
  obtain ⟨d₁, l₁, d₂, l₂, d₃, l₃, d₄, l₄, rfl⟩ := hS y₄ hy₄
  rw [quadSumExt_spec hf4 h₁ h₂ h₃ h₄, quadSumExt_spec hf4 g₁ g₂ g₃ g₄,
    quadSumExt_spec hf4 k₁ k₂ k₃ k₄, quadSumExt_spec hf4 l₁ l₂ l₃ l₄]
  have key := freimanHom_eq_of_sum hf
    (s := {a₁, a₂, b₁, b₂, c₃, c₄, d₃, d₄}) (t := {c₁, c₂, d₁, d₂, a₃, a₄, b₃, b₄})
    (by intro x hx; simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
      Multiset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
    (by intro x hx; simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
      Multiset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
    (by simp) (by simp)
    (by simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
        linear_combination he)
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton] at key
  linear_combination key

/-- **Lemma 7.8 at Sanders strength.** -/
theorem sanders_linear_part {N : Nat} [NeZero N] (A : Finset (ZMod N)) (f : ZMod N → ZMod N)
    (hf : FreimanHom 8 A f) {p : Real} (hp : 0 ≤ p)
    (hA : Real.exp (-p) * N ≤ (A.card : Real)) :
    ∃ (Γ : Finset (ZMod N)) (ρ : Real) (ψ : ZMod N → ZMod N),
      (Γ.card : Real) ≤ 1 + OAI.Erdos3.CyclicCrootSisask.quarticBogolyubovConstant * (p + 1) ^ 4 ∧
      Real.exp (-(OAI.Erdos3.CyclicCrootSisask.quarticBogolyubovConstant * (p + 1))) /
          (2 * Real.pi) ≤ ρ ∧ 0 < ρ ∧
      IsFreimanLinearOn (bohr Γ ρ) ψ ∧ ψ 0 = 0 ∧
      ∀ a ∈ A, ∀ a' ∈ A, f a - f a' = ψ (a - a') := by
  have hf4 : FreimanHom 4 A f := IsAddFreimanHom.mono (by decide : 4 ≤ 8) hf
  have hApos : (0 : Real) < A.card :=
    (mul_pos (Real.exp_pos _) (by exact_mod_cast NeZero.pos N)).trans_le hA
  have hAne : A.Nonempty := Finset.card_pos.mp (by exact_mod_cast hApos)
  obtain ⟨R, -, hRpos, -, hrank, hwidth, hsub⟩ :=
    OAI.Erdos3.CyclicCrootSisask.exists_quartic_bogolyubov A hp hA
  refine ⟨R.frequencies, R.radius / (2 * Real.pi), quadSumExt A f, hrank, ?_, by positivity, ?_,
    quadSumExt_zero hf4 hAne, fun a ha a' ha' => (quadSumExt_sub hf4 ha ha').symm⟩
  · exact div_le_div_of_nonneg_right hwidth (by positivity)
  · apply quadSumExt_freimanLinear hf
    intro x hx
    have hx' := hsub (bohr_subset_oai_carrier R hx)
    rw [two_nsmul] at hx'
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.mp hx'
    obtain ⟨a₁, h₁, a₂, h₂, rfl⟩ := Finset.mem_add.mp hu
    obtain ⟨a₃, h₃, a₄, h₄, rfl⟩ := Finset.mem_add.mp hv
    exact ⟨a₁, h₁, a₂, h₂, a₃, h₃, a₄, h₄, by ring⟩

end LeanProofs.GowersSzemeredi
