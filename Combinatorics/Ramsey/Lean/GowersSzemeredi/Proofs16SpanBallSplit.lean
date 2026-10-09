import GowersSzemeredi.Proofs16IndependenceCount
import GowersSzemeredi.Proofs16BoundedFrequencySpan
import GowersSzemeredi.Proofs16Trapezoid

/-! Span balls: membership with plain coefficient functions, the conversion from
`boundedFrequencySpan`, and the splitting over a union of frequency sets.

* `mem_spanBall_iff`: `ξ ∈ spanBall Γ R` exactly when `ξ = ∑_{γ∈Γ} n(γ)·γ`
  for some `n : G → ℤ` with `|n(γ)| ≤ R` on `Γ`.
* `boundedFrequencySpan_subset_spanBall`: in `ℤ/N`, a combination with
  centered coefficients of size at most `R` lies in `spanBall K R`, via
  `valMinAbs`.
* `spanBall_union_split`: `spanBall (Γ₁ ∪ Γ₂) R ⊆ spanBall Γ₁ R + spanBall Γ₂ R`.
* `neg_mem_spanBall`, `spanBall_mono`: span balls are symmetric and grow
  with the radius.
* `escape_split`: a frequency in both bounded spans of `Γ_{x+a} ∪ Γ_x` and
  `Γ_{y+a} ∪ Γ_y` is `ξ₀ − ξ₁ = ξ₂ − ξ₃` with each piece in its own ball.

In Claim 9.4 the escaping frequency of `escape_frequency` lies in the
bounded span of `Γ_{x+a} ∪ Γ_x`. These lemmas split it as `ξ₀ + ξ₁′`, the
decomposition `claim_9_4_core` takes. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem mem_spanBall_iff {G : Type*} [AddCommGroup G] (Γ : Finset G) (R : Nat) (ξ : G) :
    ξ ∈ spanBall Γ R ↔ ∃ n : G → Int, (∀ γ ∈ Γ, -(R : Int) ≤ n γ ∧ n γ ≤ R) ∧
      ξ = ∑ γ ∈ Γ, n γ • γ := by
  constructor
  · intro h
    obtain ⟨n', hn', rfl⟩ := Finset.mem_image.mp h
    refine ⟨fun γ => if hγ : γ ∈ Γ then n' ⟨γ, hγ⟩ else 0, ?_, ?_⟩
    · intro γ hγ
      dsimp only
      rw [dif_pos hγ]
      exact Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hn' ⟨γ, hγ⟩)
    · rw [← Finset.sum_coe_sort Γ]
      refine Finset.sum_congr rfl fun γ _ => ?_
      dsimp only
      rw [dif_pos γ.2]
  · rintro ⟨n, hn, rfl⟩
    refine Finset.mem_image.mpr ⟨fun γ => n γ, ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro γ
      exact Finset.mem_Icc.mpr (hn γ γ.2)
    · exact Finset.sum_coe_sort Γ (fun γ => n γ • γ)

theorem boundedFrequencySpan_subset_spanBall {N : Nat} [NeZero N] (K : Finset (ZMod N))
    (R : Nat) : boundedFrequencySpan (fun k : K => (k : ZMod N)) R ⊆ spanBall K R := by
  intro ξ hξ
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hξ
  rw [mem_spanBall_iff]
  refine ⟨fun γ => if h : γ ∈ K then ((v ⟨γ, h⟩ : ZMod N)).valMinAbs else 0, ?_, ?_⟩
  · intro γ hγ
    dsimp only
    rw [dif_pos hγ]
    have hv := (Finset.mem_filter.mp (v ⟨γ, hγ⟩).2).2
    unfold centeredAbs at hv
    constructor <;> omega
  · rw [← Finset.sum_coe_sort K]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp only
    rw [dif_pos k.2, zsmul_eq_mul, ZMod.coe_valMinAbs]

theorem spanBall_union_split {G : Type*} [AddCommGroup G] [DecidableEq G] (Γ₁ Γ₂ : Finset G) (R : Nat)
    {ξ : G} (hξ : ξ ∈ spanBall (Γ₁ ∪ Γ₂) R) :
    ∃ α ∈ spanBall Γ₁ R, ∃ β ∈ spanBall Γ₂ R, ξ = α + β := by
  obtain ⟨n, hn, rfl⟩ := (mem_spanBall_iff _ R ξ).mp hξ
  refine ⟨∑ γ ∈ Γ₁, n γ • γ, (mem_spanBall_iff _ R _).mpr ⟨n, fun γ hγ =>
      hn γ (Finset.mem_union_left _ hγ), rfl⟩,
    ∑ γ ∈ Γ₂, (if γ ∈ Γ₁ then 0 else n γ) • γ, (mem_spanBall_iff _ R _).mpr
      ⟨fun γ => if γ ∈ Γ₁ then 0 else n γ, fun γ hγ => ?_, rfl⟩, ?_⟩
  · by_cases h : γ ∈ Γ₁
    · simp only [if_pos h]; omega
    · simp only [if_neg h]; exact hn γ (Finset.mem_union_right _ hγ)
  · have hβ : (∑ γ ∈ Γ₂, (if γ ∈ Γ₁ then 0 else n γ) • γ) = ∑ γ ∈ Γ₂ \ Γ₁, n γ • γ := by
      rw [Finset.sdiff_eq_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun γ _ => ?_
      split_ifs <;> simp_all
    rw [hβ, ← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_self_eq_union]

theorem neg_mem_spanBall {G : Type*} [AddCommGroup G] {Γ : Finset G} {R : Nat} {ξ : G}
    (hξ : ξ ∈ spanBall Γ R) : -ξ ∈ spanBall Γ R := by
  obtain ⟨n, hn, rfl⟩ := (mem_spanBall_iff _ R ξ).mp hξ
  refine (mem_spanBall_iff _ R _).mpr ⟨fun γ => -n γ, fun γ hγ => ?_, ?_⟩
  · have := hn γ hγ
    show -(R : Int) ≤ -n γ ∧ -n γ ≤ R
    constructor <;> omega
  · rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun γ _ => (neg_smul (n γ) γ).symm

theorem spanBall_mono {G : Type*} [AddCommGroup G] (Γ : Finset G) {R R' : Nat}
    (h : R ≤ R') : spanBall Γ R ⊆ spanBall Γ R' := by
  intro ξ hξ
  obtain ⟨n, hn, rfl⟩ := (mem_spanBall_iff _ R ξ).mp hξ
  refine (mem_spanBall_iff _ R' _).mpr ⟨n, fun γ hγ => ?_, rfl⟩
  have := hn γ hγ
  have hR : (R : Int) ≤ R' := by exact_mod_cast h
  constructor <;> omega

/-- **The per-triple splitting of Claim 9.4.** A frequency in both bounded
spans of `Γ_{x+a} ∪ Γ_x` and `Γ_{y+a} ∪ Γ_y` is `ξ₀ − ξ₁ = ξ₂ − ξ₃` with
each `ξ_i` in the span ball of its own set, at the common radius `R`. -/
theorem escape_split {N : Nat} [NeZero N] (Γ : ZMod N → Finset (ZMod N)) (x y a : ZMod N)
    {R₁ R₂ R : Nat} (h₁ : R₁ ≤ R) (h₂ : R₂ ≤ R) {ξ : ZMod N}
    (hK : ξ ∈ boundedFrequencySpan (fun k : (Γ (x + a) ∪ Γ x : Finset (ZMod N)) =>
      (k : ZMod N)) R₁)
    (hL : ξ ∈ boundedFrequencySpan (fun l : (Γ (y + a) ∪ Γ y : Finset (ZMod N)) =>
      (l : ZMod N)) R₂) :
    ∃ ξ₀ ∈ spanBall (Γ (x + a)) R, ∃ ξ₁ ∈ spanBall (Γ x) R,
      ∃ ξ₂ ∈ spanBall (Γ (y + a)) R, ∃ ξ₃ ∈ spanBall (Γ y) R,
        ξ = ξ₀ - ξ₁ ∧ ξ₀ - ξ₁ = ξ₂ - ξ₃ := by
  obtain ⟨α, hα, β, hβ, hαβ⟩ :=
    spanBall_union_split (Γ (x + a)) (Γ x) R₁
      (boundedFrequencySpan_subset_spanBall (Γ (x + a) ∪ Γ x) R₁ hK)
  obtain ⟨α', hα', β', hβ', hαβ'⟩ :=
    spanBall_union_split (Γ (y + a)) (Γ y) R₂
      (boundedFrequencySpan_subset_spanBall (Γ (y + a) ∪ Γ y) R₂ hL)
  refine ⟨α, spanBall_mono _ h₁ hα, -β, neg_mem_spanBall (spanBall_mono _ h₁ hβ),
    α', spanBall_mono _ h₂ hα', -β', neg_mem_spanBall (spanBall_mono _ h₂ hβ'), ?_, ?_⟩
  · rw [sub_neg_eq_add]; exact hαβ
  · rw [sub_neg_eq_add, sub_neg_eq_add, ← hαβ, ← hαβ']

end LeanProofs.GowersSzemeredi
