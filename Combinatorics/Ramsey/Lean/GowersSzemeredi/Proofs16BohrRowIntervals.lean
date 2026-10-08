import GowersSzemeredi.Proofs16BohrDoubling

/-! Bohr conditions along a slow progression cut out an interval.

Along `x₀ + i d`, the centered value of `γ (x₀ + i d)` moves by the
centered value `c` of `γ d` at each step. While nothing wraps around modulo
`N`, it is an arithmetic progression in `ℤ`. So the set of `i` where it
stays in `[−ρN, ρN]` is convex: `|·|` is convex along arithmetic
progressions.

* `valMinAbs_add_of_small`: no wrap-around when `2 (|vma x| + |vma δ|) < N`.
* `bohr_row_convex`: if `2 (ρN + L |vma(γ d)|) < N` for every `γ ∈ K`, then
  the set of `i < L` with `x₀ + i d ∈ B(K;ρ)` is an interval.

Research notes J.2 need this: every row of `V ∩ cell` is an interval, so
`V ∩ cell` is a staircase, coverable by a chain of overlapping boxes
(`freiman_bihom_biaffine_on_chain`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- No wrap-around for small centered values. -/
theorem valMinAbs_add_of_small {N : Nat} [NeZero N] (x δ : ZMod N)
    (h : 2 * (|x.valMinAbs| + |δ.valMinAbs|) < (N : Int)) :
    (x + δ).valMinAbs = x.valMinAbs + δ.valMinAbs := by
  rw [ZMod.valMinAbs_spec]
  refine ⟨by simp [ZMod.coe_valMinAbs], ?_⟩
  have h1 := abs_add_le x.valMinAbs δ.valMinAbs
  constructor
  · have := neg_abs_le (x.valMinAbs + δ.valMinAbs); linarith
  · have := le_abs_self (x.valMinAbs + δ.valMinAbs); linarith

/-- Along a slow progression the centered values form an arithmetic
progression, starting from any index where the value is in the band. -/
theorem valMinAbs_along_progression {N : Nat} [NeZero N] (u c : ZMod N) (ρN : Int) (L : Nat)
    (_hρ : 0 ≤ ρN) (hband : 2 * (ρN + L * |c.valMinAbs|) < (N : Int))
    (i₁ : Nat) (hstart : |(u + (i₁ : ZMod N) * c).valMinAbs| ≤ ρN) :
    ∀ k, k ≤ L → (u + ((i₁ + k : Nat) : ZMod N) * c).valMinAbs =
      (u + (i₁ : ZMod N) * c).valMinAbs + k * c.valMinAbs := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hprev := ih (by omega)
    have hrw : u + ((i₁ + (k + 1) : Nat) : ZMod N) * c = (u + ((i₁ + k : Nat) : ZMod N) * c) + c := by
      push_cast; ring
    rw [hrw, valMinAbs_add_of_small, hprev]
    · push_cast; ring
    · rw [hprev]
      have hc0 : 0 ≤ |c.valMinAbs| := abs_nonneg _
      have hb1 : |(u + (i₁ : ZMod N) * c).valMinAbs + (k : Int) * c.valMinAbs| ≤
          ρN + k * |c.valMinAbs| := by
        calc _ ≤ |(u + (i₁ : ZMod N) * c).valMinAbs| + |(k : Int) * c.valMinAbs| := abs_add_le _ _
          _ = |(u + (i₁ : ZMod N) * c).valMinAbs| + k * |c.valMinAbs| := by
              rw [abs_mul, abs_of_nonneg (by positivity : (0 : Int) ≤ k)]
          _ ≤ ρN + k * |c.valMinAbs| := by linarith
      have hkL : (k : Int) + 1 ≤ L := by exact_mod_cast hk
      nlinarith

/-- `|·|` is convex along arithmetic progressions in `ℤ`. -/
theorem int_abs_le_of_ends {a c : Int} {B : Int} {m n k : Int} (hk1 : m ≤ k) (hk2 : k ≤ n)
    (hm : |a + m * c| ≤ B) (hn : |a + n * c| ≤ B) : |a + k * c| ≤ B := by
  rw [abs_le] at hm hn ⊢
  rcases le_total 0 c with hc | hc
  · constructor <;> nlinarith
  · constructor <;> nlinarith

/-- **Bohr rows are intervals.** -/
theorem bohr_row_convex {N : Nat} [NeZero N] (K : Finset (ZMod N)) {ρ : Real}
    (x₀ d : ZMod N) (L : Nat)
    (hslow : ∀ γ ∈ K, 2 * ((⌊ρ * N⌋ : Int) + L * |(γ * d).valMinAbs|) < (N : Int))
    (hρ : 0 ≤ ρ) {i₁ i₂ i : Nat} (h1 : i₁ ≤ i) (h2 : i ≤ i₂) (hL : i₂ ≤ i₁ + L)
    (hi₁ : x₀ + (i₁ : ZMod N) * d ∈ bohr K ρ) (hi₂ : x₀ + (i₂ : ZMod N) * d ∈ bohr K ρ) :
    x₀ + (i : ZMod N) * d ∈ bohr K ρ := by
  unfold bohr at hi₁ hi₂ ⊢
  obtain ⟨_, hi₁⟩ := Finset.mem_filter.mp hi₁
  obtain ⟨_, hi₂⟩ := Finset.mem_filter.mp hi₂
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun γ hγ => ?_⟩
  -- integer form of the band condition
  have hband : ∀ y : ZMod N, (centeredAbs y : Real) ≤ ρ * N ↔ |y.valMinAbs| ≤ ⌊ρ * N⌋ := by
    intro y
    unfold centeredAbs
    have e : ((|y.valMinAbs| : Int) : Real) = ((y.valMinAbs.natAbs : Nat) : Real) := by
      rw [Nat.cast_natAbs]
    constructor
    · intro hy
      rw [Int.le_floor, e]; exact hy
    · intro hy
      rw [Int.le_floor, e] at hy; exact hy
  have hρN : (0 : Int) ≤ ⌊ρ * N⌋ := Int.floor_nonneg.mpr (by positivity)
  set u : ZMod N := γ * x₀
  set c : ZMod N := γ * d
  have hval : ∀ j : Nat, γ * (x₀ + (j : ZMod N) * d) = u + (j : ZMod N) * c := by
    intro j; simp only [u, c]; ring
  have hs₁ := (hband _).mp (hi₁ γ hγ)
  rw [hval] at hs₁
  have hprog := valMinAbs_along_progression u c ⌊ρ * N⌋ L hρN (hslow γ hγ) i₁ hs₁
  have hs₂ := (hband _).mp (hi₂ γ hγ)
  rw [hval] at hs₂
  have e₂ := hprog (i₂ - i₁) (by omega)
  have e := hprog (i - i₁) (by omega)
  rw [show i₁ + (i₂ - i₁) = i₂ by omega] at e₂
  rw [show i₁ + (i - i₁) = i by omega] at e
  rw [hval, hband, e]
  rw [e₂] at hs₂
  have hs₁' : |(u + (i₁ : ZMod N) * c).valMinAbs + ((0 : Nat) : Int) * c.valMinAbs| ≤ ⌊ρ * N⌋ := by
    simpa using hs₁
  exact int_abs_le_of_ends (m := ((0 : Nat) : Int)) (n := ((i₂ - i₁ : Nat) : Int))
    (by positivity) (by exact_mod_cast (show i - i₁ ≤ i₂ - i₁ by omega)) hs₁' hs₂

end LeanProofs.GowersSzemeredi
