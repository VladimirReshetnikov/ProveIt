import GowersSzemeredi.Proofs16ClassStepDegrees

/-! Uniform classes with split controls (Notes L.7, F1).

A `SplitUniformClass k V a D` separates the family size from the parameters:
* count `(n+1)^a · W^D` and width exponent `((n+1)^a · W^D)⁻¹`, where
  `W = splitW V θ γ ρ = V·2/(γθρ)`;
* threshold `(V·2/(γθ))^D`.

`PowerUniformClass` puts `n+1` inside the base (`uniformBase = (n+1)·W`), so
its family exponent equals its parameter degree. That is why its degrees
square from one dimension to the next (Notes L.6a). With split controls the
step sends `(a, D)` to `(a′, D′)` with `a′ = O(2^k a²)` and `D′ = O(2^k a P (a + D))`.
Both logarithms stay `O(2^k)`, which Theorem 18.2 at every length needs
(Notes L.7).

* `PowerUniformClass.toSplit`: a power class at one degree `d` is a split
  class at `a = D = d`.
* `splitUniformClass_two`: dimension two is a split class at any
  `a = D ≥ 2^130`.
* `SplitUniformClass.toPower`: a split class is a power class at degree
  `a + D`.

`splitUniformClass_two` is in `Proofs16SplitUniformClassSide`, outside the final
route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-- The parameter base `V·2/(γθρ)` of split controls. -/
def splitW (V : Real) (theta gamma rho : Real) : Real := V * (2 / (gamma * theta * rho))

/-- **A uniform class with split controls.** -/
abbrev SplitUniformClass (k : Nat) (V : Real) (a D : Nat) :=
  UniformClassWith k (fun theta gamma => (V * (2 / (gamma * theta))) ^ D)
    (fun theta gamma n rho => ((n : Real) + 1) ^ a * splitW V theta gamma rho ^ D)
    (fun theta gamma n rho => (((n : Real) + 1) ^ a * splitW V theta gamma rho ^ D)⁻¹)

theorem uniformBase_eq_split (V : Real) (n : Nat) (theta gamma rho : Real) :
    uniformBase V n theta gamma rho = ((n : Real) + 1) * splitW V theta gamma rho := by
  unfold uniformBase splitW; ring

theorem splitW_facts {V : Real} (hV : 1 ≤ V) {theta gamma rho : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho)
    (hr1 : rho ≤ 1) :
    2 ≤ splitW V theta gamma rho ∧ 2 / (gamma * theta) ≤ splitW V theta gamma rho ∧
      rho⁻¹ ≤ splitW V theta gamma rho ∧ V ≤ splitW V theta gamma rho := by
  obtain ⟨hvw, hrw, -, hVw, hw2⟩ := uniformBase_facts hV 0 hg hg1 ht ht1 hr hr1
  have h0 : uniformBase V 0 theta gamma rho = splitW V theta gamma rho := by
    rw [uniformBase_eq_split]; simp
  rw [h0] at hvw hrw hVw hw2
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  exact ⟨hw2, hvw, hrw, le_trans (le_mul_of_one_le_right (by linarith)
    (le_trans (by norm_num) hu2)) hVw⟩

/-- **A split class is a power class** at degree `a + D` in every slot. -/
def SplitUniformClass.toPower {k : Nat} {V : Real} {a D : Nat} (C : SplitUniformClass k V a D)
    (hV : 1 ≤ V) : PowerUniformClass k V (a + D) (a + D) (a + D) where
  U := C.U
  mono := C.mono
  empty := C.empty
  decomp := by
    intro theta gamma ht ht1 hg hg1 N _ _ hN Gamma hsize hprod
    refine C.decomp theta gamma ht ht1 hg hg1 N (le_trans ?_ hN) Gamma hsize hprod
    obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
    have hVu : 1 ≤ V * (2 / (gamma * theta)) :=
      one_le_mul_of_one_le_of_one_le hV (le_trans (by norm_num) hu2)
    exact pow_le_pow_right₀ hVu (by omega)
  cover := by
    intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    refine (C.cover theta gamma ht ht1 hg hg1 N n Gamma hU).weaken ?_ ?_ ?_
    · intro rho hr hr1
      obtain ⟨hw2, -, -, -⟩ := splitW_facts hV hg hg1 ht ht1 hr hr1
      have hn1 : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      show ((n : Real) + 1) ^ a * splitW V theta gamma rho ^ D ≤ uniformBase V n theta gamma rho ^ (a + D)
      rw [uniformBase_eq_split, mul_pow, pow_add, pow_add]
      have h1 : ((n : Real) + 1) ^ a ≤ ((n : Real) + 1) ^ a * ((n : Real) + 1) ^ D :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ hn1)
      have h2 : splitW V theta gamma rho ^ D ≤ splitW V theta gamma rho ^ a *
          splitW V theta gamma rho ^ D :=
        le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by linarith))
      calc ((n : Real) + 1) ^ a * splitW V theta gamma rho ^ D
          ≤ (((n : Real) + 1) ^ a * ((n : Real) + 1) ^ D) *
              (splitW V theta gamma rho ^ a * splitW V theta gamma rho ^ D) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = _ := by ring
    · intro rho hr hr1
      have h2 := uniformBase_two_le hV n ht ht1 hg hg1 hr hr1
      positivity
    · intro rho hr hr1
      obtain ⟨hw2, -, -, -⟩ := splitW_facts hV hg hg1 ht ht1 hr hr1
      have hn1 : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      show (uniformBase V n theta gamma rho ^ (a + D))⁻¹ ≤
        (((n : Real) + 1) ^ a * splitW V theta gamma rho ^ D)⁻¹
      refine inv_anti₀ (by positivity) ?_
      rw [uniformBase_eq_split, mul_pow, pow_add, pow_add]
      have h1 : ((n : Real) + 1) ^ a ≤ ((n : Real) + 1) ^ a * ((n : Real) + 1) ^ D :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ hn1)
      have h2 : splitW V theta gamma rho ^ D ≤ splitW V theta gamma rho ^ a *
          splitW V theta gamma rho ^ D :=
        le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by linarith))
      calc ((n : Real) + 1) ^ a * splitW V theta gamma rho ^ D
          ≤ (((n : Real) + 1) ^ a * ((n : Real) + 1) ^ D) *
              (splitW V theta gamma rho ^ a * splitW V theta gamma rho ^ D) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = _ := by ring

/-- **A power class at one degree is a split class** at that degree:
`uniformBase^d = (n+1)^d · W^d`. -/
def PowerUniformClass.toSplit {k : Nat} {V : Real} {d : Nat} (C : PowerUniformClass k V d d d) :
    SplitUniformClass k V d d where
  U := C.U
  mono := C.mono
  empty := C.empty
  decomp := C.decomp
  cover := by
    intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    have h := C.cover theta gamma ht ht1 hg hg1 N n Gamma hU
    have hfun : ∀ rho, uniformBase V n theta gamma rho ^ d =
        ((n : Real) + 1) ^ d * splitW V theta gamma rho ^ d := fun rho => by
      rw [uniformBase_eq_split, mul_pow]
    simp only [hfun] at h
    exact h

end LeanProofs.GowersSzemeredi
