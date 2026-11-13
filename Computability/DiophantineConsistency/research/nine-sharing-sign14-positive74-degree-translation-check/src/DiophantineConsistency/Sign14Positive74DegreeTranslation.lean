import DiophantineConsistency.Sign14Positive74DegreeSubstBound

/-! SOURCE ONLY: uniform affine translation preserves total degree. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74DegreeTranslation
open MvPolynomial Sign14Positive74DegreeSubstBound

def plusOne {σ : Type*} (i : σ) : MvPolynomial σ ℤ := MvPolynomial.X i + 1
def minusOne {σ : Type*} (i : σ) : MvPolynomial σ ℤ := MvPolynomial.X i - 1
def translate {σ : Type*} (p : MvPolynomial σ ℤ) : MvPolynomial σ ℤ :=
  MvPolynomial.eval₂ MvPolynomial.C plusOne p
def untranslate {σ : Type*} (p : MvPolynomial σ ℤ) : MvPolynomial σ ℤ :=
  MvPolynomial.eval₂ MvPolynomial.C minusOne p

theorem plus_degree {σ : Type*} (i : σ) : (plusOne i).totalDegree ≤ 1 := by
  calc
    (plusOne i).totalDegree ≤ max (MvPolynomial.X i : MvPolynomial σ ℤ).totalDegree (1 : MvPolynomial σ ℤ).totalDegree :=
      MvPolynomial.totalDegree_add _ _
    _ = 1 := by simp

theorem minus_degree {σ : Type*} (i : σ) : (minusOne i).totalDegree ≤ 1 := by
  calc
    (minusOne i).totalDegree ≤ max (MvPolynomial.X i : MvPolynomial σ ℤ).totalDegree (1 : MvPolynomial σ ℤ).totalDegree :=
      MvPolynomial.totalDegree_sub _ _
    _ = 1 := by simp

theorem untranslate_translate {σ : Type*} (p : MvPolynomial σ ℤ) : untranslate (translate p) = p := by
  unfold untranslate translate
  calc
    MvPolynomial.eval₂ MvPolynomial.C minusOne (MvPolynomial.eval₂ MvPolynomial.C plusOne p) =
        MvPolynomial.eval₂ MvPolynomial.C (fun i => MvPolynomial.eval₂ MvPolynomial.C minusOne (plusOne i)) p :=
          (MvPolynomial.eval₂_assoc MvPolynomial.C minusOne plusOne p).symm
    _ = MvPolynomial.eval₂ MvPolynomial.C MvPolynomial.X p := by
      congr 1
      funext i
      simp [plusOne, minusOne]
    _ = p := MvPolynomial.eval₂_eta p

theorem translate_degree {σ : Type*} (p : MvPolynomial σ ℤ) : (translate p).totalDegree = p.totalDegree := by
  have h₁ : (translate p).totalDegree ≤ p.totalDegree := eval₂_degree_le p plusOne plus_degree
  have h₂ : (untranslate (translate p)).totalDegree ≤ (translate p).totalDegree :=
    eval₂_degree_le (translate p) minusOne minus_degree
  rw [untranslate_translate] at h₂
  exact le_antisymm h₁ h₂
end DiophantineConsistency.Sign14Positive74DegreeTranslation
#print axioms DiophantineConsistency.Sign14Positive74DegreeTranslation.translate_degree
