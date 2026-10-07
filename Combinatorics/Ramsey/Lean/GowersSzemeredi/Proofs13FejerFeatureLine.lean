import GowersSzemeredi.Proofs13FejerCoefficientBox
import GowersSzemeredi.Proofs13FejerRegularity

/-! Outside the explicitly counted coefficient-box exceptional set, all
short scalar-feature relations lie on the intended line. This discharges
the structural regularity conditions used by Fejer selection. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def balancedFeatureCoefficient {I R : Type*} [Neg R] [One R] (sign : I → R) :
    Option I × Bool → R :=
  balancedRelationCoefficient (fun j => match j with | none => 1 | some i => -sign i)
    (fun j => match j with | none => -1 | some i => sign i)

theorem balancedFeatureCoefficient_ne_zero {I R : Type*} [Ring R] [Nontrivial R]
    (sign : I → R) (hsign : ∀ i, sign i ≠ 0) (j : Option I × Bool) :
    balancedFeatureCoefficient sign j ≠ 0 := by
  rcases j with ⟨j, b⟩
  cases j <;> cases b <;> simp [balancedFeatureCoefficient, balancedRelationCoefficient, hsign]

theorem fejerFeature_regular_line {N L : Nat} [NeZero N] [Fact N.Prime]
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (sign : I → ZMod N) (hsign : ∀ i, sign i ≠ 0)
    (x : I → ZMod N) (y : Option I → ZMod N) (h : ZMod N)
    (hregular : ¬ fejerFeatureExceptional (L := L) sign (balancedFeatureAssignment x y h))
    (v : (Option I × Bool) → Fin L × Fin L)
    (hf : fejerPairRelation v (fun j =>
      (balancedFeatureVertex sign x y h j).1 * (balancedFeatureVertex sign x y h j).2) = 0) :
    ∃ c : ZMod N, ∀ j, ((v j).1 - (v j).2 : ZMod N) = c * balancedFeatureCoefficient sign j := by
  classical
  let a : (Option I × Bool) → Fin (2 * L) := fun j => fejerCoefficientBoxIndex (v j)
  let u₀ := fun j => fejerBoxCoefficient (N := N) (a (j, false))
  let u₁ := fun j => fejerBoxCoefficient (N := N) (a (j, true))
  have hcoeff (j : Option I × Bool) : balancedRelationCoefficient u₀ u₁ j =
      ((v j).1 - (v j).2 : ZMod N) := by
    rcases j with ⟨j, b⟩
    cases b <;> simp only [balancedRelationCoefficient, Bool.false_eq_true, if_false, if_true] <;>
      exact fejerCoefficientBox_difference _
  have heval : MvPolynomial.eval (balancedFeatureAssignment x y h)
      (balancedFeaturePolynomial sign u₀ u₁) = 0 := by
    rw [← balancedFeatureVertex_polynomial]
    simp_rw [hcoeff]
    exact hf
  have hp : balancedFeaturePolynomial sign u₀ u₁ = 0 := by
    by_contra hne
    exact hregular ⟨a, hne, heval⟩
  obtain ⟨c, h₀, h₁, h₀s, h₁s⟩ := (balancedFeaturePolynomial_eq_zero_iff sign hsign u₀ u₁).mp hp
  refine ⟨c, ?_⟩
  intro j
  rw [← hcoeff]
  rcases j with ⟨j, b⟩
  cases j <;> cases b <;>
    simp [balancedFeatureCoefficient, balancedRelationCoefficient, h₀, h₁, h₀s, h₁s, mul_comm]

theorem fejerFeature_regular_injective {N L : Nat} [NeZero N] [Fact N.Prime]
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (hL : 2 ≤ L) (sign : I → ZMod N) (hsign : ∀ i, sign i ≠ 0)
    (x : I → ZMod N) (y : Option I → ZMod N) (h : ZMod N)
    (hregular : ¬ fejerFeatureExceptional (L := L) sign (balancedFeatureAssignment x y h)) :
    Function.Injective (balancedFeatureVertex sign x y h) := by
  have hI : 2 < Fintype.card (Option I × Bool) := by
    have hi : 0 < Fintype.card I := Fintype.card_pos
    simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_bool]
    omega
  apply fejer_vertex_injective_of_feature_line hL hI (balancedFeatureVertex sign x y h)
    (fun z => z.1 * z.2) (balancedFeatureCoefficient sign)
    (balancedFeatureCoefficient_ne_zero sign hsign)
  exact fejerFeature_regular_line sign hsign x y h hregular

theorem fejerFeature_regular_diagonal {N L : Nat} [NeZero N] [Fact N.Prime]
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (hLN : L ≤ N) (sign : I → ZMod N) (hsign : ∀ i, sign i ≠ 0)
    (x : I → ZMod N) (y : Option I → ZMod N) (h : ZMod N)
    (phi : ZMod N × ZMod N → ZMod N)
    (hregular : ¬ fejerFeatureExceptional (L := L) sign (balancedFeatureAssignment x y h))
    (hphase : ∑ j, balancedFeatureCoefficient sign j * phi (balancedFeatureVertex sign x y h j) ≠ 0) :
    ∀ v : (Option I × Bool) → Fin L × Fin L,
      (fejerPairRelation v (phi ∘ balancedFeatureVertex sign x y h) = 0 ∧
        fejerPairRelation v (fun j =>
          (balancedFeatureVertex sign x y h j).1 * (balancedFeatureVertex sign x y h j).2) = 0) ↔
      ∀ j, (v j).1 = (v j).2 := by
  apply fejer_diagonal_of_feature_line hLN (balancedFeatureCoefficient sign)
    (phi ∘ balancedFeatureVertex sign x y h) _ hphase
  exact fejerFeature_regular_line sign hsign x y h hregular

end LeanProofs.GowersSzemeredi
