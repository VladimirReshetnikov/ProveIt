import PA194RelationalSourceExistential
import Foundation.Logic.Calculus

notation "⦃" x "⦄" => Multiset.cons x 0
notation "⦃" x "," y "⦄" => Multiset.cons x (Multiset.cons y 0)
namespace PA194Logic.Relational.Source
open LO LO.FirstOrder M6.PA.RelationalSource
abbrev SourceSequent := Multiset (Proposition language)
inductive SourceLK : SourceSequent → Type
| identity (r : language.Rel k) (v) : SourceLK ⦃.rel r v, .nrel r v⦄
| cut : SourceLK (Γ + ⦃φ⦄) → SourceLK (Δ + ⦃Semiformula.neg φ⦄) → SourceLK (Γ + Δ)
| contraction : SourceLK (Γ + ⦃φ, φ⦄) → SourceLK (Γ + ⦃φ⦄)
| weakening : SourceLK Γ → SourceLK (Γ + ⦃φ⦄)
| verum : SourceLK ⦃.verum⦄
| or : SourceLK (Γ + ⦃φ, ψ⦄) → SourceLK (Γ + ⦃.or φ ψ⦄)
| and : SourceLK (Γ + ⦃φ⦄) → SourceLK (Γ + ⦃ψ⦄) → SourceLK (Γ + ⦃.and φ ψ⦄)
| all {Γ : SourceSequent} {φ : Semiproposition language 1} : SourceLK (Γ.map Semiformula.shift + ⦃φ.free⦄) → SourceLK (Γ + ⦃.all φ⦄)
| exs {Γ : SourceSequent} {φ : Semiproposition language 1} {t : Semiterm language Nat 0} : SourceLK (Γ + ⦃instantiate φ t⦄) → SourceLK (Γ + ⦃.exs φ⦄)
structure Traversal (Γ : SourceSequent) where
  toList : List (Proposition language)
  coe_toList : (↑toList : SourceSequent) = Γ
noncomputable def traversal (Γ : SourceSequent) : Traversal Γ :=
  ⟨Quotient.out Γ, Quotient.out_eq Γ⟩
noncomputable def Traversal.getPreimage {Γ : SourceSequent} (tg : Traversal Γ)
    {f : Proposition language → Proposition language} {q : Proposition language}
    (h : q ∈ Γ.map f) : {p // p ∈ Γ ∧ f p = q} :=
  ⟨Classical.choose (Multiset.mem_map.mp h), Classical.choose_spec (Multiset.mem_map.mp h)⟩
/-- The existential premise uses the same one-term substitution as upstream. -/
theorem instantiate_eq_subst (p : Semiproposition language 1)
    (t : Semiterm language Nat 0) : instantiate p t = p/[t] := by
  apply congrArg (fun ω => Semiformula.rewAux ω p)
  apply congrArg Rew.subst
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rfl
#print axioms instantiate_eq_subst
end PA194Logic.Relational.Source
