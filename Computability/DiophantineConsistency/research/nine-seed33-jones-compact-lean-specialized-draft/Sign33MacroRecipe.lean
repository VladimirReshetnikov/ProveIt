import DiophantineConsistency.Sign33MacroLanguage

/-! Generated source only; neither target below is proved. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroRecipe
open Sign33MacroLanguage

def recipe : Dag 45 := by
  let d0 : Dag 0 := .nil
  let d1 : Dag 1 := .snoc d0 (.add (.add (.fixedY) (.constant (1 : Int))) (.input ⟨0, by decide⟩))
  let d2 : Dag 2 := .snoc d1 (.pow (.ref ⟨0, by decide⟩) (.lit 5))
  let d3 : Dag 3 := .snoc d2 (.pow (.ref ⟨1, by decide⟩) (.pow (.lit 5) (.lit 34)))
  let d4 : Dag 4 := .snoc d3 (.pow (.ref ⟨2, by decide⟩) (.lit 16))
  let d5 : Dag 5 := .snoc d4 (.sumStar (.mul (.add (.fixedZ) (.pcoef)) (.pow (.ref ⟨1, by decide⟩) (.sub (.pow (.lit 5) (.lit 34)) (.expo)))))
  let d6 : Dag 6 := .snoc d5 (.sumRange (.lit 33) (.pow (.ref ⟨1, by decide⟩) (.pow (.lit 5) (.add (.index) (.lit 1)))))
  let d7 : Dag 7 := .snoc d6 (.sumRange (.mul (.lit 4) (.pow (.lit 5) (.lit 34))) (.pow (.ref ⟨1, by decide⟩) (.index)))
  let d8 : Dag 8 := .snoc d7 (.add (.input ⟨1, by decide⟩) (.constant (1 : Int)))
  let d9 : Dag 9 := .snoc d8 (.sub (.ref ⟨1, by decide⟩) (.mul (.constant (2 : Int)) (.fixedZ)))
  let d10 : Dag 10 := .snoc d9 (.mul (.mul (.constant (32 : Int)) (.ref ⟨0, by decide⟩)) (.pow (.ref ⟨1, by decide⟩) (.pow (.lit 5) (.lit 33))))
  let d11 : Dag 11 := .snoc d10 (.add (.mul (.add (.add (.add (.ref ⟨7, by decide⟩) (.mul (.ref ⟨4, by decide⟩) (.pow (.ref ⟨2, by decide⟩) (.lit 3)))) (.mul (.ref ⟨5, by decide⟩) (.pow (.ref ⟨2, by decide⟩) (.lit 5)))) (.mul (.add (.add (.mul (.mul (.constant (2 : Int)) (.sub (.ref ⟨4, by decide⟩) (.mul (.fixedZ) (.ref ⟨6, by decide⟩)))) (.pow (.add (.add (.constant (1 : Int)) (.ref ⟨1, by decide⟩)) (.ref ⟨7, by decide⟩)) (.lit 4))) (.mul (.ref ⟨6, by decide⟩) (.ref ⟨1, by decide⟩))) (.mul (.mul (.ref ⟨6, by decide⟩) (.ref ⟨1, by decide⟩)) (.pow (.ref ⟨2, by decide⟩) (.lit 4)))) (.pow (.ref ⟨2, by decide⟩) (.lit 7)))) (.sub (.pow (.ref ⟨3, by decide⟩) (.lit 2)) (.ref ⟨3, by decide⟩))) (.mul (.add (.add (.add (.sub (.pow (.ref ⟨2, by decide⟩) (.lit 3)) (.mul (.ref ⟨0, by decide⟩) (.ref ⟨5, by decide⟩))) (.ref ⟨5, by decide⟩)) (.mul (.mul (.ref ⟨8, by decide⟩) (.ref ⟨6, by decide⟩)) (.pow (.ref ⟨2, by decide⟩) (.lit 3)))) (.mul (.sub (.ref ⟨1, by decide⟩) (.constant (2 : Int))) (.pow (.ref ⟨2, by decide⟩) (.lit 8)))) (.sub (.pow (.ref ⟨3, by decide⟩) (.lit 2)) (.constant (1 : Int)))))
  let d12 : Dag 12 := .snoc d11 (.add (.input ⟨2, by decide⟩) (.constant (1 : Int)))
  let d13 : Dag 13 := .snoc d12 (.add (.input ⟨3, by decide⟩) (.constant (1 : Int)))
  let d14 : Dag 14 := .snoc d13 (.add (.input ⟨4, by decide⟩) (.constant (1 : Int)))
  let d15 : Dag 15 := .snoc d14 (.input ⟨5, by decide⟩)
  let d16 : Dag 16 := .snoc d15 (.add (.input ⟨6, by decide⟩) (.constant (1 : Int)))
  let d17 : Dag 17 := .snoc d16 (.add (.input ⟨7, by decide⟩) (.constant (1 : Int)))
  let d18 : Dag 18 := .snoc d17 (.input ⟨8, by decide⟩)
  let d19 : Dag 19 := .snoc d18 (.mul (.pow (.ref ⟨3, by decide⟩) (.lit 2)) (.ref ⟨13, by decide⟩))
  let d20 : Dag 20 := .snoc d19 (.mul (.pow (.ref ⟨3, by decide⟩) (.lit 2)) (.ref ⟨12, by decide⟩))
  let d21 : Dag 21 := .snoc d20 (.mul (.ref ⟨10, by decide⟩) (.ref ⟨19, by decide⟩))
  let d22 : Dag 22 := .snoc d21 (.mul (.mul (.constant (2 : Int)) (.pow (.ref ⟨20, by decide⟩) (.lit 2))) (.ref ⟨18, by decide⟩))
  let d23 : Dag 23 := .snoc d22 (.add (.add (.ref ⟨10, by decide⟩) (.constant (1 : Int))) (.mul (.ref ⟨11, by decide⟩) (.sub (.ref ⟨21, by decide⟩) (.constant (1 : Int)))))
  let d24 : Dag 24 := .snoc d23 (.mul (.ref ⟨20, by decide⟩) (.add (.ref ⟨18, by decide⟩) (.constant (1 : Int))))
  let d25 : Dag 25 := .snoc d24 (.add (.mul (.constant (2 : Int)) (.ref ⟨10, by decide⟩)) (.constant (1 : Int)))
  let d26 : Dag 26 := .snoc d25 (.mul (.ref ⟨0, by decide⟩) (.ref ⟨13, by decide⟩))
  let d27 : Dag 27 := .snoc d26 (.add (.add (.ref ⟨24, by decide⟩) (.ref ⟨25, by decide⟩)) (.ref ⟨14, by decide⟩))
  let d28 : Dag 28 := .snoc d27 (.sub (.mul (.constant (4 : Int)) (.ref ⟨23, by decide⟩)) (.constant (5 : Int)))
  let d29 : Dag 29 := .snoc d28 (.sub (.mul (.mul (.constant (3 : Int)) (.ref ⟨25, by decide⟩)) (.ref ⟨26, by decide⟩)) (.mul (.constant (2 : Int)) (.sub (.pow (.ref ⟨25, by decide⟩) (.lit 2)) (.constant (1 : Int)))))
  let d30 : Dag 30 := .snoc d29 (.add (.mul (.sub (.pow (.ref ⟨23, by decide⟩) (.lit 2)) (.constant (1 : Int))) (.pow (.ref ⟨26, by decide⟩) (.lit 2))) (.constant (1 : Int)))
  let d31 : Dag 31 := .snoc d30 (.mul (.mul (.mul (.ref ⟨15, by decide⟩) (.ref ⟨27, by decide⟩)) (.ref ⟨29, by decide⟩)) (.pow (.ref ⟨26, by decide⟩) (.lit 2)))
  let d32 : Dag 32 := .snoc d31 (.add (.mul (.sub (.pow (.ref ⟨23, by decide⟩) (.lit 2)) (.constant (1 : Int))) (.pow (.ref ⟨30, by decide⟩) (.lit 2))) (.constant (1 : Int)))
  let d33 : Dag 33 := .snoc d32 (.add (.ref ⟨23, by decide⟩) (.mul (.ref ⟨31, by decide⟩) (.sub (.add (.mul (.ref ⟨26, by decide⟩) (.ref ⟨29, by decide⟩)) (.constant (1 : Int))) (.ref ⟨23, by decide⟩))))
  let d34 : Dag 34 := .snoc d33 (.add (.ref ⟨24, by decide⟩) (.mul (.ref ⟨16, by decide⟩) (.ref ⟨26, by decide⟩)))
  let d35 : Dag 35 := .snoc d34 (.add (.mul (.sub (.pow (.ref ⟨32, by decide⟩) (.lit 2)) (.constant (1 : Int))) (.pow (.ref ⟨33, by decide⟩) (.lit 2))) (.constant (1 : Int)))
  let d36 : Dag 36 := .snoc d35 (.add (.mul (.sub (.pow (.ref ⟨21, by decide⟩) (.lit 2)) (.constant (1 : Int))) (.pow (.ref ⟨22, by decide⟩) (.lit 2))) (.constant (1 : Int)))
  let d37 : Dag 37 := .snoc d36 (.mul (.mul (.ref ⟨29, by decide⟩) (.ref ⟨31, by decide⟩)) (.ref ⟨34, by decide⟩))
  let d38 : Dag 38 := .snoc d37 (.add (.pow (.ref ⟨35, by decide⟩) (.lit 2)) (.constant (2 : Int)))
  let d39 : Dag 39 := .snoc d38 (.add (.pow (.ref ⟨36, by decide⟩) (.lit 2)) (.constant (2 : Int)))
  let d40 : Dag 40 := .snoc d39 (.pow (.mul (.ref ⟨27, by decide⟩) (.ref ⟨31, by decide⟩)) (.lit 2))
  let d41 : Dag 41 := .snoc d40 (.pow (.add (.mul (.ref ⟨28, by decide⟩) (.ref ⟨31, by decide⟩)) (.mul (.ref ⟨27, by decide⟩) (.sub (.ref ⟨33, by decide⟩) (.ref ⟨26, by decide⟩)))) (.lit 2))
  let d42 : Dag 42 := .snoc d41 (.sub (.sub (.mul (.pow (.ref ⟨22, by decide⟩) (.lit 2)) (.ref ⟨9, by decide⟩)) (.mul (.mul (.constant (4 : Int)) (.pow (.sub (.ref ⟨26, by decide⟩) (.mul (.ref ⟨22, by decide⟩) (.ref ⟨19, by decide⟩))) (.lit 2))) (.ref ⟨9, by decide⟩))) (.mul (.mul (.constant (8 : Int)) (.ref ⟨7, by decide⟩)) (.pow (.ref ⟨22, by decide⟩) (.lit 2))))
  let d43 : Dag 43 := .snoc d42 (.mul (.ref ⟨39, by decide⟩) (.sub (.mul (.constant (2 : Int)) (.ref ⟨41, by decide⟩)) (.constant (1 : Int))))
  let d44 : Dag 44 := .snoc d43 (.sub (.add (.mul (.ref ⟨39, by decide⟩) (.ref ⟨17, by decide⟩)) (.ref ⟨40, by decide⟩)) (.mul (.ref ⟨42, by decide⟩) (.add (.ref ⟨40, by decide⟩) (.mul (.ref ⟨37, by decide⟩) (.ref ⟨38, by decide⟩)))))
  let d45 : Dag 45 := .snoc d44 (.sub (.pow (.sub (.add (.pow (.ref ⟨43, by decide⟩) (.lit 2)) (.mul (.pow (.ref ⟨42, by decide⟩) (.lit 2)) (.ref ⟨35, by decide⟩))) (.mul (.mul (.pow (.ref ⟨42, by decide⟩) (.lit 2)) (.pow (.ref ⟨37, by decide⟩) (.lit 2))) (.ref ⟨36, by decide⟩))) (.lit 2)) (.mul (.mul (.mul (.constant (4 : Int)) (.pow (.ref ⟨43, by decide⟩) (.lit 2))) (.pow (.ref ⟨42, by decide⟩) (.lit 2))) (.ref ⟨35, by decide⟩)))
  exact d45

/-- Open proposition: the generated graph has no unbound macro indices. -/
def WellScopedTarget : Prop := recipe.scoped = true

/-- Open proposition: compact graph evaluation equals the checked endpoint. -/
def SemanticTarget : Prop :=
  ∀ (R : Type) [CommRing R] (a : Fin 9 → R),
    recipe.values a (Fin.last 44) = Sign33IPRAEndpoint.expression.evalRing a

end DiophantineConsistency.Sign33MacroRecipe
