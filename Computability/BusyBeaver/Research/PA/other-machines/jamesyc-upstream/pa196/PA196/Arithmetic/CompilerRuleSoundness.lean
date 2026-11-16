module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import PA196.Arithmetic.CompilerRecursive
@[expose] public section
open M6.Arithmetic.PA
namespace PA196.Arithmetic.CompilerSoundness
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open CommandStep
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
private theorem checkTag (k : Nat) (yes no : Scalar.Expr) (p t d : V) :
    Scalar.eval (.ifEq .tag (.num k) yes no) p t d =
      if t=(k:V) then Scalar.eval yes p t d else Scalar.eval no p t d := rfl
private theorem wordTag (k : Nat) (yes no : WordExpression.Expr) (p t d : V) :
    WordExpression.eval (.ifEq .tag (.num k) yes no) p t d =
      if t=(k:V) then WordExpression.eval yes p t d else WordExpression.eval no p t d := rfl

theorem rule_sound (previous words tag payload out : V) (ih : TableRealizes previous words)
    (h : Scalar.eval CheckerRule.rule previous tag payload=out+1) :
    Realizes (WordExpression.eval CompilerRule.rule words tag payload) out := by
  simp only [CheckerRule.rule,checkTag] at h
  simp only [CompilerRule.rule,wordTag]
  simp only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat] at h ⊢
  by_cases h0 : tag=(0:V)
  · simp only [h0,ite_true] at h ⊢
    exact mp_sound previous words _ payload out ih h
  · simp only [h0,ite_false] at h ⊢
    by_cases h1 : tag=(1:V)
    · simp only [h1,ite_true] at h ⊢
      exact gen_sound previous words _ payload out ih h
    · simp only [h1,ite_false] at h ⊢
      by_cases h2 : tag=(2:V)
      · simp only [h2,ite_true] at h ⊢
        exact leaf1_sound previous words _ payload out h
      · simp only [h2,ite_false] at h ⊢
        by_cases h3 : tag=(3:V)
        · simp only [h3,ite_true] at h ⊢
          exact leaf2_sound previous words _ payload out h
        · simp only [h3,ite_false] at h ⊢
          by_cases h4 : tag=(4:V)
          · simp only [h4,ite_true] at h ⊢
            exact leaf3_sound previous words _ payload out h
          · simp only [h4,ite_false] at h ⊢
            by_cases h5 : tag=(5:V)
            · simp only [h5,ite_true] at h ⊢
              exact leaf4_sound previous words _ payload out h
            · simp only [h5,ite_false] at h ⊢
              by_cases h6 : tag=(6:V)
              · simp only [h6,ite_true] at h ⊢
                exact leaf5_sound previous words _ payload out h
              · simp only [h6,ite_false] at h ⊢
                by_cases h7 : tag=(7:V)
                · simp only [h7,ite_true] at h ⊢
                  exact leaf6_sound previous words _ payload out h
                · simp only [h7,ite_false] at h ⊢
                  by_cases h8 : tag=(8:V)
                  · simp only [h8,ite_true] at h ⊢
                    exact leaf8_sound previous words _ payload out h
                  · simp only [h8,ite_false] at h ⊢
                    by_cases h9 : tag=(9:V)
                    · simp only [h9,ite_true] at h ⊢
                      exact bundle_sound previous words _ payload out h
                    · simp only [h9,ite_false] at h ⊢
                      simp only [CheckerRule.zero,Scalar.eval,Nat.cast_zero] at h
                      exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))
#print axioms rule_sound
end PA196.Arithmetic.CompilerSoundness

