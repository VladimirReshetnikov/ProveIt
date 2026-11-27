import PA194PAeqNDShift

/-!
# Addition congruence translation into PAeq
-/

set_option autoImplicit false

namespace PA194PAeq.AddCongruence

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder

/-- The Foundation addition congruence sentence translated to the PAeq language. -/
def targetSource : Proposition language := PA194PAeq.formula
  (Rewriting.emb (Theory.Eq.funcExt (L := ℒₒᵣ) Language.ORing.Func.add) : ArithmeticSemiformula ℕ 0)

private def translatedBody : Semiproposition language 4 :=
  implies (eq (.bvar 0) (.bvar 2) ⋏ (eq (.bvar 1) (.bvar 3) ⋏ ⊤))
    (eq (add (.bvar 0) (.bvar 1)) (add (.bvar 2) (.bvar 3)))

private theorem targetSource_eq :
    targetSource = .all (.all (.all (.all translatedBody))) := by
  rfl

private theorem rewrite_implies {n m : ℕ} (r : Rew language ℕ n ℕ m)
    (p q : Semiproposition language n) :
    (r ▹ implies p q) = implies (r ▹ p) (r ▹ q) := by
  change (r ▹ (p 🡒 q)) = ((r ▹ p) 🡒 (r ▹ q))
  exact LogicalConnective.HomClass.map_imply _ _ _

private theorem rewrite_eq {n m : ℕ} (r : Rew language ℕ n ℕ m)
    (s t : Semiterm language ℕ n) : (r ▹ eq s t) = eq (r s) (r t) := by
  simp [eq]

private theorem rewrite_add {n m : ℕ} (r : Rew language ℕ n ℕ m)
    (s t : Semiterm language ℕ n) : r (add s t) = add (r s) (r t) := by
  simp [add]

private theorem addCongruence_shift : addCongruence.shift = addCongruence := by
  apply Semiformula.rew_eq_self_of
  · exact fun i ↦ Fin.elim0 i
  · intro i hi
    have hclosed : addCongruence.freeVariables = ∅ := by decide
    simp [Semiformula.FVar?, hclosed] at hi

set_option maxHeartbeats 5000000 in
/-- A derivation of the translated source axiom from the PAeq addition congruence axiom. -/
noncomputable def addExtCertificate : ND.Proof [addCongruence] targetSource := by
  rw [targetSource_eq]
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  let x : Semiterm language ℕ 0 := .fvar 0
  let y : Semiterm language ℕ 0 := .fvar 1
  let x' : Semiterm language ℕ 0 := .fvar 2
  let y' : Semiterm language ℕ 0 := .fvar 3
  let p := eq x x'
  let q := eq y y'
  suffices opened : ND.Proof [addCongruence.shift.shift.shift.shift]
      (implies (p ⋏ (q ⋏ ⊤)) (eq (add x y) (add x' y'))) by
    convert opened using 1
    · rfl
    · change (Rew.free ▹ (Rew.free.q ▹ (Rew.free.q.q ▹
        (Rew.free.q.q.q ▹ translatedBody)))) = _
      rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app,
        ← TransitiveRewriting.comp_app]
      let freeOne : Rew language ℕ 1 ℕ 0 := Rew.free
      let openFour : Rew language ℕ 4 ℕ 0 :=
        ((freeOne.comp freeOne.q).comp freeOne.q.q).comp freeOne.q.q.q
      change (openFour ▹ translatedBody) = _
      have h0 : openFour (.bvar 0) = x := rfl
      have h1 : openFour (.bvar 1) = y := rfl
      have h2 : openFour (.bvar 2) = x' := rfl
      have h3 : openFour (.bvar 3) = y' := rfl
      simp only [translatedBody, rewrite_implies, LogicalConnective.HomClass.map_and,
        LogicalConnective.HomClass.map_top, rewrite_eq, rewrite_add, p, q, h0, h1, h2, h3]
  simp only [addCongruence_shift]
  apply ND.impIntro
  let Γ := [p ⋏ (q ⋏ ⊤), addCongruence]
  have both : ND.Proof Γ (p ⋏ (q ⋏ ⊤)) := ND.assumption (by simp [Γ])
  have first : ND.Proof Γ p := ND.andLeft both
  have second : ND.Proof Γ q := ND.andLeft (ND.andRight both)
  have ax : ND.Proof Γ addCongruence := ND.assumption (by simp [Γ])
  have a := ND.allElim _ y' ax
  have b := ND.allElim _ y a
  have c := ND.allElim _ x' b
  have d : ND.Proof Γ (implies p (implies q (eq (add x y) (add x' y')))) :=
    by
      convert ND.allElim _ x c using 1
      change _ = (Rew.subst ![x] ▹ ((Rew.subst ![x']).q ▹ ((Rew.subst ![y]).q.q ▹
        ((Rew.subst ![y']).q.q.q ▹
          implies (eq (.bvar 0) (.bvar 1)) (implies (eq (.bvar 2) (.bvar 3))
            (eq (add (.bvar 0) (.bvar 2)) (add (.bvar 1) (.bvar 3))))))))
      rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app,
        ← TransitiveRewriting.comp_app]
      let substituteFour : Rew language ℕ 4 ℕ 0 :=
        ((((Rew.subst ![x]).comp (Rew.subst ![x']).q).comp
          (Rew.subst ![y]).q.q).comp (Rew.subst ![y']).q.q.q)
      change _ = (substituteFour ▹ _)
      have h0 : substituteFour (.bvar 0) = x := rfl
      have h1 : substituteFour (.bvar 1) = x' := rfl
      have h2 : substituteFour (.bvar 2) = y := rfl
      have h3 : substituteFour (.bvar 3) = y' := rfl
      simp only [rewrite_implies, rewrite_eq, rewrite_add, p, q, h0, h1, h2, h3]
  exact ND.mp second (ND.mp first d)

#print axioms addExtCertificate

end PA194PAeq.AddCongruence
