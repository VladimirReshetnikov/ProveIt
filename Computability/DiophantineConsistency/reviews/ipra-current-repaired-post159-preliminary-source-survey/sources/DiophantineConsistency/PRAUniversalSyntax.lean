import DiophantineConsistency.PRAUniversalEquivalence

/-! Syntactic recognition of a universal prefix over an open matrix. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAUniversalSyntax
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAUniversalCandidate

/-- A formula is a chain of universal quantifiers ending in an open matrix. -/
def UniversalPrefix {ξ : Type} : {n : ℕ} → Semiformula language ξ n → Prop
  | _, ∀⁰ φ => UniversalPrefix φ
  | _, φ => φ.Open

theorem universalPrefix_rew_iff {ξ η : Type} {n m : ℕ}
    (φ : Semiformula language ξ n) (w : Rew language ξ n η m) :
    UniversalPrefix (w ▹ φ) ↔ UniversalPrefix φ := by
  induction φ using Semiformula.rec' generalizing η m with
  | hverum => simp [UniversalPrefix, Semiformula.Open]
  | hfalsum => simp [UniversalPrefix, Semiformula.Open]
  | hrel r v => simp [UniversalPrefix, Semiformula.Open]
  | hnrel r v => simp [UniversalPrefix, Semiformula.Open]
  | hand p q ihp ihq => simp [UniversalPrefix, Semiformula.Open, PRAFormulaParameters.qr_rew]
  | hor p q ihp ihq => simp [UniversalPrefix, Semiformula.Open, PRAFormulaParameters.qr_rew]
  | hall p ih => simpa [UniversalPrefix] using ih w.q
  | hexs p ih => simp [UniversalPrefix, Semiformula.Open]

theorem universalPrefix_allClosure {ξ : Type} {n : ℕ}
    (φ : Semiformula language ξ n) (h : UniversalPrefix φ) : UniversalPrefix (∀⁰* φ) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
      rw [allClosure_succ]
      apply ih
      simpa [UniversalPrefix] using h

theorem universalPrefix_toEmpty {ξ : Type} [DecidableEq ξ] {n : ℕ}
    (φ : Semiformula language ξ n) (hfree : φ.freeVariables = ∅) (h : UniversalPrefix φ) :
    UniversalPrefix (φ.toEmpty hfree) := by
  have he := universalPrefix_rew_iff (φ.toEmpty hfree) (Rew.emb : Rew language Empty n ξ n)
  rw [Semiformula.emb_toEmpty] at he
  exact he.mp h

theorem universalPrefix_univCl (φ : Proposition language) (h : UniversalPrefix φ) :
    UniversalPrefix φ.univCl := by
  unfold Semiformula.univCl Semiformula.univCl'
  apply universalPrefix_toEmpty
  apply universalPrefix_allClosure
  exact (universalPrefix_rew_iff φ (Rew.fixitr 0 φ.fvSup)).mpr h

end DiophantineConsistency.PRAUniversalSyntax
