import PA194SearchPR
import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Coding
namespace PA194SourceSearchCoding
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping M6.PA.RelationalSource
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

instance relationEncodable (k : Nat) : Encodable (Relation k) where
  encode r := match r with | .eq => 0 | .mem => 1
  decode n := match k, n with
    | 2, 0 => some .eq
    | 2, 1 => some .mem
    | _, _ => none
  encodek r := by cases r <;> rfl

instance sourceLanguageEncodable : language.Encodable := ⟨fun _ => inferInstanceAs (Encodable Empty), fun k => relationEncodable k⟩

instance sourceLanguageLOR : language.LORDefinable where
  func := .mkSigma “k f. ⊥”
  rel := .mkSigma “k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)”
  func_iff {k c} := by simp [language]
  rel_iff {k c} := by
    have h : c ∈ Set.range (Encodable.encode : Relation k → ℕ) ↔
        (k = 2 ∧ c = 0) ∨ (k = 2 ∧ c = 1) := by
      constructor
      · rintro ⟨r, hr⟩
        cases r with
        | eq => exact Or.inl ⟨rfl, hr.symm⟩
        | mem => exact Or.inr ⟨rfl, hr.symm⟩
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨Relation.eq, rfl⟩
        · exact ⟨Relation.mem, rfl⟩
    simpa [models_iff] using! h

theorem encode_shift (p : Proposition language) :
    Encodable.encode (Semiformula.shift p) =
      LO.FirstOrder.Arithmetic.Bootstrapping.shift language (Encodable.encode p) := by
  simpa [Semiformula.quote_eq_encode] using
    (Semiformula.quote_shift (V := Nat) p)

theorem encoded_search (xs : List (Proposition language)) (q : Proposition language) :
    (xs.map Encodable.encode).find? (fun p => decide
        (LO.FirstOrder.Arithmetic.Bootstrapping.shift language p = Encodable.encode q)) =
      (xs.find? (fun p => decide (Semiformula.shift p = q))).map Encodable.encode := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
    by_cases h : Semiformula.shift p = q
    · have hc : LO.FirstOrder.Arithmetic.Bootstrapping.shift language (Encodable.encode p) =
          Encodable.encode q := by rw [← encode_shift, h]
      simp [List.find?, h, hc]
    · have hc : LO.FirstOrder.Arithmetic.Bootstrapping.shift language (Encodable.encode p) ≠
          Encodable.encode q := by
        rw [← encode_shift]
        exact fun he => h (Encodable.encode_injective he)
      simp [List.find?, h, hc, ih]

theorem numeric_search_primrec
    (hs : Primrec (LO.FirstOrder.Arithmetic.Bootstrapping.shift language : Nat → Nat)) :
    Primrec₂ (fun (xs : List Nat) (q : Nat) => xs.find? (fun p => decide
      (LO.FirstOrder.Arithmetic.Bootstrapping.shift language p = q))) :=
  PA194SearchPR.search_primrec _ hs

theorem encoded_selected (xs : List (Proposition language)) (q : Proposition language)
    (h : q ∈ xs.map Semiformula.shift) :
    (xs.map Encodable.encode).find? (fun p => decide
        (LO.FirstOrder.Arithmetic.Bootstrapping.shift language p = Encodable.encode q)) =
      some (Encodable.encode (PA194Logic.Relational.Source.findPreimage xs Semiformula.shift q h).val) := by
  rw [encoded_search, PA194SearchPR.search_eq_preimage xs Semiformula.shift q h]
  rfl

#print axioms numeric_search_primrec
#print axioms encoded_selected
#print axioms encoded_search
#print axioms encode_shift
#print axioms sourceLanguageLOR
#print axioms relationEncodable
#print axioms sourceLanguageEncodable
end PA194SourceSearchCoding
