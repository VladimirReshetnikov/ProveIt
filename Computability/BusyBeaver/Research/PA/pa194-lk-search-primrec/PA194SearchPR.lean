import PA194SourceListPreimage
import Mathlib.Computability.Primrec.List

namespace PA194SearchPR
open PA194Logic.Relational.Source
open LO LO.FirstOrder M6.PA.RelationalSource

/-- Search is primitive recursive for any primitively coded type and function. -/
theorem search_primrec {α : Type} [Primcodable α] [DecidableEq α]
    (f : α → α) (hf : Primrec f) :
    Primrec₂ (fun (xs : List α) (q : α) => xs.find? (fun p => decide (f p = q))) := by
  have hr : PrimrecRel (fun p q : α => f p = q) := Primrec.eq.comp (hf.comp Primrec.fst) Primrec.snd
  have h := Primrec.list_head?.comp hr.listFilter
  apply h.of_eq
  intro ⟨xs,q⟩
  induction xs with
  | nil => rfl
  | cons p ps ih =>
    by_cases hp : f p = q <;> simp [List.find?, hp, ih]

/-- The universal-rule search specializes to source shift once its coding is supplied. -/
theorem shift_search_primrec [Primcodable (Proposition language)]
    (hshift : Primrec (Semiformula.shift : Proposition language → Proposition language)) :
    Primrec₂ (fun (xs : List (Proposition language)) (q : Proposition language) =>
      xs.find? (fun p => decide (Semiformula.shift p = q))) :=
  search_primrec Semiformula.shift hshift

/-- Its output is exactly the list compiler's selected source formula. -/
theorem search_eq_preimage (xs : List (Proposition language))
    (f : Proposition language → Proposition language) (q : Proposition language)
    (h : q ∈ xs.map f) :
    xs.find? (fun p => decide (f p = q)) = some (findPreimage xs f q h).val := by
  unfold findPreimage
  split
  · assumption
  · rename_i hnone
    have hall := List.find?_eq_none.mp hnone
    obtain ⟨p, hp, hq⟩ := List.mem_map.mp h
    have hn := hall p hp
    have hy : decide (f p = q) = true := by simpa using hq
    exact False.elim (hn hy)

#print axioms search_primrec
#print axioms shift_search_primrec
#print axioms search_eq_preimage
end PA194SearchPR
