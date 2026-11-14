import PA194SourceLKBudget
namespace PA194Logic.Relational.Source
open LO LO.FirstOrder M6.PA.RelationalSource

def findPreimage (xs : List (Proposition language)) (f : Proposition language → Proposition language)
    (q : Proposition language) (h : q ∈ xs.map f) : {p // p ∈ xs ∧ f p = q} := by
  match he : xs.find? (fun p => decide (f p = q)) with
  | some p =>
    refine ⟨p, List.mem_of_find?_eq_some he, ?_⟩
    simpa using List.find?_some he
  | none =>
    have hall := List.find?_eq_none.mp he
    have bad : False := by
      rcases List.mem_map.mp h with ⟨p,hp,hq⟩
      have hn := hall p hp
      have hy : decide (f p = q) = true := by simpa using hq
      exact hn hy
    exact False.elim bad
#print axioms findPreimage
end PA194Logic.Relational.Source
