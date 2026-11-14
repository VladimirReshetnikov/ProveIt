import PA194SourcePRACodes
namespace PA194SearchPRACode
open LO LO.FirstOrder M6.PA.RelationalSource
open PA194SourceSearchCoding PA194FormulaShiftPR
open DiophantineConsistency.PRAFiniteFunctionCodes

def numericSearch (s q : Nat) : Nat :=
  Encodable.encode (((Encodable.decode s : Option (List Nat)).getD []).find?
    (fun p => decide (formulaShiftCode p = q)))

theorem numericSearch_primrec : Primrec₂ numericSearch := by
  have pl : Primrec (fun s : Nat => (Encodable.decode s : Option (List Nat)).getD []) :=
    Primrec.option_getD.comp Primrec.decode (Primrec.const [])
  have hi : Primrec (fun p : Nat × Nat => (Encodable.decode p.1 : Option (List Nat)).getD []) :=
    pl.comp Primrec.fst
  have h := Primrec.encode.comp (codedSearch_primrec.comp hi Primrec.snd)
  exact h

theorem search_has_PRA_code : ∃ c : Code 2, ∀ s q : Nat,
    eval c (List.Vector.ofFn (fun i : Fin 2 => if i = 0 then s else q)) = numericSearch s q := by
  have p0 : Primrec (fun v : List.Vector Nat 2 => v.get 0) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const 0)
  have p1 : Primrec (fun v : List.Vector Nat 2 => v.get 1) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const 1)
  have h : Primrec (fun v : List.Vector Nat 2 => numericSearch (v.get 0) (v.get 1)) :=
    numericSearch_primrec.comp p0 p1
  obtain ⟨c, hc⟩ := exists_code_of_primrec h
  refine ⟨c, fun s q => ?_⟩
  have h := congrFun hc (List.Vector.ofFn (fun i : Fin 2 => if i = 0 then s else q))
  simpa using h

theorem search_PRA_code_correct : ∃ c : Code 2,
    ∀ (xs : List (Proposition language)) (q : Proposition language) (h : q ∈ xs.map Semiformula.shift),
      eval c (List.Vector.ofFn (fun i : Fin 2 => if i = 0 then Encodable.encode (xs.map Encodable.encode)
        else Encodable.encode q)) =
      Encodable.encode (some (Encodable.encode (PA194Logic.Relational.Source.findPreimage xs Semiformula.shift q h).val)) := by
  obtain ⟨c, hc⟩ := search_has_PRA_code
  refine ⟨c, fun xs q h => ?_⟩
  rw [hc]
  simp [numericSearch, codedSearch_selected xs q h]

#print axioms numericSearch_primrec
#print axioms search_has_PRA_code
#print axioms search_PRA_code_correct
end PA194SearchPRACode
