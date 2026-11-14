import PA194SourcePRACodes
namespace PA194SeqDepthPRACode
open LO LO.FirstOrder M6.PA.RelationalSource
open PA194SourceSearchCoding PA194DepthPR PA194SourcePRACodes
open DiophantineConsistency.PRAFiniteFunctionCodes

def numericSequentDepth (s : Nat) : Nat :=
  sequentDepthCode ((Encodable.decode s : Option (List Nat)).getD [])

theorem numericSequentDepth_primrec : Primrec numericSequentDepth := by
  have pl : Primrec (fun s : Nat => (Encodable.decode s : Option (List Nat)).getD []) :=
    Primrec.option_getD.comp Primrec.decode (Primrec.const [])
  exact sequentDepthCode_primrec.comp pl

theorem sequentDepth_code_correct : ∃ c : Code 1,
    ∀ xs : List (Proposition language),
      eval c (List.Vector.ofFn (fun _ : Fin 1 => Encodable.encode (xs.map Encodable.encode))) =
        PA194Logic.Relational.Source.sequentDepth (xs : PA194Logic.Relational.Source.SourceSequent) := by
  obtain ⟨c, hc⟩ := unaryCode_of_primrec _ numericSequentDepth_primrec
  refine ⟨c, fun xs => ?_⟩
  rw [hc]
  simp [numericSequentDepth, sequentDepthCode_correct]

#print axioms numericSequentDepth_primrec
#print axioms sequentDepth_code_correct
end PA194SeqDepthPRACode
