import PAFiniteBasisReduction.HullTotalRowTable
import PAFiniteBasisReduction.StandardRowFunctionality

/-!
# Reconstructing genuine hull rows from standard descriptors

`StandardRowFunctionality` extracts a normalized seven-way descriptor from
any genuine row at a standard code.  This file proves the converse and then
constructs the canonical descriptor selected by `totalRowProgram`.
-/

namespace LeanProofs
namespace PAFiniteBasisReduction

open SetTheory PA

universe u

namespace FiniteSkolemCut
namespace ProgramTrace

/-- The recurring child-bound obligation: hull numerals are `RawLt`-ordered
like their standard codes.  Composes the ambient-to-hull order transport with
the standard numeral order. -/
private theorem hull_rawLt_numeralValue_of_lt {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (generator : alpha) (hPA : RawPASatisfies M)
    (hLtRank : formulaRank traceLtFormula ≤ rank)
    {m n : Nat} (hmn : m < n) :
    RawLt (preModel M S rank generator)
      (PA.Term.numeralValue (preModel M S rank generator) m)
      (PA.Term.numeralValue (preModel M S rank generator) n) := by
  apply hull_rawLt_of_ambient M S rank generator
    (by simpa [traceLtFormula] using hLtRank)
  simpa only [hull_numeralValue_val_transport] using
    rawLt_numeralValue_of_lt (m := m) (n := n) hPA hmn

/-- Shared reconstruction of a binary (`add`/`mul`) row case from its
witness fields; only the tag, the syntactic operator, and the hull
operation differ between the two instantiations. -/
private theorem sat_binaryCase_of_witness {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (generator : alpha) (hPA : RawPASatisfies M)
    (hLtRank : formulaRank traceLtFormula ≤ rank)
    (target : Nat) (code value betaCode betaStep : PA.Term)
    (e : Nat → Carrier M S rank generator)
    (hcode : PA.Term.eval (preModel M S rank generator) e code =
      PA.Term.numeralValue (preModel M S rank generator) target)
    (tag : Nat) (op : PA.Term → PA.Term → PA.Term)
    (opValue : Carrier M S rank generator → Carrier M S rank generator →
      Carrier M S rank generator)
    (hop : ∀ (e' : Nat → Carrier M S rank generator) (a b : PA.Term),
      PA.Term.eval (preModel M S rank generator) e' (op a b) =
        opValue (PA.Term.eval (preModel M S rank generator) e' a)
          (PA.Term.eval (preModel M S rank generator) e' b))
    (leftCode rightCode : Nat)
    (leftValue rightValue : Carrier M S rank generator)
    (target_eq : target = Program.nodeCode tag
      (Program.nodeCode leftCode rightCode))
    (hleft : RawBetaEntry (preModel M S rank generator) leftValue
      (PA.Term.eval (preModel M S rank generator) e betaCode)
      (PA.Term.eval (preModel M S rank generator) e betaStep)
      (PA.Term.numeralValue (preModel M S rank generator) leftCode))
    (hright : RawBetaEntry (preModel M S rank generator) rightValue
      (PA.Term.eval (preModel M S rank generator) e betaCode)
      (PA.Term.eval (preModel M S rank generator) e betaStep)
      (PA.Term.numeralValue (preModel M S rank generator) rightCode))
    (hvalue : PA.Term.eval (preModel M S rank generator) e value =
      opValue leftValue rightValue) :
    PA.Formula.Sat (preModel M S rank generator) e
      (binaryCase tag op code value betaCode betaStep) := by
  let KM := preModel M S rank generator
  apply sat_binaryCase_of KM tag op opValue
    code value betaCode betaStep (PA.Term.numeral leftCode)
    (PA.Term.numeral rightCode) leftValue rightValue e hop
  · have hinner := hull_eval_nodeTerm_standard M S rank generator hPA
      (PA.Term.numeral leftCode) (PA.Term.numeral rightCode) e
      leftCode rightCode (by simp only [PA.Term.eval_numeral])
      (by simp only [PA.Term.eval_numeral])
    calc
      PA.Term.eval KM e code = PA.Term.numeralValue KM target := hcode
      _ = PA.Term.numeralValue KM
          (Program.nodeCode tag
            (Program.nodeCode leftCode rightCode)) := by rw [target_eq]
      _ = PA.Term.eval KM e
          (nodeTerm (PA.Term.numeral tag)
            (nodeTerm (PA.Term.numeral leftCode)
              (PA.Term.numeral rightCode))) :=
        (hull_eval_nodeTerm_standard M S rank generator hPA _ _ e tag
          (Program.nodeCode leftCode rightCode)
          (by simp only [PA.Term.eval_numeral]) hinner).symm
  · simp only [PA.Term.eval_numeral]
    rw [hcode]
    exact hull_rawLt_numeralValue_of_lt M S rank generator hPA hLtRank (by
      rw [target_eq]
      exact Nat.lt_trans
        (Program.left_lt_nodeCode leftCode rightCode)
        (Program.right_lt_nodeCode tag _))
  · simp only [PA.Term.eval_numeral]
    rw [hcode]
    exact hull_rawLt_numeralValue_of_lt M S rank generator hPA hLtRank (by
      rw [target_eq]
      exact Nat.lt_trans
        (Program.right_lt_nodeCode leftCode rightCode)
        (Program.right_lt_nodeCode tag _))
  · simpa only [PA.Term.eval_numeral] using hleft
  · simpa only [PA.Term.eval_numeral] using hright
  · exact hvalue

/-- Every normalized standard-row descriptor reconstructs a genuine
`programCases` witness in the hull. -/
theorem sat_programCases_of_standardRowWitness {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (generator : alpha) (hPA : RawPASatisfies M)
    (hLtRank : formulaRank traceLtFormula ≤ rank)
    (target : Nat) (code value betaCode betaStep starTerm : PA.Term)
    (e : Nat → Carrier M S rank generator)
    (hcode : PA.Term.eval (preModel M S rank generator) e code =
      PA.Term.numeralValue (preModel M S rank generator) target)
    (hwitness : StandardRowWitness (preModel M S rank generator)
      rank target
      (PA.Term.eval (preModel M S rank generator) e betaCode)
      (PA.Term.eval (preModel M S rank generator) e betaStep)
      (PA.Term.eval (preModel M S rank generator) e starTerm)
      (PA.Term.eval (preModel M S rank generator) e value)) :
    PA.Formula.Sat (preModel M S rank generator) e
      (programCases rank code value betaCode betaStep starTerm) := by
  classical
  let KM := preModel M S rank generator
  change PA.Term.eval KM e code = PA.Term.numeralValue KM target at hcode
  change StandardRowWitness KM rank target
    (PA.Term.eval KM e betaCode) (PA.Term.eval KM e betaStep)
    (PA.Term.eval KM e starTerm) (PA.Term.eval KM e value) at hwitness
  change PA.Formula.Sat KM e
    (programCases rank code value betaCode betaStep starTerm)
  rw [programCases, sat_disjunction]
  cases hwitness with
  | star target_eq hvalue =>
      refine ⟨starCase code value starTerm, by simp, ?_⟩
      constructor
      · calc
          PA.Term.eval KM e code = PA.Term.numeralValue KM target := hcode
          _ = PA.Term.numeralValue KM (Program.nodeCode 0 0) := by
            rw [target_eq]
          _ = PA.Term.eval KM e
              (nodeTerm (PA.Term.numeral 0) (PA.Term.numeral 0)) :=
            (hull_eval_nodeTerm_standard M S rank generator hPA _ _ e 0 0
              (by simp only [PA.Term.eval_numeral])
              (by simp only [PA.Term.eval_numeral])).symm
      · exact hvalue
  | zero target_eq hvalue =>
      refine ⟨zeroCase code value, by simp, ?_⟩
      constructor
      · calc
          PA.Term.eval KM e code = PA.Term.numeralValue KM target := hcode
          _ = PA.Term.numeralValue KM (Program.nodeCode 1 0) := by
            rw [target_eq]
          _ = PA.Term.eval KM e
              (nodeTerm (PA.Term.numeral 1) (PA.Term.numeral 0)) :=
            (hull_eval_nodeTerm_standard M S rank generator hPA _ _ e 1 0
              (by simp only [PA.Term.eval_numeral])
              (by simp only [PA.Term.eval_numeral])).symm
      · exact hvalue
  | succ childCode childValue target_eq hlookup hvalue =>
      refine ⟨succCase code value betaCode betaStep, by simp, ?_⟩
      apply sat_succCase_of KM code value betaCode betaStep
        (PA.Term.numeral childCode) childValue e
      · calc
          PA.Term.eval KM e code = PA.Term.numeralValue KM target := hcode
          _ = PA.Term.numeralValue KM (Program.nodeCode 2 childCode) := by
            rw [target_eq]
          _ = PA.Term.eval KM e
              (nodeTerm (PA.Term.numeral 2)
                (PA.Term.numeral childCode)) :=
            (hull_eval_nodeTerm_standard M S rank generator hPA _ _ e
              2 childCode (by simp only [PA.Term.eval_numeral])
              (by simp only [PA.Term.eval_numeral])).symm
      · simp only [PA.Term.eval_numeral]
        rw [hcode]
        exact hull_rawLt_numeralValue_of_lt M S rank generator hPA hLtRank (by
            rw [target_eq]
            exact Program.right_lt_nodeCode 2 childCode)
      · simpa only [PA.Term.eval_numeral] using hlookup
      · exact hvalue
  | add leftCode rightCode leftValue rightValue target_eq
      hleft hright hvalue =>
      refine ⟨binaryCase 3 PA.Term.add code value betaCode betaStep,
        by simp, ?_⟩
      exact sat_binaryCase_of_witness M S rank generator hPA hLtRank
        target code value betaCode betaStep e hcode 3 PA.Term.add
        KM.add (fun _ _ _ => rfl) leftCode rightCode leftValue
        rightValue target_eq hleft hright hvalue
  | mul leftCode rightCode leftValue rightValue target_eq
      hleft hright hvalue =>
      refine ⟨binaryCase 4 PA.Term.mul code value betaCode betaStep,
        by simp, ?_⟩
      exact sat_binaryCase_of_witness M S rank generator hPA hLtRank
        target code value betaCode betaStep e hcode 4 PA.Term.mul
        KM.mul (fun _ _ _ => rfl) leftCode rightCode leftValue
        rightValue target_eq hleft hright hvalue
  | exSkolem body hRank codes values target_eq hlookup hgraph =>
      refine ⟨exSkolemCase rank code value betaCode betaStep, by simp, ?_⟩
      rw [exSkolemCase, sat_disjunction]
      have hBodyRank : formulaRank body ≤ rank := by
        simp only [formulaRank] at hRank
        omega
      have hBodyMem : body ∈ exBodies rank := by
        simp [exBodies, (mem_formulasOfRankAtMost rank body).mpr hBodyRank,
          hRank]
      refine ⟨skolemBranch rank 5 (leastDefaultGraph body)
        (Program.formulaIndex rank body) code value betaCode betaStep,
        List.mem_map.mpr ⟨body, hBodyMem, rfl⟩, ?_⟩
      apply sat_skolemBranch_of_slots KM rank 5 (leastDefaultGraph body)
        (Program.formulaIndex rank body) code value betaCode betaStep e
        values (fun i => PA.Term.numeral (codes i))
      · have hvector := hull_eval_listTerm_standard_entries M S rank
          generator hPA (List.ofFn (fun i : Fin rank => i))
          (fun i => PA.Term.numeral (codes i)) (fun i => codes i) e
          (by intro i hi; simp only [PA.Term.eval_numeral])
        have hvector' : PA.Term.eval KM e
            (listTerm (List.ofFn (fun i => PA.Term.numeral (codes i)))) =
            PA.Term.numeralValue KM (Program.vectorCode codes) := by
          simpa [Program.vectorCode, List.map_ofFn, Function.comp_def]
            using hvector
        have hinner := hull_eval_nodeTerm_standard M S rank generator hPA
          (PA.Term.numeral (Program.formulaIndex rank body))
          (listTerm (List.ofFn (fun i => PA.Term.numeral (codes i)))) e
          (Program.formulaIndex rank body) (Program.vectorCode codes)
          (by simp only [PA.Term.eval_numeral]) hvector'
        calc
          PA.Term.eval KM e code = PA.Term.numeralValue KM target := hcode
          _ = PA.Term.numeralValue KM
              (Program.nodeCode 5
                (Program.nodeCode (Program.formulaIndex rank body)
                  (Program.vectorCode codes))) := by rw [target_eq]
          _ = PA.Term.eval KM e
              (nodeTerm (PA.Term.numeral 5)
                (nodeTerm
                  (PA.Term.numeral (Program.formulaIndex rank body))
                  (listTerm (List.ofFn
                    (fun i => PA.Term.numeral (codes i)))))) :=
            (hull_eval_nodeTerm_standard M S rank generator hPA _ _ e 5
              (Program.nodeCode (Program.formulaIndex rank body)
                (Program.vectorCode codes))
              (by simp only [PA.Term.eval_numeral]) hinner).symm
      · intro i
        simp only [PA.Term.eval_numeral]
        rw [hcode]
        exact hull_rawLt_numeralValue_of_lt M S rank generator hPA hLtRank (by
            rw [target_eq]
            exact Nat.lt_trans (Program.vector_entry_lt_code codes i)
              (Nat.lt_trans
                (Program.right_lt_nodeCode
                  (Program.formulaIndex rank body) _)
                (Program.right_lt_nodeCode 5 _)))
      · intro i
        simpa only [PA.Term.eval_numeral] using hlookup i
      · exact hgraph
  | allSkolem body hRank codes values target_eq hlookup hgraph =>
      refine ⟨allSkolemCase rank code value betaCode betaStep, by simp, ?_⟩
      rw [allSkolemCase, sat_disjunction]
      have hBodyRank : formulaRank body ≤ rank := by
        simp only [formulaRank] at hRank
        omega
      have hBodyMem : body ∈ allBodies rank := by
        simp [allBodies, (mem_formulasOfRankAtMost rank body).mpr hBodyRank,
          hRank]
      refine ⟨skolemBranch rank 6 (leastCounterexampleGraph body)
        (Program.formulaIndex rank body) code value betaCode betaStep,
        List.mem_map.mpr ⟨body, hBodyMem, rfl⟩, ?_⟩
      apply sat_skolemBranch_of_slots KM rank 6
        (leastCounterexampleGraph body) (Program.formulaIndex rank body)
        code value betaCode betaStep e values
        (fun i => PA.Term.numeral (codes i))
      · have hvector := hull_eval_listTerm_standard_entries M S rank
          generator hPA (List.ofFn (fun i : Fin rank => i))
          (fun i => PA.Term.numeral (codes i)) (fun i => codes i) e
          (by intro i hi; simp only [PA.Term.eval_numeral])
        have hvector' : PA.Term.eval KM e
            (listTerm (List.ofFn (fun i => PA.Term.numeral (codes i)))) =
            PA.Term.numeralValue KM (Program.vectorCode codes) := by
          simpa [Program.vectorCode, List.map_ofFn, Function.comp_def]
            using hvector
        have hinner := hull_eval_nodeTerm_standard M S rank generator hPA
          (PA.Term.numeral (Program.formulaIndex rank body))
          (listTerm (List.ofFn (fun i => PA.Term.numeral (codes i)))) e
          (Program.formulaIndex rank body) (Program.vectorCode codes)
          (by simp only [PA.Term.eval_numeral]) hvector'
        calc
          PA.Term.eval KM e code = PA.Term.numeralValue KM target := hcode
          _ = PA.Term.numeralValue KM
              (Program.nodeCode 6
                (Program.nodeCode (Program.formulaIndex rank body)
                  (Program.vectorCode codes))) := by rw [target_eq]
          _ = PA.Term.eval KM e
              (nodeTerm (PA.Term.numeral 6)
                (nodeTerm
                  (PA.Term.numeral (Program.formulaIndex rank body))
                  (listTerm (List.ofFn
                    (fun i => PA.Term.numeral (codes i)))))) :=
            (hull_eval_nodeTerm_standard M S rank generator hPA _ _ e 6
              (Program.nodeCode (Program.formulaIndex rank body)
                (Program.vectorCode codes))
              (by simp only [PA.Term.eval_numeral]) hinner).symm
      · intro i
        simp only [PA.Term.eval_numeral]
        rw [hcode]
        exact hull_rawLt_numeralValue_of_lt M S rank generator hPA hLtRank (by
            rw [target_eq]
            exact Nat.lt_trans (Program.vector_entry_lt_code codes i)
              (Nat.lt_trans
                (Program.right_lt_nodeCode
                  (Program.formulaIndex rank body) _)
                (Program.right_lt_nodeCode 6 _)))
      · intro i
        simpa only [PA.Term.eval_numeral] using hlookup i
      · exact hgraph

/-! ## Exhaustive canonical standard row -/

set_option linter.unusedSimpArgs false in
/-- At every standard code, the total decoder either recognizes one of the
seven genuine row shapes (with the canonical child values supplied by the
table), or its denoting program is literally `zero`. -/
theorem canonicalStandardRowWitness_or_zero {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (generator : alpha)
    (betaCode betaStep : Carrier M S rank generator) (target : Nat)
    (htable : ∀ child, child < target →
      RawBetaEntry (preModel M S rank generator)
        (hullProgramValue M S rank generator
          (totalRowProgram rank child))
        betaCode betaStep
        (PA.Term.numeralValue (preModel M S rank generator) child)) :
    StandardRowWitness (preModel M S rank generator) rank target
        betaCode betaStep
        (⟨generator, Hull.star⟩ : Carrier M S rank generator)
        (hullProgramValue M S rank generator
          (totalRowProgram rank target)) ∨
      totalRowProgram rank target = .zero := by
  classical
  let KM := preModel M S rank generator
  let row : Nat → Carrier M S rank generator := fun k =>
    hullProgramValue M S rank generator (totalRowProgram rank k)
  cases houter : boundedNodeComponents target with
  | none =>
      right
      rw [totalRowProgram_eq]
      simp [totalRowProgramStep, houter]
  | some outer =>
      have houterRaw : nodeComponents target = some outer.1 :=
        boundedNodeComponents_eq_some_iff.mp houter
      have houterCode :
          Program.nodeCode outer.1.1 outer.1.2 = target :=
        nodeComponents_eq_some_iff.mp houterRaw
      by_cases hstar : outer.1.1 = 0 ∧ outer.1.2 = 0
      · left
        rcases hstar with ⟨htag, hpayload⟩
        refine .star ?_ ?_
        · simpa [htag, hpayload] using houterCode.symm
        · rw [totalRowProgram_of_star houter htag hpayload]
          exact hullProgramValue_star M S rank generator
      by_cases hzero : outer.1.1 = 1 ∧ outer.1.2 = 0
      · left
        rcases hzero with ⟨htag, hpayload⟩
        refine .zero ?_ ?_
        · simpa [htag, hpayload] using houterCode.symm
        · rw [totalRowProgram_of_zero houter htag hpayload]
          exact hullProgramValue_zero M S rank generator
      by_cases hsucc : outer.1.1 = 2
      · left
        let child := outer.1.2
        refine .succ child (row child) ?_ ?_ ?_
        · simpa [hsucc, child] using houterCode.symm
        · exact htable child outer.2.2
        · rw [totalRowProgram_of_succ houter hsucc rfl]
          exact hullProgramValue_succ M S rank generator
            (totalRowProgram rank child)
      by_cases hadd : outer.1.1 = 3
      · cases hchildren : boundedNodeComponents outer.1.2 with
        | none =>
            right
            rw [totalRowProgram_eq]
            simp [totalRowProgramStep, houter, hstar, hzero, hsucc,
              hadd, hchildren]
        | some children =>
            left
            have hchildrenRaw : nodeComponents outer.1.2 =
                some children.1 :=
              boundedNodeComponents_eq_some_iff.mp hchildren
            have hchildrenCode : Program.nodeCode children.1.1
                children.1.2 = outer.1.2 :=
              nodeComponents_eq_some_iff.mp hchildrenRaw
            let leftCode := children.1.1
            let rightCode := children.1.2
            refine .add leftCode rightCode (row leftCode) (row rightCode)
              ?_ ?_ ?_ ?_
            · calc
                target = Program.nodeCode outer.1.1 outer.1.2 :=
                  houterCode.symm
                _ = Program.nodeCode 3
                    (Program.nodeCode leftCode rightCode) := by
                  rw [hadd, hchildrenCode]
            · exact htable leftCode
                (Nat.lt_trans children.2.1 outer.2.2)
            · exact htable rightCode
                (Nat.lt_trans children.2.2 outer.2.2)
            · rw [totalRowProgram_of_add houter hadd rfl hchildren
                rfl rfl]
              exact hullProgramValue_add M S rank generator
                (totalRowProgram rank leftCode)
                (totalRowProgram rank rightCode)
      by_cases hmul : outer.1.1 = 4
      · cases hchildren : boundedNodeComponents outer.1.2 with
        | none =>
            right
            rw [totalRowProgram_eq]
            simp [totalRowProgramStep, houter, hstar, hzero, hsucc,
              hadd, hmul, hchildren]
        | some children =>
            left
            have hchildrenRaw : nodeComponents outer.1.2 =
                some children.1 :=
              boundedNodeComponents_eq_some_iff.mp hchildren
            have hchildrenCode : Program.nodeCode children.1.1
                children.1.2 = outer.1.2 :=
              nodeComponents_eq_some_iff.mp hchildrenRaw
            let leftCode := children.1.1
            let rightCode := children.1.2
            refine .mul leftCode rightCode (row leftCode) (row rightCode)
              ?_ ?_ ?_ ?_
            · calc
                target = Program.nodeCode outer.1.1 outer.1.2 :=
                  houterCode.symm
                _ = Program.nodeCode 4
                    (Program.nodeCode leftCode rightCode) := by
                  rw [hmul, hchildrenCode]
            · exact htable leftCode
                (Nat.lt_trans children.2.1 outer.2.2)
            · exact htable rightCode
                (Nat.lt_trans children.2.2 outer.2.2)
            · rw [totalRowProgram_of_mul houter hmul rfl hchildren
                rfl rfl]
              exact hullProgramValue_mul M S rank generator
                (totalRowProgram rank leftCode)
                (totalRowProgram rank rightCode)
      by_cases hex : outer.1.1 = 5
      · cases hfields : boundedNodeComponents outer.1.2 with
        | none =>
            right
            rw [totalRowProgram_eq]
            simp [totalRowProgramStep, houter, hstar, hzero, hsucc,
              hadd, hmul, hex, hfields]
        | some fields =>
            cases hchildren : boundedVectorComponents rank fields.1.2 with
            | none =>
                right
                rw [totalRowProgram_eq]
                simp [totalRowProgramStep, houter, hstar, hzero, hsucc,
                  hadd, hmul, hex, hfields, hchildren]
            | some children =>
                cases hbody : exBodyAt rank fields.1.1 with
                | none =>
                    right
                    rw [totalRowProgram_eq]
                    simp [totalRowProgramStep, houter, hstar, hzero, hsucc,
                      hadd, hmul, hex, hfields, hchildren, hbody]
                | some entry =>
                    left
                    have hfieldsRaw : nodeComponents outer.1.2 =
                        some fields.1 :=
                      boundedNodeComponents_eq_some_iff.mp hfields
                    have hfieldsCode : Program.nodeCode fields.1.1
                        fields.1.2 = outer.1.2 :=
                      nodeComponents_eq_some_iff.mp hfieldsRaw
                    have hchildrenRaw : vectorComponents rank fields.1.2 =
                        some children.1 :=
                      boundedVectorComponents_eq_some_iff.mp hchildren
                    have hchildrenCode : Program.vectorCode children.1 =
                        fields.1.2 :=
                      vectorComponents_eq_some_iff.mp hchildrenRaw
                    let codes : Fin rank → Nat := children.1
                    let values : Fin rank → Carrier M S rank generator :=
                      fun i => row (codes i)
                    refine .exSkolem entry.body entry.quantifiedRank
                      codes values ?_ ?_ ?_
                    · calc
                        target = Program.nodeCode outer.1.1 outer.1.2 :=
                          houterCode.symm
                        _ = Program.nodeCode 5
                            (Program.nodeCode (Program.formulaIndex rank
                              entry.body) (Program.vectorCode codes)) := by
                          rw [hex, entry.index_eq, hchildrenCode,
                            hfieldsCode]
                    · intro i
                      exact htable (codes i) (Nat.lt_trans (children.2 i)
                        (Nat.lt_trans fields.2.2 outer.2.2))
                    · have hrow := totalRowProgram_of_ex houter hex rfl
                        hfields hchildren hbody
                      have hgraph := hullProgramValue_exSkolem_graph M S rank
                        generator entry.body entry.quantifiedRank
                        (fun i => totalRowProgram rank (codes i))
                      rw [hrow]
                      simpa [values, row, hullProgramArgsEnv] using hgraph
      by_cases hall : outer.1.1 = 6
      · cases hfields : boundedNodeComponents outer.1.2 with
        | none =>
            right
            rw [totalRowProgram_eq]
            simp [totalRowProgramStep, houter, hstar, hzero, hsucc,
              hadd, hmul, hex, hall, hfields]
        | some fields =>
            cases hchildren : boundedVectorComponents rank fields.1.2 with
            | none =>
                right
                rw [totalRowProgram_eq]
                simp [totalRowProgramStep, houter, hstar, hzero, hsucc,
                  hadd, hmul, hex, hall, hfields, hchildren]
            | some children =>
                cases hbody : allBodyAt rank fields.1.1 with
                | none =>
                    right
                    rw [totalRowProgram_eq]
                    simp [totalRowProgramStep, houter, hstar, hzero, hsucc,
                      hadd, hmul, hex, hall, hfields, hchildren, hbody]
                | some entry =>
                    left
                    have hfieldsRaw : nodeComponents outer.1.2 =
                        some fields.1 :=
                      boundedNodeComponents_eq_some_iff.mp hfields
                    have hfieldsCode : Program.nodeCode fields.1.1
                        fields.1.2 = outer.1.2 :=
                      nodeComponents_eq_some_iff.mp hfieldsRaw
                    have hchildrenRaw : vectorComponents rank fields.1.2 =
                        some children.1 :=
                      boundedVectorComponents_eq_some_iff.mp hchildren
                    have hchildrenCode : Program.vectorCode children.1 =
                        fields.1.2 :=
                      vectorComponents_eq_some_iff.mp hchildrenRaw
                    let codes : Fin rank → Nat := children.1
                    let values : Fin rank → Carrier M S rank generator :=
                      fun i => row (codes i)
                    refine .allSkolem entry.body entry.quantifiedRank
                      codes values ?_ ?_ ?_
                    · calc
                        target = Program.nodeCode outer.1.1 outer.1.2 :=
                          houterCode.symm
                        _ = Program.nodeCode 6
                            (Program.nodeCode (Program.formulaIndex rank
                              entry.body) (Program.vectorCode codes)) := by
                          rw [hall, entry.index_eq, hchildrenCode,
                            hfieldsCode]
                    · intro i
                      exact htable (codes i) (Nat.lt_trans (children.2 i)
                        (Nat.lt_trans fields.2.2 outer.2.2))
                    · have hrow := totalRowProgram_of_all houter hall rfl
                        hfields hchildren hbody
                      have hgraph := hullProgramValue_allSkolem_graph M S rank
                        generator entry.body entry.quantifiedRank
                        (fun i => totalRowProgram rank (codes i))
                      rw [hrow]
                      simpa [values, row, hullProgramArgsEnv] using hgraph
      · right
        rw [totalRowProgram_eq]
        simp [totalRowProgramStep, houter, hstar, hzero, hsucc,
          hadd, hmul, hex, hall]

end ProgramTrace
end FiniteSkolemCut

end PAFiniteBasisReduction
end LeanProofs
