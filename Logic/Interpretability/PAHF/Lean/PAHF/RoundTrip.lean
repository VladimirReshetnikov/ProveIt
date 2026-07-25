/-
  SetTheory.PAHF.RoundTrip

  Syntactic proof of the PA side of the PA/HFFin round trip.  This module
  defines the internal graph of Ackermann's finite-ordinal code function,
  proves totality, exact range, injectivity, and compatibility with every PA
  term constructor, and lifts the graph result through formula induction to
  the composite-identity theorem for PA sentences.
-/
import PAHF.Interpretation
import PAHF.ProofCalculus

namespace SetTheory
namespace PA
namespace Formula

/-- Standard-model semantics of the term-parametric Ackermann-membership
macro. -/
theorem hfMemTermAt_exact (e : Nat → Nat) (elem : Nat)
    (setCode : Term) :
    Sat natModel e (hfMemTermAt elem setCode) ↔
      AckermannHF.Mem (e elem) (Term.eval natModel e setCode) := by
  rw [← subst_instTerm_hfMemAt_succ_zero]
  rw [Sat_subst]
  have henv : ∀ n,
      Term.eval natModel e (instTerm setCode n) =
        scons (Term.eval natModel e setCode) e n := by
    intro n
    cases n <;> rfl
  exact
    (Sat_ext natModel (hfMemAt (elem+1) 0) henv).trans
      (hfMemAt_exact
        (scons (Term.eval natModel e setCode) e) (elem+1) 0)

/-- In the standard model, the term-parametric graph is precisely Ackermann
adjunction on the values of its three parameter terms. -/
theorem hfAdjoinGraphTermAt_exact (e : Nat → Nat)
    (newCode oldCode elemCode : Term) :
    Sat natModel e (hfAdjoinGraphTermAt newCode oldCode elemCode) ↔
      Term.eval natModel e newCode =
        AckermannHF.adjoin
          (Term.eval natModel e oldCode)
          (Term.eval natModel e elemCode) := by
  constructor
  · intro hgraph
    apply AckermannHF.ext
    intro x
    have hpoint := hgraph x
    rw [Sat_iffForm] at hpoint
    have hor :
        Sat natModel (scons x e)
            (or
              (hfMemTermAt 0 (Term.rename Nat.succ oldCode))
              (eq (Term.var 0) (Term.rename Nat.succ elemCode))) ↔
          (Sat natModel (scons x e)
              (hfMemTermAt 0 (Term.rename Nat.succ oldCode)) ∨
            Sat natModel (scons x e)
              (eq (Term.var 0) (Term.rename Nat.succ elemCode))) :=
      Iff.rfl
    rw [hor] at hpoint
    have heq : Sat natModel (scons x e)
          (eq (Term.var 0) (Term.rename Nat.succ elemCode)) ↔
        x = Term.eval natModel e elemCode := by
      simp [Sat, Term.eval_rename, Term.eval, scons]
    rw [heq] at hpoint
    rw [hfMemTermAt_exact,
      hfMemTermAt_exact] at hpoint
    simpa [Term.eval_rename, Term.eval, scons,
      AckermannHF.mem_adjoin] using hpoint
  · intro hnew x
    rw [Sat_iffForm]
    have hor :
        Sat natModel (scons x e)
            (or
              (hfMemTermAt 0 (Term.rename Nat.succ oldCode))
              (eq (Term.var 0) (Term.rename Nat.succ elemCode))) ↔
          (Sat natModel (scons x e)
              (hfMemTermAt 0 (Term.rename Nat.succ oldCode)) ∨
            Sat natModel (scons x e)
              (eq (Term.var 0) (Term.rename Nat.succ elemCode))) :=
      Iff.rfl
    rw [hor]
    have heq : Sat natModel (scons x e)
          (eq (Term.var 0) (Term.rename Nat.succ elemCode)) ↔
        x = Term.eval natModel e elemCode := by
      simp [Sat, Term.eval_rename, Term.eval, scons]
    rw [heq]
    rw [hfMemTermAt_exact,
      hfMemTermAt_exact]
    simp [hnew, Term.eval_rename, scons,
      AckermannHF.mem_adjoin]

/-- A beta-coded trace of the recursive finite-ordinal code construction.
The sequence starts at the empty code and each successor entry is obtained by
Ackermann adjunction of the current entry to itself. -/
def OrdinalCodeBetaTrace
    (raw coded sequenceCode sequenceStep : Nat) : Prop :=
  BetaEntry sequenceCode sequenceStep 0 0 ∧
    BetaEntry sequenceCode sequenceStep raw coded ∧
      ∀ i, i < raw →
        ∃ current next,
          BetaEntry sequenceCode sequenceStep i current ∧
          BetaEntry sequenceCode sequenceStep (i+1) next ∧
          next = AckermannHF.adjoin current current

theorem OrdinalCodeBetaTrace_value
    {raw coded sequenceCode sequenceStep : Nat}
    (h : OrdinalCodeBetaTrace raw coded sequenceCode sequenceStep) :
    coded = AckermannHF.ordinalCode raw := by
  induction raw generalizing coded with
  | zero =>
      exact BetaEntry_functional h.2.1 h.1
  | succ raw ih =>
      rcases h.2.2 raw (Nat.lt_succ_self raw) with
        ⟨current, next, hcurrent, hnext, hadjoin⟩
      have hprefix : OrdinalCodeBetaTrace
          raw current sequenceCode sequenceStep :=
        ⟨h.1, hcurrent, fun i hi ↦ h.2.2 i (by omega)⟩
      have hcurrentCode : current = AckermannHF.ordinalCode raw :=
        ih hprefix
      have hcodedNext : coded = next :=
        BetaEntry_functional h.2.1 hnext
      calc
        coded = next := hcodedNext
        _ = AckermannHF.adjoin current current := hadjoin
        _ = AckermannHF.adjoin
              (AckermannHF.ordinalCode raw)
              (AckermannHF.ordinalCode raw) := by rw [hcurrentCode]
        _ = AckermannHF.ordinalCode (raw+1) :=
          (AckermannHF.ordinalCode_succ raw).symm

theorem OrdinalCodeBetaTrace_exists (raw : Nat) :
    ∃ sequenceCode sequenceStep,
      OrdinalCodeBetaTrace raw (AckermannHF.ordinalCode raw)
        sequenceCode sequenceStep := by
  let scale : Nat := AckermannHF.ordinalCode raw + 1
  let sequenceStep : Nat := betaFact raw * scale
  have hvalue_le : ∀ i, i ≤ raw →
      AckermannHF.ordinalCode i ≤ AckermannHF.ordinalCode raw := by
    intro i hi
    rcases Nat.lt_or_eq_of_le hi with hlt | rfl
    · exact Nat.le_of_lt (AckermannHF.ordinalCode_lt_of_lt hlt)
    · exact Nat.le_refl _
  have hsmall : ∀ i, i ≤ raw →
      AckermannHF.ordinalCode i < BetaModulus sequenceStep i := by
    intro i hi
    have hltScale : AckermannHF.ordinalCode i < scale := by
      simp only [scale]
      exact Nat.lt_succ_of_le (hvalue_le i hi)
    have hfact : 1 ≤ betaFact raw := betaFact_pos raw
    have hscaleStep : scale ≤ sequenceStep := by
      calc
        scale = 1 * scale := by simp
        _ ≤ betaFact raw * scale := Nat.mul_le_mul_right scale hfact
    have hstepMod : sequenceStep ≤ BetaModulus sequenceStep i := by
      simp only [BetaModulus]
      have hone : 1 ≤ i + 1 := by omega
      have hmul : sequenceStep ≤ (i+1) * sequenceStep := by
        simpa using Nat.mul_le_mul_right sequenceStep hone
      omega
    exact Nat.lt_of_lt_of_le hltScale
      (Nat.le_trans hscaleStep hstepMod)
  rcases beta_entries_exist_through_mul_betaFact
      (N := raw) (scale := scale) AckermannHF.ordinalCode (by
        simpa [sequenceStep] using hsmall) with
    ⟨sequenceCode, hentries⟩
  refine ⟨sequenceCode, sequenceStep, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [sequenceStep, AckermannHF.ordinalCode_zero,
      AckermannHF.empty] using hentries 0 (by omega)
  · exact hentries raw (Nat.le_refl raw)
  · intro i hi
    refine ⟨AckermannHF.ordinalCode i,
      AckermannHF.ordinalCode (i+1), ?_, ?_, ?_⟩
    · exact hentries i (by omega)
    · exact hentries (i+1) (by omega)
    · exact AckermannHF.ordinalCode_succ i

theorem ordinalCodeStepWitnessTermAt_exact
    (e : Nat → Nat) (sequenceCode sequenceStep index : Term) :
    Sat natModel e
        (ordinalCodeStepWitnessTermAt sequenceCode sequenceStep index) ↔
      ∃ current next,
        BetaEntry
            (Term.eval natModel e sequenceCode)
            (Term.eval natModel e sequenceStep)
            (Term.eval natModel e index) current ∧
          BetaEntry
            (Term.eval natModel e sequenceCode)
            (Term.eval natModel e sequenceStep)
            (Term.eval natModel e index + 1) next ∧
          next = AckermannHF.adjoin current current := by
  constructor
  · intro h
    rcases h with ⟨current, next, hcurrent, hnext, hadjoin⟩
    refine ⟨current, next, ?_, ?_, ?_⟩
    · have hraw := (betaTermTermAt_nat_entry
          (scons next (scons current e))
          (Term.var 1)
          (Term.rename (fun n ↦ n+2) sequenceCode)
          (Term.rename (fun n ↦ n+2) sequenceStep)
          (Term.rename (fun n ↦ n+2) index)).mp hcurrent
      simpa [Term.eval_rename, Term.eval, scons] using hraw
    · have hraw := (betaTermTermAt_nat_entry
          (scons next (scons current e))
          (Term.var 0)
          (Term.rename (fun n ↦ n+2) sequenceCode)
          (Term.rename (fun n ↦ n+2) sequenceStep)
          (Term.succ (Term.rename (fun n ↦ n+2) index))).mp hnext
      simpa [Term.eval_rename, Term.eval, natModel, scons] using hraw
    · have hraw := (hfAdjoinGraphTermAt_exact
          (scons next (scons current e))
          (Term.var 0) (Term.var 1) (Term.var 1)).mp hadjoin
      simpa [Term.eval, natModel, scons] using hraw
  · intro h
    rcases h with ⟨current, next, hcurrent, hnext, hadjoin⟩
    refine ⟨current, next, ?_, ?_, ?_⟩
    · apply (betaTermTermAt_nat_entry
        (scons next (scons current e))
        (Term.var 1)
        (Term.rename (fun n ↦ n+2) sequenceCode)
        (Term.rename (fun n ↦ n+2) sequenceStep)
        (Term.rename (fun n ↦ n+2) index)).mpr
      simpa [Term.eval_rename, Term.eval, scons] using hcurrent
    · apply (betaTermTermAt_nat_entry
        (scons next (scons current e))
        (Term.var 0)
        (Term.rename (fun n ↦ n+2) sequenceCode)
        (Term.rename (fun n ↦ n+2) sequenceStep)
        (Term.succ (Term.rename (fun n ↦ n+2) index))).mpr
      simpa [Term.eval_rename, Term.eval, natModel, scons] using hnext
    · apply (hfAdjoinGraphTermAt_exact
        (scons next (scons current e))
        (Term.var 0) (Term.var 1) (Term.var 1)).mpr
      simpa [Term.eval, scons] using hadjoin

theorem ordinalCodeStepsTermAt_exact
    (e : Nat → Nat) (sequenceCode sequenceStep raw : Term) :
    Sat natModel e
        (ordinalCodeStepsTermAt sequenceCode sequenceStep raw) ↔
      ∀ i, i < Term.eval natModel e raw →
        ∃ current next,
          BetaEntry
              (Term.eval natModel e sequenceCode)
              (Term.eval natModel e sequenceStep)
              i current ∧
            BetaEntry
              (Term.eval natModel e sequenceCode)
              (Term.eval natModel e sequenceStep)
              (i+1) next ∧
            next = AckermannHF.adjoin current current := by
  constructor
  · intro h i hi
    have hlt : Sat natModel (scons i e)
        (ltTermAt (Term.var 0) (Term.rename Nat.succ raw)) := by
      apply (ltTermAt_nat (scons i e)
        (Term.var 0) (Term.rename Nat.succ raw)).mpr
      simpa [Term.eval_rename, Term.eval, scons] using hi
    have hstep := h i hlt
    have hspec := (ordinalCodeStepWitnessTermAt_exact
      (scons i e)
      (Term.rename Nat.succ sequenceCode)
      (Term.rename Nat.succ sequenceStep)
      (Term.var 0)).mp hstep
    simpa [Term.eval_rename, Term.eval, scons] using hspec
  · intro h i hlt
    have hiRaw := (ltTermAt_nat (scons i e)
      (Term.var 0) (Term.rename Nat.succ raw)).mp hlt
    have hi : i < Term.eval natModel e raw := by
      simpa [Term.eval_rename, Term.eval, scons] using hiRaw
    have hspec := h i hi
    apply (ordinalCodeStepWitnessTermAt_exact
      (scons i e)
      (Term.rename Nat.succ sequenceCode)
      (Term.rename Nat.succ sequenceStep)
      (Term.var 0)).mpr
    simpa [Term.eval_rename, Term.eval, scons] using hspec

theorem ordinalCodeGraphTermAt_trace_exact
    (e : Nat → Nat) (raw coded : Term) :
    Sat natModel e (ordinalCodeGraphTermAt raw coded) ↔
      ∃ sequenceCode sequenceStep,
        OrdinalCodeBetaTrace
          (Term.eval natModel e raw)
          (Term.eval natModel e coded)
          sequenceCode sequenceStep := by
  constructor
  · intro h
    rcases h with
      ⟨sequenceCode, sequenceStep, hzero, hend, hsteps⟩
    refine ⟨sequenceCode, sequenceStep, ?_, ?_, ?_⟩
    · have hraw := (betaTermTermAt_nat_entry
          (scons sequenceStep (scons sequenceCode e))
          Term.zero (Term.var 1) (Term.var 0) Term.zero).mp hzero
      simpa [Term.eval, natModel, scons] using hraw
    · have hraw := (betaTermTermAt_nat_entry
          (scons sequenceStep (scons sequenceCode e))
          (Term.rename (fun n ↦ n+2) coded)
          (Term.var 1) (Term.var 0)
          (Term.rename (fun n ↦ n+2) raw)).mp hend
      simpa [Term.eval_rename, Term.eval, scons] using hraw
    · have hraw := (ordinalCodeStepsTermAt_exact
          (scons sequenceStep (scons sequenceCode e))
          (Term.var 1) (Term.var 0)
          (Term.rename (fun n ↦ n+2) raw)).mp hsteps
      simpa [Term.eval_rename, Term.eval, scons] using hraw
  · intro h
    rcases h with
      ⟨sequenceCode, sequenceStep, hzero, hend, hsteps⟩
    refine ⟨sequenceCode, sequenceStep, ?_, ?_, ?_⟩
    · apply (betaTermTermAt_nat_entry
        (scons sequenceStep (scons sequenceCode e))
        Term.zero (Term.var 1) (Term.var 0) Term.zero).mpr
      simpa [Term.eval, natModel, scons] using hzero
    · apply (betaTermTermAt_nat_entry
        (scons sequenceStep (scons sequenceCode e))
        (Term.rename (fun n ↦ n+2) coded)
        (Term.var 1) (Term.var 0)
        (Term.rename (fun n ↦ n+2) raw)).mpr
      simpa [Term.eval_rename, Term.eval, scons] using hend
    · apply (ordinalCodeStepsTermAt_exact
        (scons sequenceStep (scons sequenceCode e))
        (Term.var 1) (Term.var 0)
        (Term.rename (fun n ↦ n+2) raw)).mpr
      simpa [Term.eval_rename, Term.eval, scons] using hsteps

theorem ordinalCodeGraphTermAt_exact
    (e : Nat → Nat) (raw coded : Term) :
    Sat natModel e (ordinalCodeGraphTermAt raw coded) ↔
      Term.eval natModel e coded =
        AckermannHF.ordinalCode (Term.eval natModel e raw) := by
  constructor
  · intro h
    rcases (ordinalCodeGraphTermAt_trace_exact e raw coded).mp h with
      ⟨sequenceCode, sequenceStep, htrace⟩
    exact OrdinalCodeBetaTrace_value htrace
  · intro h
    rcases OrdinalCodeBetaTrace_exists (Term.eval natModel e raw) with
      ⟨sequenceCode, sequenceStep, htrace⟩
    apply (ordinalCodeGraphTermAt_trace_exact e raw coded).mpr
    refine ⟨sequenceCode, sequenceStep, ?_⟩
    simpa [h] using htrace

theorem ordinalCodeGraphAt_exact
    (e : Nat → Nat) (raw coded : Nat) :
    Sat natModel e (ordinalCodeGraphAt raw coded) ↔
      e coded = AckermannHF.ordinalCode (e raw) := by
  simpa [ordinalCodeGraphAt, Term.eval] using
    (ordinalCodeGraphTermAt_exact e (Term.var raw) (Term.var coded))

/-- The coded-ordinal domain appearing in the PA-side composite. -/
def codedOrdinalDomain : Formula :=
  translateHFFormula AckermannHF.PAInHF.domainForm

theorem codedOrdinalDomain_exact (e : Nat → Nat) :
    Sat natModel e codedOrdinalDomain ↔
      ∃ raw, AckermannHF.ordinalCode raw = e 0 :=
  (translateHFFormula_exact AckermannHF.PAInHF.domainForm e).trans
    (AckermannHF.PAInHF.domain_exact e)

/-- Closed totality sentence for the internal ordinal-code graph. -/
def ordinalCodeGraphTotal : Formula :=
  all (ex (ordinalCodeGraphAt 1 0))

/-- Closed range characterization: the graph hits exactly the relativized
coded-ordinal domain. -/
def ordinalCodeGraphRange : Formula :=
  all
    (iffForm codedOrdinalDomain
      (ex (ordinalCodeGraphAt 0 1)))

theorem standard_sat_ordinalCodeGraphTotal (e : Nat → Nat) :
    Sat natModel e ordinalCodeGraphTotal := by
  intro raw
  refine ⟨AckermannHF.ordinalCode raw, ?_⟩
  apply (ordinalCodeGraphAt_exact
    (scons (AckermannHF.ordinalCode raw) (scons raw e)) 1 0).mpr
  simp [scons]

theorem standard_sat_ordinalCodeGraphRange (e : Nat → Nat) :
    Sat natModel e ordinalCodeGraphRange := by
  intro coded
  rw [Sat_iffForm]
  constructor
  · intro hdomain
    rcases (codedOrdinalDomain_exact (scons coded e)).mp hdomain with
      ⟨raw, hraw⟩
    refine ⟨raw, ?_⟩
    apply (ordinalCodeGraphAt_exact
      (scons raw (scons coded e)) 0 1).mpr
    simpa [Term.eval, scons] using hraw.symm
  · intro hgraph
    rcases hgraph with ⟨raw, hraw⟩
    have hcode := (ordinalCodeGraphAt_exact
      (scons raw (scons coded e)) 0 1).mp hraw
    apply (codedOrdinalDomain_exact (scons coded e)).mpr
    refine ⟨raw, ?_⟩
    simpa [Term.eval, scons] using hcode.symm

/-- HF slot map used for a translated term graph: slot `0` is the graph
output, and slot `n+1` contains the code paired with raw PA variable `n`. -/
def codedTermSlotMap (codedOut : Nat) (codedMap : Nat → Nat) : Nat → Nat
  | 0 => codedOut
  | n+1 => codedMap n

/-- Reverse-translate the finite-ordinal graph of a PA term while selecting
explicit PA slots for the coded inputs and output. -/
def compositeTermGraphAt
    (codedOut : Nat) (codedMap : Nat → Nat) (t : Term) : Formula :=
  hfFormulaAt (codedTermSlotMap codedOut codedMap)
    (AckermannHF.PAInHF.termGraphAt (fun n ↦ n+1) 0 t)

/-- Formula-level composite with an explicit map from intermediate HF slots
to the PA slots containing their ordinal codes. -/
def paCompositeAt (codedMap : Nat → Nat) (phi : Formula) : Formula :=
  hfFormulaAt codedMap
    (AckermannHF.PAInHF.formulaAt (fun n : Nat ↦ n) phi)

theorem paCompositeAt_id (phi : Formula) :
    paCompositeAt (fun n : Nat ↦ n) phi =
      translateHFFormula (AckermannHF.PAInHF.translateFormula phi) := rfl

/-- The translated coded-ordinal domain is unchanged by the slot-map lift
introduced for a surrounding PA quantifier. -/
theorem hfFormulaAt_domain_up_eq_codedOrdinalDomain
    (codedMap : Nat → Nat) :
    hfFormulaAt (hfUpVarMap codedMap)
        AckermannHF.PAInHF.domainForm =
      codedOrdinalDomain := by
  unfold codedOrdinalDomain translateHFFormula
  apply hfFormulaAt_ext_free
  intro n hn
  have hn0 := AckermannHF.PAInHF.domainForm_free hn
  subst n
  rfl

theorem PAInHF_formulaAt_up_id (phi : Formula) :
    AckermannHF.PAInHF.formulaAt
        (AckermannHF.PAInHF.upVarMap (fun n : Nat ↦ n)) phi =
      AckermannHF.PAInHF.formulaAt (fun n : Nat ↦ n) phi := by
  apply AckermannHF.PAInHF.formulaAt_map_ext
  intro n
  cases n <;> rfl

/-- Universal PA composites quantify over exactly the translated coded
ordinal domain. -/
theorem paCompositeAt_all_normalForm
    (codedMap : Nat → Nat) (phi : Formula) :
    paCompositeAt codedMap (all phi) =
      all (imp codedOrdinalDomain
        (paCompositeAt (hfUpVarMap codedMap) phi)) := by
  simp only [paCompositeAt, AckermannHF.PAInHF.formulaAt,
    hfFormulaAt]
  rw [hfFormulaAt_domain_up_eq_codedOrdinalDomain]
  rw [PAInHF_formulaAt_up_id]

/-- Existential PA composites quantify over exactly the translated coded
ordinal domain. -/
theorem paCompositeAt_ex_normalForm
    (codedMap : Nat → Nat) (phi : Formula) :
    paCompositeAt codedMap (ex phi) =
      ex (and codedOrdinalDomain
        (paCompositeAt (hfUpVarMap codedMap) phi)) := by
  simp only [paCompositeAt, AckermannHF.PAInHF.formulaAt,
    hfFormulaAt]
  rw [hfFormulaAt_domain_up_eq_codedOrdinalDomain]
  rw [PAInHF_formulaAt_up_id]

/-- Paired slot map used after opening a coded ordinal by the range theorem:
the raw witness is slot `0`, the coded value is slot `1`, and outer raw
variables have moved through both binders. -/
def rangeRawMap (rawMap : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => rawMap n + 2

def rangeCodedMap (codedMap : Nat → Nat) : Nat → Nat
  | 0 => 1
  | n+1 => codedMap n + 2

/-- Paired slot map used after totality chooses a code for a bound raw value:
the coded witness is slot `0`, the raw value is slot `1`, and outer variables
have moved through both binders. -/
def totalRawMap (rawMap : Nat → Nat) : Nat → Nat
  | 0 => 1
  | n+1 => rawMap n + 2

def totalCodedMap (codedMap : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => codedMap n + 2

theorem rename_paCompositeAt
    (r : Nat → Nat) (codedMap : Nat → Nat) (phi : Formula) :
    rename r (paCompositeAt codedMap phi) =
      paCompositeAt (fun n ↦ r (codedMap n)) phi := by
  simpa [paCompositeAt] using
    (rename_hfFormulaAt
      (AckermannHF.PAInHF.formulaAt (fun n : Nat ↦ n) phi)
      codedMap r)

theorem rename_succ_paCompositeAt_up
    (codedMap : Nat → Nat) (phi : Formula) :
    rename Nat.succ
        (paCompositeAt (hfUpVarMap codedMap) phi) =
      paCompositeAt (rangeCodedMap codedMap) phi := by
  rw [rename_paCompositeAt]
  apply congrArg (fun m ↦ paCompositeAt m phi)
  funext n
  cases n <;> rfl

theorem rename_succ_rawBody
    (rawMap : Nat → Nat) (phi : Formula) :
    rename Nat.succ
        (rename (AckermannHF.PAInHF.upVarMap rawMap) phi) =
      rename (totalRawMap rawMap) phi := by
  rw [rename_comp]
  apply rename_ext
  intro n
  cases n <;> rfl

theorem subst_instTerm_range_rawBody
    (rawMap : Nat → Nat) (phi : Formula) :
    subst (instTerm (Term.var 0))
        (rename (SetTheory.up Nat.succ)
          (rename (SetTheory.up Nat.succ)
            (rename (AckermannHF.PAInHF.upVarMap rawMap) phi))) =
      rename (rangeRawMap rawMap) phi := by
  rw [subst_instTerm_var_zero_rename_up_succ]
  rw [rename_comp]
  apply rename_ext
  intro n
  cases n <;> rfl

theorem subst_instTerm_total_codedBody
    (codedMap : Nat → Nat) (phi : Formula) :
    subst (instTerm (Term.var 0))
        (rename (SetTheory.up Nat.succ)
          (rename (SetTheory.up Nat.succ)
            (paCompositeAt (hfUpVarMap codedMap) phi))) =
      paCompositeAt (totalCodedMap codedMap) phi := by
  rw [subst_instTerm_var_zero_rename_up_succ]
  rw [rename_paCompositeAt]
  apply congrArg (fun m ↦ paCompositeAt m phi)
  funext n
  cases n <;> rfl

/-- Exact syntactic Code-graph frontier.

The first three fields are the graph's totality/range/injectivity kit.  The
last field is the sole term-language compatibility theorem needed to reduce
composite equality atoms to the Code relation. -/
structure OrdinalCodeGraphProofs where
  total : ∀ (G : List Formula) (raw : Term),
    BProv Ax_s G
      (ex (ordinalCodeGraphTermAt
        (Term.rename Nat.succ raw) (Term.var 0)))
  range : ∀ (G : List Formula) (coded : Term),
    BProv Ax_s G
      (iffForm
        (subst (instTerm coded) codedOrdinalDomain)
        (ex (ordinalCodeGraphTermAt
          (Term.var 0) (Term.rename Nat.succ coded))))
  injective : ∀ {G : List Formula} {raw₁ raw₂ coded : Term},
    BProv Ax_s G (ordinalCodeGraphTermAt raw₁ coded) →
    BProv Ax_s G (ordinalCodeGraphTermAt raw₂ coded) →
    BProv Ax_s G (eq raw₁ raw₂)
  term_graph : ∀ (G : List Formula) (t : Term)
      (rawMap codedMap : Nat → Nat) (codedOut : Nat),
    (∀ n, Term.Free n t →
      BProv Ax_s G (ordinalCodeGraphAt (rawMap n) (codedMap n))) →
    BProv Ax_s G
      (iffForm
        (compositeTermGraphAt codedOut codedMap t)
        (ordinalCodeGraphTermAt
          (Term.rename rawMap t) (Term.var codedOut)))

theorem codedOrdinalDomain_free
    {i : Nat} (h : Free i codedOrdinalDomain) : i = 0 := by
  rcases hfFormulaAt_free AckermannHF.PAInHF.domainForm h with
    ⟨n, hn, hi⟩
  have hn0 := AckermannHF.PAInHF.domainForm_free hn
  exact hi.trans hn0

theorem subst_instTerm_var_zero_codedOrdinalDomain :
    subst (instTerm (Term.var 0)) codedOrdinalDomain =
      codedOrdinalDomain := by
  rw [subst_instTerm_var]
  calc
    rename (SetTheory.inst 0) codedOrdinalDomain =
        rename (fun n : Nat ↦ n) codedOrdinalDomain := by
      apply rename_ext_free
      intro n hn
      have hn0 := codedOrdinalDomain_free hn
      subst n
      rfl
    _ = codedOrdinalDomain := rename_id codedOrdinalDomain

/-- Instantiating the current coded witness after two surrounding proof
binders recovers the coded-ordinal domain formula. -/
theorem subst_instTerm_total_codedOrdinalDomain :
    subst (instTerm (Term.var 0))
        (rename (SetTheory.up Nat.succ)
          (rename (SetTheory.up Nat.succ) codedOrdinalDomain)) =
      codedOrdinalDomain := by
  rw [subst_instTerm_var_zero_rename_up_succ]
  calc
    rename (SetTheory.up Nat.succ) codedOrdinalDomain =
        rename (fun n : Nat ↦ n) codedOrdinalDomain := by
      apply rename_ext_free
      intro n hn
      have hn0 := codedOrdinalDomain_free hn
      subst n
      rfl
    _ = codedOrdinalDomain := rename_id codedOrdinalDomain

/-- Use the range equivalence to open an arbitrary coded ordinal as the Code
of a raw PA value. -/
theorem BProv_Ax_s_ordinalCodeGraph_range_of_domain
    (P : OrdinalCodeGraphProofs)
    {G : List Formula} {coded : Term}
    (hdomain : BProv Ax_s G
      (subst (instTerm coded) codedOrdinalDomain)) :
    BProv Ax_s G
      (ex (ordinalCodeGraphTermAt
        (Term.var 0) (Term.rename Nat.succ coded))) := by
  have hrange := P.range G coded
  have hforward : BProv Ax_s G
      (imp
        (subst (instTerm coded) codedOrdinalDomain)
        (ex (ordinalCodeGraphTermAt
          (Term.var 0) (Term.rename Nat.succ coded)))) := by
    simpa [iffForm] using BProv_andE1 hrange
  exact BProv_mp Ax_s G _ _ hforward hdomain

/-- Conditional structural formula-induction package.  Its `formula_exact`
field is the logical induction driven by `OrdinalCodeGraphProofs`; keeping it
separate makes the remaining de Bruijn/context plumbing explicit. -/
structure PACompositeStructuralProofs extends OrdinalCodeGraphProofs where
  formula_exact : ∀ (G : List Formula) (phi : Formula)
      (rawMap codedMap : Nat → Nat),
    (∀ n, Free n phi →
      BProv Ax_s G (ordinalCodeGraphAt (rawMap n) (codedMap n))) →
    BProv Ax_s G
      (iffForm (rename rawMap phi) (paCompositeAt codedMap phi))

/-- A completed paired-variable structural induction immediately closes the
PA composite identity on sentences. -/
theorem BProv_Ax_s_pa_roundTrip_of_structuralProofs
    (P : PACompositeStructuralProofs)
    (phi : Formula) (hphi : Sentence phi) :
    BProv Ax_s []
      (iffForm phi
        (translateHFFormula
          (AckermannHF.PAInHF.translateFormula phi))) := by
  have h := P.formula_exact [] phi
    (fun n : Nat ↦ n) (fun n : Nat ↦ n)
    (fun n hn ↦ False.elim (hphi n hn))
  simpa [paCompositeAt_id, rename_id] using h

/-- The β-trace recurrence is vacuous at raw input zero. -/
theorem BProv_Ax_s_ordinalCodeStepsTermAt_zero
    {G : List Formula} (sequenceCode sequenceStep : Term) :
    BProv Ax_s G
      (ordinalCodeStepsTermAt sequenceCode sequenceStep Term.zero) := by
  let antecedent : Formula := ltTermAt (Term.var 0) Term.zero
  let consequent : Formula :=
    ordinalCodeStepWitnessTermAt
      (Term.rename Nat.succ sequenceCode)
      (Term.rename Nat.succ sequenceStep)
      (Term.var 0)
  let body : Formula := imp antecedent consequent
  have hbody : BProv Ax_s
      (antecedent :: G.map (rename Nat.succ)) consequent := by
    let C : List Formula := antecedent :: G.map (rename Nat.succ)
    have hlt : BProv Ax_s C
        (ltTermAt (Term.var 0) Term.zero) := by
      simpa [C, antecedent] using
        (BProv_ass (B := Ax_s) (G := C) (by simp [C, antecedent]))
    have hle : BProv Ax_s C
        (leTermAt Term.zero (Term.var 0)) :=
      BProv_Ax_s_leTermAt_zero_left (Term.var 0)
    have hbot : BProv Ax_s C bot :=
      BProv_Ax_s_ltTermAt_leTermAt_bot hlt hle
    exact BProv_botE (B := Ax_s) (G := C)
      (a := consequent) hbot
  have himp : BProv Ax_s (G.map (rename Nat.succ)) body := by
    simpa [body] using BProv_impI hbody
  have hall : BProv Ax_s G (all body) :=
    BProv_allI_of_sentences (B := Ax_s)
      Ax_s_sentences himp
  simpa [ordinalCodeStepsTermAt, body, antecedent, consequent,
    Term.rename] using hall

/-- Binder-free body used to package the two beta-sequence witnesses. -/
def ordinalCodeGraphBodyTermAt
    (sequenceCode sequenceStep raw coded : Term) : Formula :=
  and
    (betaTermTermAt Term.zero sequenceCode sequenceStep Term.zero)
    (and
      (betaTermTermAt coded sequenceCode sequenceStep raw)
      (ordinalCodeStepsTermAt sequenceCode sequenceStep raw))

theorem subst_ordinalCodeGraphBodyTermAt
    (sigma : Nat → Term)
    (sequenceCode sequenceStep raw coded : Term) :
    subst sigma
        (ordinalCodeGraphBodyTermAt
          sequenceCode sequenceStep raw coded) =
      ordinalCodeGraphBodyTermAt
        (Term.subst sigma sequenceCode)
        (Term.subst sigma sequenceStep)
        (Term.subst sigma raw)
        (Term.subst sigma coded) := by
  simp [ordinalCodeGraphBodyTermAt,
    subst_betaTermTermAt,
    subst_ordinalCodeStepsTermAt, subst, Term.subst]

theorem rename_ordinalCodeGraphBodyTermAt
    (r : Nat → Nat)
    (sequenceCode sequenceStep raw coded : Term) :
    rename r
        (ordinalCodeGraphBodyTermAt
          sequenceCode sequenceStep raw coded) =
      ordinalCodeGraphBodyTermAt
        (Term.rename r sequenceCode)
        (Term.rename r sequenceStep)
        (Term.rename r raw)
        (Term.rename r coded) := by
  rw [← subst_var_rename,
    subst_ordinalCodeGraphBodyTermAt]
  simp only [term_subst_var_rename]

/-- Instantiating the inner graph binder supplies the sequence-step term. -/
theorem subst_instTerm_ordinalCodeGraphBody_inner
    (sequenceCode sequenceStep raw coded : Term) :
    subst (instTerm sequenceStep)
        (ordinalCodeGraphBodyTermAt
          (Term.rename Nat.succ sequenceCode)
          (Term.var 0)
          (Term.rename Nat.succ raw)
          (Term.rename Nat.succ coded)) =
      ordinalCodeGraphBodyTermAt
        sequenceCode sequenceStep raw coded := by
  rw [subst_ordinalCodeGraphBodyTermAt]
  simp [instTerm, Term.subst, term_subst_instTerm_rename_succ]

/-- Instantiating the outer graph binder supplies the sequence-code term while
leaving the inner sequence-step binder protected. -/
theorem subst_instTerm_ordinalCodeGraphBody_outer
    (sequenceCode raw coded : Term) :
    subst (instTerm sequenceCode)
        (ex (ordinalCodeGraphBodyTermAt
          (Term.var 1)
          (Term.var 0)
          (Term.rename (fun n ↦ n+2) raw)
          (Term.rename (fun n ↦ n+2) coded))) =
      ex (ordinalCodeGraphBodyTermAt
        (Term.rename Nat.succ sequenceCode)
        (Term.var 0)
        (Term.rename Nat.succ raw)
        (Term.rename Nat.succ coded)) := by
  simp only [subst, subst_ordinalCodeGraphBodyTermAt]
  simp [instTerm, Term.subst, Term.upSubst,
    term_subst_upSubst_instTerm_rename_two_succ]

/-- Package explicit beta-sequence code and step terms into the internal
ordinal-code graph's two existential binders. -/
theorem BProv_ordinalCodeGraphTermAt_of_body
    {B : Formula → Prop} {G : List Formula}
    {sequenceCode sequenceStep raw coded : Term}
    (hbody : BProv B G
      (ordinalCodeGraphBodyTermAt
        sequenceCode sequenceStep raw coded)) :
    BProv B G (ordinalCodeGraphTermAt raw coded) := by
  have hinnerInst : BProv B G
      (subst (instTerm sequenceStep)
        (ordinalCodeGraphBodyTermAt
          (Term.rename Nat.succ sequenceCode)
          (Term.var 0)
          (Term.rename Nat.succ raw)
          (Term.rename Nat.succ coded))) := by
    rw [subst_instTerm_ordinalCodeGraphBody_inner]
    exact hbody
  have hinner : BProv B G
      (ex (ordinalCodeGraphBodyTermAt
        (Term.rename Nat.succ sequenceCode)
        (Term.var 0)
        (Term.rename Nat.succ raw)
        (Term.rename Nat.succ coded))) :=
    BProv_exI (B := B) (G := G) hinnerInst
  have houterInst : BProv B G
      (subst (instTerm sequenceCode)
        (ex (ordinalCodeGraphBodyTermAt
          (Term.var 1)
          (Term.var 0)
          (Term.rename (fun n ↦ n+2) raw)
          (Term.rename (fun n ↦ n+2) coded)))) := by
    rw [subst_instTerm_ordinalCodeGraphBody_outer]
    exact hinner
  have hgraph : BProv B G
      (ex (ex (ordinalCodeGraphBodyTermAt
        (Term.var 1)
        (Term.var 0)
        (Term.rename (fun n ↦ n+2) raw)
        (Term.rename (fun n ↦ n+2) coded)))) :=
    BProv_exI (B := B) (G := G) houterInst
  simpa [ordinalCodeGraphTermAt,
    ordinalCodeGraphBodyTermAt] using hgraph

/-! ### Ordinal-code graph functionality reduction -/

/-- Eliminate the two beta-sequence witnesses of an ordinal-code graph while
keeping the fully opened trace body available as a finite-context assumption. -/
theorem BProv_Ax_s_ordinalCodeGraphTermAt_elim_opened
    {G : List Formula} {raw coded : Term} {target : Formula}
    (hgraph : BProv Ax_s G (ordinalCodeGraphTermAt raw coded))
    (hopened :
      let body : Formula :=
        ordinalCodeGraphBodyTermAt
          (Term.var 1) (Term.var 0)
          (Term.rename (fun n ↦ n+2) raw)
          (Term.rename (fun n ↦ n+2) coded)
      let inner : Formula := ex body
      BProv Ax_s
        (body :: (inner :: G.map (rename Nat.succ)).map (rename Nat.succ))
        (rename Nat.succ (rename Nat.succ target))) :
    BProv Ax_s G target := by
  let body : Formula :=
    ordinalCodeGraphBodyTermAt
      (Term.var 1) (Term.var 0)
      (Term.rename (fun n ↦ n+2) raw)
      (Term.rename (fun n ↦ n+2) coded)
  have hgraph' : BProv Ax_s G (ex (ex body)) := by
    simpa [ordinalCodeGraphTermAt, ordinalCodeGraphBodyTermAt,
      body] using hgraph
  exact BProv_two_exE_of_sentences (B := Ax_s)
    Ax_s_sentences hgraph' (by simpa [body] using hopened)

/-- The genuine internal induction frontier: two explicit beta traces with a
common raw bound have equal endpoints. -/
def OrdinalCodeGraphBodyFunctional : Prop :=
  ∀ {G : List Formula}
      {sequenceCode₁ sequenceStep₁ sequenceCode₂ sequenceStep₂
        raw coded₁ coded₂ : Term},
    BProv Ax_s G
      (ordinalCodeGraphBodyTermAt
        sequenceCode₁ sequenceStep₁ raw coded₁) →
    BProv Ax_s G
      (ordinalCodeGraphBodyTermAt
        sequenceCode₂ sequenceStep₂ raw coded₂) →
    BProv Ax_s G (eq coded₁ coded₂)

/-- Opened-trace functionality lifts through all four existential sequence
witnesses to functionality of the public ordinal-code graph. -/
theorem BProv_Ax_s_ordinalCodeGraphTermAt_functional_of_body
    (hbodyFunctional : OrdinalCodeGraphBodyFunctional)
    {G : List Formula} {raw coded₁ coded₂ : Term}
    (hgraph₁ : BProv Ax_s G
      (ordinalCodeGraphTermAt raw coded₁))
    (hgraph₂ : BProv Ax_s G
      (ordinalCodeGraphTermAt raw coded₂)) :
    BProv Ax_s G (eq coded₁ coded₂) := by
  let body₁ : Formula :=
    ordinalCodeGraphBodyTermAt
      (Term.var 1) (Term.var 0)
      (Term.rename (fun n ↦ n+2) raw)
      (Term.rename (fun n ↦ n+2) coded₁)
  let inner₁ : Formula := ex body₁
  refine BProv_Ax_s_ordinalCodeGraphTermAt_elim_opened
    (raw := raw) (coded := coded₁)
    (target := eq coded₁ coded₂) hgraph₁ ?_
  let A : List Formula :=
    body₁ :: (inner₁ :: G.map (rename Nat.succ)).map (rename Nat.succ)
  have hbody₁A : BProv Ax_s A body₁ :=
    BProv_ass (B := Ax_s) (G := A) (by simp [A])
  have hgraph₂A0 := BProv_lift_two_contexts_of_sentences
    (B := Ax_s) Ax_s_sentences
    (outer := inner₁) (inner := body₁) hgraph₂
  have hgraph₂A : BProv Ax_s A
      (ordinalCodeGraphTermAt
        (Term.rename (fun n ↦ n+2) raw)
        (Term.rename (fun n ↦ n+2) coded₂)) := by
    simpa [A, body₁, inner₁,
      rename_ordinalCodeGraphTermAt,
      Term.rename, Term.rename_comp, List.map_map,
      Function.comp_def, Nat.add_assoc] using hgraph₂A0
  let raw₂ : Term := Term.rename (fun n ↦ n+2) raw
  let coded₁₂ : Term := Term.rename (fun n ↦ n+2) coded₁
  let coded₂₂ : Term := Term.rename (fun n ↦ n+2) coded₂
  let body₂ : Formula :=
    ordinalCodeGraphBodyTermAt
      (Term.var 1) (Term.var 0)
      (Term.rename (fun n ↦ n+2) raw₂)
      (Term.rename (fun n ↦ n+2) coded₂₂)
  let inner₂ : Formula := ex body₂
  have hnested : BProv Ax_s A (eq coded₁₂ coded₂₂) := by
    refine BProv_Ax_s_ordinalCodeGraphTermAt_elim_opened
      (G := A) (raw := raw₂) (coded := coded₂₂)
      (target := eq coded₁₂ coded₂₂)
      (by simpa [raw₂, coded₂₂] using hgraph₂A) ?_
    let B : List Formula :=
      body₂ :: (inner₂ :: A.map (rename Nat.succ)).map (rename Nat.succ)
    have hbody₂B : BProv Ax_s B body₂ :=
      BProv_ass (B := Ax_s) (G := B) (by simp [B])
    have hbody₁B0 := BProv_lift_two_contexts_of_sentences
      (B := Ax_s) Ax_s_sentences
      (outer := inner₂) (inner := body₂) hbody₁A
    let raw₄ : Term := Term.rename (fun n ↦ n+4) raw
    let coded₁₄ : Term := Term.rename (fun n ↦ n+4) coded₁
    let coded₂₄ : Term := Term.rename (fun n ↦ n+4) coded₂
    have hbody₁B : BProv Ax_s B
        (ordinalCodeGraphBodyTermAt
          (Term.var 3) (Term.var 2) raw₄ coded₁₄) := by
      simpa [B, A, body₁, inner₁, body₂, inner₂,
        raw₄, coded₁₄, rename_ordinalCodeGraphBodyTermAt,
        Term.rename, Term.rename_comp, List.map_map,
        Function.comp_def, Nat.add_assoc] using hbody₁B0
    have hbody₂B' : BProv Ax_s B
        (ordinalCodeGraphBodyTermAt
          (Term.var 1) (Term.var 0) raw₄ coded₂₄) := by
      simpa [body₂, raw₂, coded₂₂,
        raw₄, coded₂₄, Term.rename_comp,
        Function.comp_def, Nat.add_assoc] using hbody₂B
    have heq : BProv Ax_s B (eq coded₁₄ coded₂₄) :=
      hbodyFunctional hbody₁B hbody₂B'
    simpa [B, body₂, inner₂,
      coded₁₂, coded₂₂, coded₁₄, coded₂₄,
      rename, Term.rename_comp, Function.comp_def, Nat.add_assoc] using heq
  simpa [A, body₁, inner₁, coded₁₂, coded₂₂,
    rename, Term.rename_comp, Function.comp_def, Nat.add_assoc] using hnested

/-- Two beta traces agree at a selected index, with both current values named
explicitly.  Proving this at the common raw endpoint is the true recurrence
induction needed for graph functionality. -/
def ordinalCodeTraceAgreementAt
    (sequenceCode₁ sequenceStep₁ sequenceCode₂ sequenceStep₂
      index : Term) : Formula :=
  ex (ex
    (and
      (betaTermTermAt (Term.var 1)
        (Term.rename (fun n ↦ n+2) sequenceCode₁)
        (Term.rename (fun n ↦ n+2) sequenceStep₁)
        (Term.rename (fun n ↦ n+2) index))
      (and
        (betaTermTermAt (Term.var 0)
          (Term.rename (fun n ↦ n+2) sequenceCode₂)
          (Term.rename (fun n ↦ n+2) sequenceStep₂)
          (Term.rename (fun n ↦ n+2) index))
        (eq (Term.var 1) (Term.var 0)))))

/-- Pointwise trace agreement at the endpoint, together with each trace's own
endpoint beta entry, forces equality of the two advertised outputs. -/
theorem BProv_Ax_s_eq_of_ordinalCodeTraceAgreementAt
    {G : List Formula}
    {sequenceCode₁ sequenceStep₁ sequenceCode₂ sequenceStep₂
      raw coded₁ coded₂ : Term}
    (hendpoint₁ : BProv Ax_s G
      (betaTermTermAt coded₁ sequenceCode₁ sequenceStep₁ raw))
    (hendpoint₂ : BProv Ax_s G
      (betaTermTermAt coded₂ sequenceCode₂ sequenceStep₂ raw))
    (hagreement : BProv Ax_s G
      (ordinalCodeTraceAgreementAt
        sequenceCode₁ sequenceStep₁ sequenceCode₂ sequenceStep₂
        raw)) :
    BProv Ax_s G (eq coded₁ coded₂) := by
  let body : Formula :=
    and
      (betaTermTermAt (Term.var 1)
        (Term.rename (fun n ↦ n+2) sequenceCode₁)
        (Term.rename (fun n ↦ n+2) sequenceStep₁)
        (Term.rename (fun n ↦ n+2) raw))
      (and
        (betaTermTermAt (Term.var 0)
          (Term.rename (fun n ↦ n+2) sequenceCode₂)
          (Term.rename (fun n ↦ n+2) sequenceStep₂)
          (Term.rename (fun n ↦ n+2) raw))
        (eq (Term.var 1) (Term.var 0)))
  have hagreement' : BProv Ax_s G (ex (ex body)) := by
    simpa [ordinalCodeTraceAgreementAt, body] using hagreement
  refine BProv_two_exE_of_sentences
    (B := Ax_s) Ax_s_sentences hagreement' ?_
  let D : List Formula :=
    body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
  have hbody : BProv Ax_s D body :=
    BProv_ass (B := Ax_s) (G := D) (by simp [D])
  have hcurrent₁ : BProv Ax_s D
      (betaTermTermAt (Term.var 1)
        (Term.rename (fun n ↦ n+2) sequenceCode₁)
        (Term.rename (fun n ↦ n+2) sequenceStep₁)
        (Term.rename (fun n ↦ n+2) raw)) := by
    simpa [body] using BProv_andE1 hbody
  have htail : BProv Ax_s D
      (and
        (betaTermTermAt (Term.var 0)
          (Term.rename (fun n ↦ n+2) sequenceCode₂)
          (Term.rename (fun n ↦ n+2) sequenceStep₂)
          (Term.rename (fun n ↦ n+2) raw))
        (eq (Term.var 1) (Term.var 0))) := by
    simpa [body] using BProv_andE2 hbody
  have hcurrent₂ := BProv_andE1 htail
  have hcurrentEq := BProv_andE2 htail
  have hendpoint₁D0 := BProv_lift_two_contexts_of_sentences
    (B := Ax_s) Ax_s_sentences
    (outer := ex body) (inner := body) hendpoint₁
  have hendpoint₁D : BProv Ax_s D
      (betaTermTermAt
        (Term.rename (fun n ↦ n+2) coded₁)
        (Term.rename (fun n ↦ n+2) sequenceCode₁)
        (Term.rename (fun n ↦ n+2) sequenceStep₁)
        (Term.rename (fun n ↦ n+2) raw)) := by
    simpa [D, body, rename_betaTermTermAt,
      Term.rename, Term.rename_comp, List.map_map,
      Function.comp_def, Nat.add_assoc] using hendpoint₁D0
  have hendpoint₂D0 := BProv_lift_two_contexts_of_sentences
    (B := Ax_s) Ax_s_sentences
    (outer := ex body) (inner := body) hendpoint₂
  have hendpoint₂D : BProv Ax_s D
      (betaTermTermAt
        (Term.rename (fun n ↦ n+2) coded₂)
        (Term.rename (fun n ↦ n+2) sequenceCode₂)
        (Term.rename (fun n ↦ n+2) sequenceStep₂)
        (Term.rename (fun n ↦ n+2) raw)) := by
    simpa [D, body, rename_betaTermTermAt,
      Term.rename, Term.rename_comp, List.map_map,
      Function.comp_def, Nat.add_assoc] using hendpoint₂D0
  have hcurrent₁ToEndpoint : BProv Ax_s D
      (eq (Term.var 1)
        (Term.rename (fun n ↦ n+2) coded₁)) :=
    BProv_Ax_s_eq_of_betaTermTermAt_betaTermTermAt_same_index
      hendpoint₁D hcurrent₁
  have hcurrent₂ToEndpoint : BProv Ax_s D
      (eq (Term.var 0)
        (Term.rename (fun n ↦ n+2) coded₂)) :=
    BProv_Ax_s_eq_of_betaTermTermAt_betaTermTermAt_same_index
      hendpoint₂D hcurrent₂
  have heq : BProv Ax_s D
      (eq
        (Term.rename (fun n ↦ n+2) coded₁)
        (Term.rename (fun n ↦ n+2) coded₂)) :=
    BProv_eqTrans (BProv_eqSym hcurrent₁ToEndpoint)
      (BProv_eqTrans hcurrentEq hcurrent₂ToEndpoint)
  simpa [D, body, rename, Term.rename_comp,
    Function.comp_def, Nat.add_assoc] using heq

/-- Term-parametric specialization of translated HF extensionality: two
Ackermann codes with exactly the same members are equal. -/
theorem BProv_Ax_s_eq_of_hfSameMembersTermAt
    {G : List Formula} {left right : Term}
    (hsame : BProv Ax_s G
      (all
        (iffForm
          (hfMemTermAt 0 (Term.rename Nat.succ left))
          (hfMemTermAt 0 (Term.rename Nat.succ right))))) :
    BProv Ax_s G (eq left right) := by
  have hext0 := BProv_weaken_nil
    (G := G) BProv_Ax_s_translated_HF_extensionality
  let extBody : Formula :=
    all (all
      (imp
        (all (iffForm (hfMemAt 0 2) (hfMemAt 0 1)))
        (eq (Term.var 1) (Term.var 0))))
  let k : Nat := SetTheory.bound AckermannHF.HF_extensionality_form
  have hextClosed : BProv Ax_s G (closeN k extBody) := by
    set_option maxRecDepth 10000 in
    simpa [k, extBody, translateHFFormula,
      AckermannHF.HF_extensionality_form,
      SetTheory.sealF, SetTheory.closeN, SetTheory.bound,
      hfFormulaAt, hfUpVarMap, SetTheory.fIff, iffForm, closeN]
      using hext0
  have hHFsentence :
      SetTheory.Sentence AckermannHF.HF_extensionality_form := by
    intro n hn
    simp [AckermannHF.HF_extensionality_form,
      SetTheory.fIff, SetTheory.Free] at hn
  have hextSentence : Sentence extBody := by
    have htranslated :=
      translateHFFormula_sentence_of_HF_sentence
        AckermannHF.HF_extensionality_form hHFsentence
    have heq :
        extBody =
          translateHFFormula AckermannHF.HF_extensionality_form := by
      rfl
    rw [heq]
    exact htranslated
  have hextRen := BProv_closeN_allE_rename
    (B := Ax_s) (G := G) k extBody (fun n : Nat ↦ n)
    (fun n hn ↦ False.elim (hextSentence n hn))
    hextClosed
  have hext : BProv Ax_s G extBody := by
    simpa [rename_id] using hextRen
  have hext' : BProv Ax_s G
      (all (all
        (imp
          (all (iffForm (hfMemAt 0 2) (hfMemAt 0 1)))
          (eq (Term.var 1) (Term.var 0))))) := by
    simpa [extBody] using hext
  have hleft := BProv_allE (B := Ax_s) (G := G)
    (t := left) hext'
  have hright := BProv_allE (B := Ax_s) (G := G)
    (t := right) hleft
  have hmemLeft :
      subst (Term.upSubst (instTerm right))
          (subst (Term.upSubst (Term.upSubst (instTerm left)))
            (hfMemAt 0 2)) =
        hfMemTermAt 0 (Term.rename Nat.succ left) := by
    rw [← hfMemTermAt_var 0 2]
    change
      subst (Term.upSubst (instTerm right))
          (subst (Term.upSubst (Term.upSubst (instTerm left)))
            (hfMemTermAt 0
              (Term.rename Nat.succ (Term.var 1)))) =
        hfMemTermAt 0 (Term.rename Nat.succ left)
    rw [subst_up_hfMemTermAt_zero_rename_succ]
    rw [subst_up_hfMemTermAt_zero_rename_succ]
    have hinner :
        Term.subst (Term.upSubst (instTerm left)) (Term.var 1) =
          Term.rename Nat.succ left := by
      rfl
    rw [hinner, term_subst_instTerm_rename_succ]
  have hmemRight :
      subst (Term.upSubst (instTerm right))
          (subst (Term.upSubst (Term.upSubst (instTerm left)))
            (hfMemAt 0 1)) =
        hfMemTermAt 0 (Term.rename Nat.succ right) := by
    rw [← hfMemTermAt_var 0 1]
    change
      subst (Term.upSubst (instTerm right))
          (subst (Term.upSubst (Term.upSubst (instTerm left)))
            (hfMemTermAt 0
              (Term.rename Nat.succ (Term.var 0)))) =
        hfMemTermAt 0 (Term.rename Nat.succ right)
    rw [subst_up_hfMemTermAt_zero_rename_succ]
    rw [subst_up_hfMemTermAt_zero_rename_succ]
    simp [instTerm, Term.subst, Term.upSubst]
  change BProv Ax_s G
    (imp
      (all
        (iffForm
          (subst (Term.upSubst (instTerm right))
            (subst (Term.upSubst (Term.upSubst (instTerm left)))
              (hfMemAt 0 2)))
          (subst (Term.upSubst (instTerm right))
            (subst (Term.upSubst (Term.upSubst (instTerm left)))
              (hfMemAt 0 1)))))
      (eq
        (Term.subst (instTerm right)
          (Term.subst (Term.upSubst (instTerm left)) (Term.var 1)))
        (Term.subst (instTerm right)
          (Term.subst (Term.upSubst (instTerm left)) (Term.var 0))))) at hright
  rw [hmemLeft, hmemRight] at hright
  have hleftTerm :
      Term.subst (instTerm right)
          (Term.subst (Term.upSubst (instTerm left)) (Term.var 1)) =
        left := by
    have hinner :
        Term.subst (Term.upSubst (instTerm left)) (Term.var 1) =
          Term.rename Nat.succ left := by
      rfl
    rw [hinner, term_subst_instTerm_rename_succ]
  have hrightTerm :
      Term.subst (instTerm right)
          (Term.subst (Term.upSubst (instTerm left)) (Term.var 0)) =
        right := by
    rfl
  rw [hleftTerm, hrightTerm] at hright
  exact BProv_mp Ax_s G _ _ hright hsame

/-- The translated Ackermann-adjoin graph is functional in its output code. -/
theorem BProv_Ax_s_hfAdjoinGraphTermAt_functional
    {G : List Formula}
    {newCode₁ newCode₂ oldCode elemCode : Term}
    (hgraph₁ : BProv Ax_s G
      (hfAdjoinGraphTermAt newCode₁ oldCode elemCode))
    (hgraph₂ : BProv Ax_s G
      (hfAdjoinGraphTermAt newCode₂ oldCode elemCode)) :
    BProv Ax_s G (eq newCode₁ newCode₂) := by
  let C : List Formula := G.map (rename Nat.succ)
  let leftMem : Formula :=
    hfMemTermAt 0 (Term.rename Nat.succ newCode₁)
  let rightMem : Formula :=
    hfMemTermAt 0 (Term.rename Nat.succ newCode₂)
  let rhs : Formula :=
    or
      (hfMemTermAt 0 (Term.rename Nat.succ oldCode))
      (eq (Term.var 0) (Term.rename Nat.succ elemCode))
  have hgraph₁RenRaw := BProv_rename_of_sentences
    (B := Ax_s) Ax_s_sentences
    hgraph₁ Nat.succ
  have hgraph₁Ren : BProv Ax_s C
      (hfAdjoinGraphTermAt
        (Term.rename Nat.succ newCode₁)
        (Term.rename Nat.succ oldCode)
        (Term.rename Nat.succ elemCode)) := by
    simpa [C, rename_hfAdjoinGraphTermAt_succ] using hgraph₁RenRaw
  have hgraph₂RenRaw := BProv_rename_of_sentences
    (B := Ax_s) Ax_s_sentences
    hgraph₂ Nat.succ
  have hgraph₂Ren : BProv Ax_s C
      (hfAdjoinGraphTermAt
        (Term.rename Nat.succ newCode₂)
        (Term.rename Nat.succ oldCode)
        (Term.rename Nat.succ elemCode)) := by
    simpa [C, rename_hfAdjoinGraphTermAt_succ] using hgraph₂RenRaw
  have hpoint₁ : BProv Ax_s C (iffForm leftMem rhs) := by
    simpa [leftMem, rhs] using
      (BProv_hfAdjoinGraphTermAt_point
        (B := Ax_s) (G := C) (query := 0) hgraph₁Ren)
  have hpoint₂ : BProv Ax_s C (iffForm rightMem rhs) := by
    simpa [rightMem, rhs] using
      (BProv_hfAdjoinGraphTermAt_point
        (B := Ax_s) (G := C) (query := 0) hgraph₂Ren)
  have hforward : BProv Ax_s C (imp leftMem rightMem) := by
    let D : List Formula := leftMem :: C
    have hleft : BProv Ax_s D leftMem :=
      BProv_ass (B := Ax_s) (G := D) (by simp [D])
    have hpoint₁D := BProv_context_cons (B := Ax_s)
      (a := leftMem) hpoint₁
    have hpoint₂D := BProv_context_cons (B := Ax_s)
      (a := leftMem) hpoint₂
    have hrhs : BProv Ax_s D rhs :=
      BProv_mp Ax_s D leftMem rhs (BProv_andE1 hpoint₁D) hleft
    have hright : BProv Ax_s D rightMem :=
      BProv_mp Ax_s D rhs rightMem (BProv_andE2 hpoint₂D) hrhs
    simpa [D] using BProv_impI hright
  have hreverse : BProv Ax_s C (imp rightMem leftMem) := by
    let D : List Formula := rightMem :: C
    have hright : BProv Ax_s D rightMem :=
      BProv_ass (B := Ax_s) (G := D) (by simp [D])
    have hpoint₁D := BProv_context_cons (B := Ax_s)
      (a := rightMem) hpoint₁
    have hpoint₂D := BProv_context_cons (B := Ax_s)
      (a := rightMem) hpoint₂
    have hrhs : BProv Ax_s D rhs :=
      BProv_mp Ax_s D rightMem rhs (BProv_andE1 hpoint₂D) hright
    have hleft : BProv Ax_s D leftMem :=
      BProv_mp Ax_s D rhs leftMem (BProv_andE2 hpoint₁D) hrhs
    simpa [D] using BProv_impI hleft
  have hsame : BProv Ax_s G
      (all (iffForm leftMem rightMem)) :=
    BProv_allI_of_sentences
      (B := Ax_s) (G := G)
      Ax_s_sentences
      (BProv_iffForm_intro hforward hreverse)
  exact BProv_Ax_s_eq_of_hfSameMembersTermAt
    (by simpa [leftMem, rightMem] using hsame)

theorem subst_ordinalCodeTraceAgreementAt
    (sigma : Nat → Term)
    (sequenceCode₁ sequenceStep₁ sequenceCode₂ sequenceStep₂
      index : Term) :
    subst sigma
        (ordinalCodeTraceAgreementAt
          sequenceCode₁ sequenceStep₁ sequenceCode₂ sequenceStep₂
          index) =
      ordinalCodeTraceAgreementAt
        (Term.subst sigma sequenceCode₁)
        (Term.subst sigma sequenceStep₁)
        (Term.subst sigma sequenceCode₂)
        (Term.subst sigma sequenceStep₂)
        (Term.subst sigma index) := by
  simp [ordinalCodeTraceAgreementAt,
    subst_betaTermTermAt, subst, Term.subst, Term.upSubst,
    Term.rename, term_subst_up_up_rename_add_two]

theorem rename_ordinalCodeTraceAgreementAt
    (r : Nat → Nat)
    (sequenceCode₁ sequenceStep₁ sequenceCode₂ sequenceStep₂
      index : Term) :
    rename r
        (ordinalCodeTraceAgreementAt
          sequenceCode₁ sequenceStep₁ sequenceCode₂ sequenceStep₂
          index) =
      ordinalCodeTraceAgreementAt
        (Term.rename r sequenceCode₁)
        (Term.rename r sequenceStep₁)
        (Term.rename r sequenceCode₂)
        (Term.rename r sequenceStep₂)
        (Term.rename r index) := by
  rw [← subst_var_rename,
    subst_ordinalCodeTraceAgreementAt]
  simp only [term_subst_var_rename]

/-- The two explicit zero entries give pointwise trace agreement at zero. -/
theorem BProv_Ax_s_ordinalCodeTraceAgreementAt_zero
    {G : List Formula}
    {sequenceCode₁ sequenceStep₁ sequenceCode₂ sequenceStep₂ : Term}
    (hzero₁ : BProv Ax_s G
      (betaTermTermAt Term.zero sequenceCode₁ sequenceStep₁ Term.zero))
    (hzero₂ : BProv Ax_s G
      (betaTermTermAt Term.zero sequenceCode₂ sequenceStep₂ Term.zero)) :
    BProv Ax_s G
      (ordinalCodeTraceAgreementAt
        sequenceCode₁ sequenceStep₁ sequenceCode₂ sequenceStep₂
        Term.zero) := by
  have hcomponents : BProv Ax_s G
      (and
        (betaTermTermAt Term.zero
          sequenceCode₁ sequenceStep₁ Term.zero)
        (and
          (betaTermTermAt Term.zero
            sequenceCode₂ sequenceStep₂ Term.zero)
          (eq Term.zero Term.zero))) :=
    BProv_andI hzero₁
      (BProv_andI hzero₂
        (BProv_eqRefl (B := Ax_s) (G := G) Term.zero))
  apply BProv_exI (t := Term.zero)
  apply BProv_exI (t := Term.zero)
  simpa [ordinalCodeTraceAgreementAt,
    subst_betaTermTermAt, subst, instTerm,
    Term.subst, Term.upSubst, Term.rename,
    Term.subst_rename_succ_up,
    term_subst_instTerm_rename_succ,
    term_subst_instTerm_rename_two_succ,
    term_subst_upSubst_instTerm_rename_two_succ]
    using hcomponents

/-- Equality transport in the two input positions of an adjoin graph. -/
theorem BProv_Ax_s_hfAdjoinGraphTermAt_congr_inputs
    {G : List Formula}
    {newCode oldCode₁ oldCode₂ elemCode₁ elemCode₂ : Term}
    (hold : BProv Ax_s G (eq oldCode₁ oldCode₂))
    (helem : BProv Ax_s G (eq elemCode₁ elemCode₂))
    (hgraph : BProv Ax_s G
      (hfAdjoinGraphTermAt newCode oldCode₁ elemCode₁)) :
    BProv Ax_s G
      (hfAdjoinGraphTermAt newCode oldCode₂ elemCode₂) := by
  exact BProv_hfAdjoinGraphTermAt_congr_inputs hold helem hgraph

/-- Package two named beta values and their equality as trace agreement. -/
theorem BProv_ordinalCodeTraceAgreementAt_of_components
    {B : Formula → Prop} {G : List Formula}
    {sequenceCode₁ sequenceStep₁ sequenceCode₂ sequenceStep₂
      index value₁ value₂ : Term}
    (hvalue₁ : BProv B G
      (betaTermTermAt value₁ sequenceCode₁ sequenceStep₁ index))
    (hvalue₂ : BProv B G
      (betaTermTermAt value₂ sequenceCode₂ sequenceStep₂ index))
    (heq : BProv B G (eq value₁ value₂)) :
    BProv B G
      (ordinalCodeTraceAgreementAt
        sequenceCode₁ sequenceStep₁ sequenceCode₂ sequenceStep₂
        index) := by
  have hcomponents : BProv B G
      (and
        (betaTermTermAt value₁
          sequenceCode₁ sequenceStep₁ index)
        (and
          (betaTermTermAt value₂
            sequenceCode₂ sequenceStep₂ index)
          (eq value₁ value₂))) :=
    BProv_andI hvalue₁ (BProv_andI hvalue₂ heq)
  apply BProv_exI (t := value₁)
  apply BProv_exI (t := value₂)
  simpa [ordinalCodeTraceAgreementAt,
    subst_betaTermTermAt, subst, instTerm,
    Term.subst, Term.upSubst, Term.rename,
    Term.subst_rename_succ_up,
    term_subst_instTerm_rename_succ,
    term_subst_instTerm_rename_two_succ,
    term_subst_upSubst_instTerm_rename_two_succ]
    using hcomponents

private def ordinalCodeStepBodyTermAt
    (current next sequenceCode sequenceStep index : Term) : Formula :=
  and
    (betaTermTermAt current sequenceCode sequenceStep index)
    (and
      (betaTermTermAt next sequenceCode sequenceStep (Term.succ index))
      (hfAdjoinGraphTermAt next current current))

/-- Pointwise agreement of two ordinal-code traces is preserved by one
Ackermann-adjoin recurrence edge. -/
theorem BProv_Ax_s_ordinalCodeTraceAgreementAt_succ
    {G : List Formula}
    {sequenceCode₁ sequenceStep₁ sequenceCode₂ sequenceStep₂
      index : Term}
    (hagreement : BProv Ax_s G
      (ordinalCodeTraceAgreementAt
        sequenceCode₁ sequenceStep₁ sequenceCode₂ sequenceStep₂
        index))
    (hstep₁ : BProv Ax_s G
      (ordinalCodeStepWitnessTermAt sequenceCode₁ sequenceStep₁ index))
    (hstep₂ : BProv Ax_s G
      (ordinalCodeStepWitnessTermAt sequenceCode₂ sequenceStep₂ index)) :
    BProv Ax_s G
      (ordinalCodeTraceAgreementAt
        sequenceCode₁ sequenceStep₁ sequenceCode₂ sequenceStep₂
        (Term.succ index)) := by
  let target : Formula :=
    ordinalCodeTraceAgreementAt
      sequenceCode₁ sequenceStep₁ sequenceCode₂ sequenceStep₂
      (Term.succ index)
  let sequenceCode₁A : Term :=
    Term.rename (fun n ↦ n+2) sequenceCode₁
  let sequenceStep₁A : Term :=
    Term.rename (fun n ↦ n+2) sequenceStep₁
  let sequenceCode₂A : Term :=
    Term.rename (fun n ↦ n+2) sequenceCode₂
  let sequenceStep₂A : Term :=
    Term.rename (fun n ↦ n+2) sequenceStep₂
  let indexA : Term := Term.rename (fun n ↦ n+2) index
  let body₁ : Formula :=
    ordinalCodeStepBodyTermAt
      (Term.var 1) (Term.var 0)
      sequenceCode₁A sequenceStep₁A indexA
  let inner₁ : Formula := ex body₁
  have hstep₁Ex : BProv Ax_s G (ex (ex body₁)) := by
    simpa [ordinalCodeStepWitnessTermAt, body₁,
      sequenceCode₁A, sequenceStep₁A, indexA,
      ordinalCodeStepBodyTermAt] using hstep₁
  refine BProv_two_exE_of_sentences
    (B := Ax_s) (G := G) (body := body₁) (target := target)
    Ax_s_sentences hstep₁Ex ?_
  let A : List Formula :=
    body₁ :: (inner₁ :: G.map (rename Nat.succ)).map (rename Nat.succ)
  change BProv Ax_s A (rename Nat.succ (rename Nat.succ target))
  have hbody₁A : BProv Ax_s A body₁ :=
    BProv_ass (B := Ax_s) (G := A) (by simp [A])
  have lift2ToA : ∀ {phi : Formula}, BProv Ax_s G phi →
      BProv Ax_s A (rename Nat.succ (rename Nat.succ phi)) := by
    intro phi hphi
    simpa [A] using
      (BProv_lift_two_contexts_of_sentences
        (B := Ax_s) Ax_s_sentences
        (outer := inner₁) (inner := body₁) hphi)
  have hstep₂ARaw := lift2ToA hstep₂
  have hstep₂A : BProv Ax_s A
      (ordinalCodeStepWitnessTermAt
        sequenceCode₂A sequenceStep₂A indexA) := by
    simpa [sequenceCode₂A, sequenceStep₂A, indexA,
      rename_ordinalCodeStepWitnessTermAt,
      Term.rename_comp, Function.comp_def, Nat.add_assoc]
      using hstep₂ARaw
  have hagreementARaw := lift2ToA hagreement
  have hagreementA : BProv Ax_s A
      (ordinalCodeTraceAgreementAt
        sequenceCode₁A sequenceStep₁A
        sequenceCode₂A sequenceStep₂A indexA) := by
    simpa [sequenceCode₁A, sequenceStep₁A,
      sequenceCode₂A, sequenceStep₂A, indexA,
      rename_ordinalCodeTraceAgreementAt,
      Term.rename_comp, Function.comp_def, Nat.add_assoc]
      using hagreementARaw
  let sequenceCode₁D : Term :=
    Term.rename (fun n ↦ n+4) sequenceCode₁
  let sequenceStep₁D : Term :=
    Term.rename (fun n ↦ n+4) sequenceStep₁
  let sequenceCode₂D : Term :=
    Term.rename (fun n ↦ n+4) sequenceCode₂
  let sequenceStep₂D : Term :=
    Term.rename (fun n ↦ n+4) sequenceStep₂
  let indexD : Term := Term.rename (fun n ↦ n+4) index
  let body₂ : Formula :=
    ordinalCodeStepBodyTermAt
      (Term.var 1) (Term.var 0)
      sequenceCode₂D sequenceStep₂D indexD
  let inner₂ : Formula := ex body₂
  have hstep₂Ex : BProv Ax_s A (ex (ex body₂)) := by
    simpa [ordinalCodeStepWitnessTermAt, body₂,
      sequenceCode₂A, sequenceStep₂A, indexA,
      sequenceCode₂D, sequenceStep₂D, indexD,
      ordinalCodeStepBodyTermAt,
      Term.rename_comp, Function.comp_def, Nat.add_assoc]
      using hstep₂A
  refine BProv_two_exE_of_sentences
    (B := Ax_s) (G := A) (body := body₂)
    (target := rename Nat.succ (rename Nat.succ target))
    Ax_s_sentences hstep₂Ex ?_
  let D : List Formula :=
    body₂ :: (inner₂ :: A.map (rename Nat.succ)).map (rename Nat.succ)
  change BProv Ax_s D
    (rename Nat.succ (rename Nat.succ
      (rename Nat.succ (rename Nat.succ target))))
  have hbody₂D : BProv Ax_s D body₂ :=
    BProv_ass (B := Ax_s) (G := D) (by simp [D])
  have lift2ToD : ∀ {phi : Formula}, BProv Ax_s A phi →
      BProv Ax_s D (rename Nat.succ (rename Nat.succ phi)) := by
    intro phi hphi
    simpa [D] using
      (BProv_lift_two_contexts_of_sentences
        (B := Ax_s) Ax_s_sentences
        (outer := inner₂) (inner := body₂) hphi)
  have hcurrent₁A : BProv Ax_s A
      (betaTermTermAt (Term.var 1)
        sequenceCode₁A sequenceStep₁A indexA) := by
    simpa [body₁, ordinalCodeStepBodyTermAt] using
      BProv_andE1 hbody₁A
  have htail₁A := BProv_andE2 hbody₁A
  have hnext₁A : BProv Ax_s A
      (betaTermTermAt (Term.var 0)
        sequenceCode₁A sequenceStep₁A (Term.succ indexA)) := by
    simpa [body₁, ordinalCodeStepBodyTermAt] using
      BProv_andE1 htail₁A
  have hgraph₁A : BProv Ax_s A
      (hfAdjoinGraphTermAt (Term.var 0) (Term.var 1) (Term.var 1)) := by
    simpa [body₁, ordinalCodeStepBodyTermAt] using
      BProv_andE2 htail₁A
  have hcurrent₁DRaw := lift2ToD hcurrent₁A
  have hcurrent₁D : BProv Ax_s D
      (betaTermTermAt (Term.var 3)
        sequenceCode₁D sequenceStep₁D indexD) := by
    simpa [sequenceCode₁A, sequenceStep₁A, indexA,
      sequenceCode₁D, sequenceStep₁D, indexD,
      rename_betaTermTermAt, rename, Term.rename,
      Term.rename_comp, Function.comp_def, Nat.add_assoc]
      using hcurrent₁DRaw
  have hnext₁DRaw := lift2ToD hnext₁A
  have hnext₁D : BProv Ax_s D
      (betaTermTermAt (Term.var 2)
        sequenceCode₁D sequenceStep₁D (Term.succ indexD)) := by
    simpa [sequenceCode₁A, sequenceStep₁A, indexA,
      sequenceCode₁D, sequenceStep₁D, indexD,
      rename_betaTermTermAt, rename, Term.rename,
      Term.rename_comp, Function.comp_def, Nat.add_assoc]
      using hnext₁DRaw
  have hgraph₁DRaw := lift2ToD hgraph₁A
  have hgraph₁D : BProv Ax_s D
      (hfAdjoinGraphTermAt (Term.var 2) (Term.var 3) (Term.var 3)) := by
    simpa [rename_hfAdjoinGraphTermAt_succ,
      rename, Term.rename] using hgraph₁DRaw
  have hagreementDRaw := lift2ToD hagreementA
  have hagreementD : BProv Ax_s D
      (ordinalCodeTraceAgreementAt
        sequenceCode₁D sequenceStep₁D
        sequenceCode₂D sequenceStep₂D indexD) := by
    simpa [sequenceCode₁A, sequenceStep₁A,
      sequenceCode₂A, sequenceStep₂A, indexA,
      sequenceCode₁D, sequenceStep₁D,
      sequenceCode₂D, sequenceStep₂D, indexD,
      rename_ordinalCodeTraceAgreementAt,
      Term.rename_comp, Function.comp_def, Nat.add_assoc]
      using hagreementDRaw
  have hcurrent₂D : BProv Ax_s D
      (betaTermTermAt (Term.var 1)
        sequenceCode₂D sequenceStep₂D indexD) := by
    simpa [body₂, ordinalCodeStepBodyTermAt] using
      BProv_andE1 hbody₂D
  have htail₂D := BProv_andE2 hbody₂D
  have hnext₂D : BProv Ax_s D
      (betaTermTermAt (Term.var 0)
        sequenceCode₂D sequenceStep₂D (Term.succ indexD)) := by
    simpa [body₂, ordinalCodeStepBodyTermAt] using
      BProv_andE1 htail₂D
  have hgraph₂D : BProv Ax_s D
      (hfAdjoinGraphTermAt (Term.var 0) (Term.var 1) (Term.var 1)) := by
    simpa [body₂, ordinalCodeStepBodyTermAt] using
      BProv_andE2 htail₂D
  have hcurrentEq : BProv Ax_s D (eq (Term.var 3) (Term.var 1)) :=
    BProv_Ax_s_eq_of_ordinalCodeTraceAgreementAt
      hcurrent₁D hcurrent₂D hagreementD
  have hgraph₂D' : BProv Ax_s D
      (hfAdjoinGraphTermAt (Term.var 0) (Term.var 3) (Term.var 3)) :=
    BProv_Ax_s_hfAdjoinGraphTermAt_congr_inputs
      (BProv_eqSym hcurrentEq) (BProv_eqSym hcurrentEq) hgraph₂D
  have hnextEq : BProv Ax_s D (eq (Term.var 2) (Term.var 0)) :=
    BProv_Ax_s_hfAdjoinGraphTermAt_functional hgraph₁D hgraph₂D'
  have hresult : BProv Ax_s D
      (ordinalCodeTraceAgreementAt
        sequenceCode₁D sequenceStep₁D
        sequenceCode₂D sequenceStep₂D (Term.succ indexD)) :=
    BProv_ordinalCodeTraceAgreementAt_of_components
      hnext₁D hnext₂D hnextEq
  simpa [target,
    sequenceCode₁D, sequenceStep₁D,
    sequenceCode₂D, sequenceStep₂D, indexD,
    rename_ordinalCodeTraceAgreementAt,
    Term.rename, Term.rename_comp, Function.comp_def, Nat.add_assoc]
    using hresult

/-- Minimal recurrence-induction interface: two explicit graph bodies produce
pointwise agreement at their common raw endpoint. -/
def OrdinalCodeTraceAgreementProof : Prop :=
  ∀ {G : List Formula}
      {sequenceCode₁ sequenceStep₁ sequenceCode₂ sequenceStep₂
        raw coded₁ coded₂ : Term},
    BProv Ax_s G
      (ordinalCodeGraphBodyTermAt
        sequenceCode₁ sequenceStep₁ raw coded₁) →
    BProv Ax_s G
      (ordinalCodeGraphBodyTermAt
        sequenceCode₂ sequenceStep₂ raw coded₂) →
    BProv Ax_s G
      (ordinalCodeTraceAgreementAt
        sequenceCode₁ sequenceStep₁ sequenceCode₂ sequenceStep₂
        raw)

/-- PA proves pointwise agreement of any two ordinal-code beta traces at their
common endpoint.  The induction invariant is `n ≤ raw → agreement n`; the
successor case uses functionality of translated Ackermann adjunction. -/
theorem ordinalCodeTraceAgreementProof :
    OrdinalCodeTraceAgreementProof := by
  intro G sequenceCode₁ sequenceStep₁ sequenceCode₂ sequenceStep₂
    raw coded₁ coded₂ hbody₁ hbody₂
  have hzero₁ : BProv Ax_s G
      (betaTermTermAt Term.zero
        sequenceCode₁ sequenceStep₁ Term.zero) := by
    simpa [ordinalCodeGraphBodyTermAt] using BProv_andE1 hbody₁
  have htail₁ := BProv_andE2 hbody₁
  have hsteps₁ : BProv Ax_s G
      (ordinalCodeStepsTermAt sequenceCode₁ sequenceStep₁ raw) := by
    simpa [ordinalCodeGraphBodyTermAt] using BProv_andE2 htail₁
  have hzero₂ : BProv Ax_s G
      (betaTermTermAt Term.zero
        sequenceCode₂ sequenceStep₂ Term.zero) := by
    simpa [ordinalCodeGraphBodyTermAt] using BProv_andE1 hbody₂
  have htail₂ := BProv_andE2 hbody₂
  have hsteps₂ : BProv Ax_s G
      (ordinalCodeStepsTermAt sequenceCode₂ sequenceStep₂ raw) := by
    simpa [ordinalCodeGraphBodyTermAt] using BProv_andE2 htail₂
  let agreementZero : Formula :=
    ordinalCodeTraceAgreementAt
      sequenceCode₁ sequenceStep₁ sequenceCode₂ sequenceStep₂
      Term.zero
  have hagreementZero : BProv Ax_s G agreementZero := by
    simpa [agreementZero] using
      (BProv_Ax_s_ordinalCodeTraceAgreementAt_zero hzero₁ hzero₂)
  let phi : Formula :=
    imp
      (leTermAt (Term.var 0) (Term.rename Nat.succ raw))
      (ordinalCodeTraceAgreementAt
        (Term.rename Nat.succ sequenceCode₁)
        (Term.rename Nat.succ sequenceStep₁)
        (Term.rename Nat.succ sequenceCode₂)
        (Term.rename Nat.succ sequenceStep₂)
        (Term.var 0))
  have hzeroImp : BProv Ax_s G
      (imp (leTermAt Term.zero raw) agreementZero) := by
    let C : List Formula := leTermAt Term.zero raw :: G
    have hagreementZeroC : BProv Ax_s C agreementZero :=
      BProv_context_cons (B := Ax_s)
        (a := leTermAt Term.zero raw) hagreementZero
    simpa [C] using BProv_impI hagreementZeroC
  have hzero : BProv Ax_s G (subst substZero phi) := by
    simpa [phi, agreementZero,
      subst_ordinalCodeTraceAgreementAt,
      leTermAt, substZero, subst, instTerm,
      Term.subst, Term.upSubst, Term.rename,
      Term.subst_rename_succ_up,
      term_substZero_rename_succ]
      using hzeroImp
  let R : List Formula := G.map (rename Nat.succ)
  let S : List Formula := phi :: R
  let sequenceCode₁R : Term := Term.rename Nat.succ sequenceCode₁
  let sequenceStep₁R : Term := Term.rename Nat.succ sequenceStep₁
  let sequenceCode₂R : Term := Term.rename Nat.succ sequenceCode₂
  let sequenceStep₂R : Term := Term.rename Nat.succ sequenceStep₂
  let rawR : Term := Term.rename Nat.succ raw
  let agreementCurrent : Formula :=
    ordinalCodeTraceAgreementAt
      sequenceCode₁R sequenceStep₁R sequenceCode₂R sequenceStep₂R
      (Term.var 0)
  let agreementNext : Formula :=
    ordinalCodeTraceAgreementAt
      sequenceCode₁R sequenceStep₁R sequenceCode₂R sequenceStep₂R
      (Term.succ (Term.var 0))
  let leCurrent : Formula := leTermAt (Term.var 0) rawR
  let leNext : Formula := leTermAt (Term.succ (Term.var 0)) rawR
  have hphiS : BProv Ax_s S phi :=
    BProv_ass (B := Ax_s) (G := S) (by simp [S])
  have hih : BProv Ax_s S (imp leCurrent agreementCurrent) := by
    simpa [phi, leCurrent, agreementCurrent,
      sequenceCode₁R, sequenceStep₁R,
      sequenceCode₂R, sequenceStep₂R, rawR] using hphiS
  have hsteps₁RRaw := BProv_rename_of_sentences
    (B := Ax_s) Ax_s_sentences
    hsteps₁ Nat.succ
  have hsteps₁R : BProv Ax_s R
      (ordinalCodeStepsTermAt sequenceCode₁R sequenceStep₁R rawR) := by
    simpa [R, sequenceCode₁R, sequenceStep₁R, rawR,
      rename_ordinalCodeStepsTermAt] using hsteps₁RRaw
  have hsteps₂RRaw := BProv_rename_of_sentences
    (B := Ax_s) Ax_s_sentences
    hsteps₂ Nat.succ
  have hsteps₂R : BProv Ax_s R
      (ordinalCodeStepsTermAt sequenceCode₂R sequenceStep₂R rawR) := by
    simpa [R, sequenceCode₂R, sequenceStep₂R, rawR,
      rename_ordinalCodeStepsTermAt] using hsteps₂RRaw
  have hsuccBody : BProv Ax_s S (subst substSuccVar phi) := by
    let D : List Formula := leNext :: S
    have hleNext : BProv Ax_s D leNext :=
      BProv_ass (B := Ax_s) (G := D) (by simp [D])
    have hleCurrent : BProv Ax_s D leCurrent :=
      BProv_Ax_s_leTermAt_pred_of_succ_le hleNext
    have hihD : BProv Ax_s D (imp leCurrent agreementCurrent) :=
      BProv_context_cons (B := Ax_s) (a := leNext) hih
    have hagreementCurrent : BProv Ax_s D agreementCurrent :=
      BProv_mp Ax_s D leCurrent agreementCurrent hihD hleCurrent
    have hlt : BProv Ax_s D (ltTermAt (Term.var 0) rawR) :=
      BProv_Ax_s_ltTermAt_of_succ_leTermAt hleNext
    have hsteps₁D : BProv Ax_s D
        (ordinalCodeStepsTermAt sequenceCode₁R sequenceStep₁R rawR) :=
      BProv_context_two hsteps₁R
    have hsteps₂D : BProv Ax_s D
        (ordinalCodeStepsTermAt sequenceCode₂R sequenceStep₂R rawR) :=
      BProv_context_two hsteps₂R
    have hstep₁D : BProv Ax_s D
        (ordinalCodeStepWitnessTermAt
          sequenceCode₁R sequenceStep₁R (Term.var 0)) :=
      by
        have himpRaw := BProv_allE (B := Ax_s) (G := D)
          (t := Term.var 0) hsteps₁D
        have himp : BProv Ax_s D
            (imp
              (ltTermAt (Term.var 0) rawR)
              (ordinalCodeStepWitnessTermAt
                sequenceCode₁R sequenceStep₁R (Term.var 0))) := by
          simpa [ordinalCodeStepsTermAt,
            subst_ordinalCodeStepWitnessTermAt,
            subst_ltTermAt, subst, instTerm, Term.subst,
            Term.upSubst, Term.subst_rename_succ_up,
            term_subst_instTerm_rename_succ] using himpRaw
        exact BProv_mp Ax_s D _ _ himp hlt
    have hstep₂D : BProv Ax_s D
        (ordinalCodeStepWitnessTermAt
          sequenceCode₂R sequenceStep₂R (Term.var 0)) :=
      by
        have himpRaw := BProv_allE (B := Ax_s) (G := D)
          (t := Term.var 0) hsteps₂D
        have himp : BProv Ax_s D
            (imp
              (ltTermAt (Term.var 0) rawR)
              (ordinalCodeStepWitnessTermAt
                sequenceCode₂R sequenceStep₂R (Term.var 0))) := by
          simpa [ordinalCodeStepsTermAt,
            subst_ordinalCodeStepWitnessTermAt,
            subst_ltTermAt, subst, instTerm, Term.subst,
            Term.upSubst, Term.subst_rename_succ_up,
            term_subst_instTerm_rename_succ] using himpRaw
        exact BProv_mp Ax_s D _ _ himp hlt
    have hagreementNext : BProv Ax_s D agreementNext := by
      simpa [agreementCurrent, agreementNext] using
        (BProv_Ax_s_ordinalCodeTraceAgreementAt_succ
          hagreementCurrent hstep₁D hstep₂D)
    have hnextImp : BProv Ax_s S (imp leNext agreementNext) := by
      simpa [D] using BProv_impI hagreementNext
    simpa [phi, leNext, agreementNext,
      sequenceCode₁R, sequenceStep₁R,
      sequenceCode₂R, sequenceStep₂R, rawR,
      subst_ordinalCodeTraceAgreementAt,
      leTermAt, substSuccVar, subst, instTerm,
      Term.subst, Term.upSubst, Term.rename, SetTheory.up,
      Term.subst_rename_succ_up,
      term_substSuccVar_rename_succ]
      using hnextImp
  have hsuccImp : BProv Ax_s R
      (imp phi (subst substSuccVar phi)) := by
    simpa [S, R] using BProv_impI hsuccBody
  have hsucc : BProv Ax_s G
      (all (imp phi (subst substSuccVar phi))) :=
    BProv_allI_of_sentences
      (B := Ax_s) (G := G)
      Ax_s_sentences
      (by simpa [R] using hsuccImp)
  have hall : BProv Ax_s G (all phi) :=
    BProv_Ax_s_induction_rule hzero hsucc
  have hrawRaw := BProv_allE (B := Ax_s) (G := G) (t := raw) hall
  have hraw : BProv Ax_s G
      (imp
        (leTermAt raw raw)
        (ordinalCodeTraceAgreementAt
          sequenceCode₁ sequenceStep₁ sequenceCode₂ sequenceStep₂
          raw)) := by
    simpa [phi,
      subst_ordinalCodeTraceAgreementAt,
      leTermAt, subst, instTerm,
      Term.subst, Term.upSubst, Term.rename,
      Term.subst_rename_succ_up,
      term_subst_instTerm_rename_succ]
      using hrawRaw
  exact BProv_mp Ax_s G _ _ hraw
    (BProv_Ax_s_leTermAt_refl raw)

/-- Endpoint-agreement induction implies opened-body functionality. -/
theorem OrdinalCodeGraphBodyFunctional_of_traceAgreement
    (hagreement : OrdinalCodeTraceAgreementProof) :
    OrdinalCodeGraphBodyFunctional := by
  intro G sequenceCode₁ sequenceStep₁ sequenceCode₂ sequenceStep₂
    raw coded₁ coded₂ hbody₁ hbody₂
  have htail₁ : BProv Ax_s G
      (and
        (betaTermTermAt coded₁ sequenceCode₁ sequenceStep₁ raw)
        (ordinalCodeStepsTermAt sequenceCode₁ sequenceStep₁ raw)) := by
    simpa [ordinalCodeGraphBodyTermAt] using BProv_andE2 hbody₁
  have htail₂ : BProv Ax_s G
      (and
        (betaTermTermAt coded₂ sequenceCode₂ sequenceStep₂ raw)
        (ordinalCodeStepsTermAt sequenceCode₂ sequenceStep₂ raw)) := by
    simpa [ordinalCodeGraphBodyTermAt] using BProv_andE2 hbody₂
  exact BProv_Ax_s_eq_of_ordinalCodeTraceAgreementAt
    (BProv_andE1 htail₁) (BProv_andE1 htail₂)
    (hagreement hbody₁ hbody₂)

/-- End-to-end reduction: the sole remaining recurrence-induction theorem
immediately yields functionality of the public ordinal-code graph. -/
theorem BProv_Ax_s_ordinalCodeGraphTermAt_functional_of_traceAgreement
    (hagreement : OrdinalCodeTraceAgreementProof)
    {G : List Formula} {raw coded₁ coded₂ : Term}
    (hgraph₁ : BProv Ax_s G
      (ordinalCodeGraphTermAt raw coded₁))
    (hgraph₂ : BProv Ax_s G
      (ordinalCodeGraphTermAt raw coded₂)) :
    BProv Ax_s G (eq coded₁ coded₂) :=
  BProv_Ax_s_ordinalCodeGraphTermAt_functional_of_body
    (OrdinalCodeGraphBodyFunctional_of_traceAgreement hagreement)
    hgraph₁ hgraph₂

/-- A concrete Code witness lies in the translated coded-ordinal domain. -/
theorem BProv_Ax_s_codedOrdinalDomain_of_ordinalCodeGraph
    (P : OrdinalCodeGraphProofs)
    {G : List Formula} {raw coded : Term}
    (hgraph : BProv Ax_s G
      (ordinalCodeGraphTermAt raw coded)) :
    BProv Ax_s G
      (subst (instTerm coded) codedOrdinalDomain) := by
  have hinst : BProv Ax_s G
      (subst (instTerm raw)
        (ordinalCodeGraphTermAt
          (Term.var 0) (Term.rename Nat.succ coded))) := by
    simpa [subst_ordinalCodeGraphTermAt, instTerm, Term.subst,
      term_subst_instTerm_rename_succ] using hgraph
  have hex : BProv Ax_s G
      (ex (ordinalCodeGraphTermAt
        (Term.var 0) (Term.rename Nat.succ coded))) :=
    BProv_exI hinst
  have hrange := P.range G coded
  have hreverse : BProv Ax_s G
      (imp
        (ex (ordinalCodeGraphTermAt
          (Term.var 0) (Term.rename Nat.succ coded)))
        (subst (instTerm coded) codedOrdinalDomain)) := by
    simpa [iffForm] using BProv_andE2 hrange
  exact BProv_mp Ax_s G _ _ hreverse hex

/-- The explicit beta trace witnessing the Ackermann ordinal code of zero. -/
theorem BProv_Ax_s_ordinalCodeGraphTermAt_zero
    {G : List Formula} :
    BProv Ax_s G
      (ordinalCodeGraphTermAt Term.zero Term.zero) := by
  have hstepZero : BProv Ax_s G (eq Term.zero Term.zero) :=
    BProv_eqRefl (B := Ax_s) (G := G) Term.zero
  have hentry : BProv Ax_s G
      (betaTermTermAt Term.zero Term.zero Term.zero Term.zero) :=
    BProv_Ax_s_betaTermTermAt_zero_of_eq_step_zero hstepZero
  have hsteps : BProv Ax_s G
      (ordinalCodeStepsTermAt Term.zero Term.zero Term.zero) :=
    BProv_Ax_s_ordinalCodeStepsTermAt_zero Term.zero Term.zero
  exact BProv_ordinalCodeGraphTermAt_of_body
    (BProv_andI hentry (BProv_andI hentry hsteps))

/-- Base case in precisely the existential shape used by graph totality. -/
theorem BProv_Ax_s_ordinalCodeGraphTermAt_zero_exists
    {G : List Formula} :
    BProv Ax_s G
      (ex (ordinalCodeGraphTermAt
        (Term.rename Nat.succ Term.zero) (Term.var 0))) := by
  apply BProv_exI (t := Term.zero)
  simpa [subst_ordinalCodeGraphTermAt, instTerm, Term.subst,
    Term.rename] using
    (BProv_Ax_s_ordinalCodeGraphTermAt_zero (G := G))

theorem BProv_Ax_s_ordinalCodeStepWitnessTermAt_of_components
    {G : List Formula}
    {sequenceCode sequenceStep index current next : Term}
    (hcurrent : BProv Ax_s G
      (betaTermTermAt current sequenceCode sequenceStep index))
    (hnext : BProv Ax_s G
      (betaTermTermAt next sequenceCode sequenceStep
        (Term.succ index)))
    (hadjoin : BProv Ax_s G
      (hfAdjoinGraphTermAt next current current)) :
    BProv Ax_s G
      (ordinalCodeStepWitnessTermAt
        sequenceCode sequenceStep index) := by
  let body : Formula :=
    and
      (betaTermTermAt (Term.var 1)
        (Term.rename (fun n => n + 2) sequenceCode)
        (Term.rename (fun n => n + 2) sequenceStep)
        (Term.rename (fun n => n + 2) index))
      (and
        (betaTermTermAt (Term.var 0)
          (Term.rename (fun n => n + 2) sequenceCode)
          (Term.rename (fun n => n + 2) sequenceStep)
          (Term.succ (Term.rename (fun n => n + 2) index)))
        (hfAdjoinGraphTermAt
          (Term.var 0) (Term.var 1) (Term.var 1)))
  have hcomponents : BProv Ax_s G
      (and
        (betaTermTermAt current sequenceCode sequenceStep index)
        (and
          (betaTermTermAt next sequenceCode sequenceStep
            (Term.succ index))
          (hfAdjoinGraphTermAt next current current))) :=
    BProv_andI hcurrent (BProv_andI hnext hadjoin)
  apply BProv_exI (t := current)
  apply BProv_exI (t := next)
  simpa [ordinalCodeStepWitnessTermAt, body,
    subst_betaTermTermAt, subst_hfAdjoinGraphTermAt,
    subst, instTerm, Term.subst, Term.upSubst,
    Term.subst_rename_succ_up,
    term_subst_instTerm_rename_succ,
    term_subst_instTerm_rename_two_succ,
    term_subst_upSubst_instTerm_rename_two_succ,
    term_subst_up_up_instTerm_rename_three_succ,
    Term.rename_comp, Function.comp_def] using hcomponents

/-- Instantiate the bounded ordinal-code recurrence at an arbitrary term
known to lie below its raw bound. -/
theorem BProv_Ax_s_ordinalCodeStepsTermAt_step_of_ltTerm
    {G : List Formula}
    {sequenceCode sequenceStep raw index : Term}
    (hsteps : BProv Ax_s G
      (ordinalCodeStepsTermAt sequenceCode sequenceStep raw))
    (hlt : BProv Ax_s G (ltTermAt index raw)) :
    BProv Ax_s G
      (ordinalCodeStepWitnessTermAt
        sequenceCode sequenceStep index) := by
  have himpRaw := BProv_allE (B := Ax_s) (G := G)
    (t := index) hsteps
  have himp : BProv Ax_s G
      (imp (ltTermAt index raw)
        (ordinalCodeStepWitnessTermAt
          sequenceCode sequenceStep index)) := by
    simpa [ordinalCodeStepsTermAt,
      subst_ordinalCodeStepWitnessTermAt,
      subst_ltTermAt, subst, instTerm, Term.subst,
      Term.upSubst, Term.subst_rename_succ_up,
      term_subst_instTerm_rename_succ] using himpRaw
  exact BProv_mp Ax_s G _ _ himp hlt

/-- Prefix agreement transports an Ackermann-adjoin trace edge when both of
its adjacent indices lie below the agreement bound. -/
theorem BProv_Ax_s_ordinalCodeStepWitnessTermAt_of_prefixAgreement
    {G : List Formula}
    {oldCode newCode step bound index : Term}
    (hagreement : BProv Ax_s G
      (betaPrefixAgreementTermAt oldCode newCode step bound))
    (hltCurrent : BProv Ax_s G (ltTermAt index bound))
    (hltNext : BProv Ax_s G
      (ltTermAt (Term.succ index) bound))
    (hwitness : BProv Ax_s G
      (ordinalCodeStepWitnessTermAt oldCode step index)) :
    BProv Ax_s G
      (ordinalCodeStepWitnessTermAt newCode step index) := by
  let target : Formula :=
    ordinalCodeStepWitnessTermAt newCode step index
  let body : Formula :=
    and
      (betaTermTermAt (Term.var 1)
        (Term.rename (fun n => n + 2) oldCode)
        (Term.rename (fun n => n + 2) step)
        (Term.rename (fun n => n + 2) index))
      (and
        (betaTermTermAt (Term.var 0)
          (Term.rename (fun n => n + 2) oldCode)
          (Term.rename (fun n => n + 2) step)
          (Term.succ (Term.rename (fun n => n + 2) index)))
        (hfAdjoinGraphTermAt
          (Term.var 0) (Term.var 1) (Term.var 1)))
  have hwit : BProv Ax_s G (ex (ex body)) := by
    simpa [ordinalCodeStepWitnessTermAt, body] using hwitness
  refine BProv_two_exE_of_sentences
    (B := Ax_s) Ax_s_sentences hwit ?_
  let C : List Formula :=
    body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)
  let oldCode2 : Term := Term.rename (fun n => n + 2) oldCode
  let newCode2 : Term := Term.rename (fun n => n + 2) newCode
  let step2 : Term := Term.rename (fun n => n + 2) step
  let bound2 : Term := Term.rename (fun n => n + 2) bound
  let index2 : Term := Term.rename (fun n => n + 2) index
  have hbody : BProv Ax_s C body :=
    BProv_ass (B := Ax_s) (G := C) (by simp [C])
  have hcurrent : BProv Ax_s C
      (betaTermTermAt (Term.var 1) oldCode2 step2 index2) := by
    simpa [body, oldCode2, step2, index2] using BProv_andE1 hbody
  have htail : BProv Ax_s C
      (and
        (betaTermTermAt (Term.var 0) oldCode2 step2
          (Term.succ index2))
        (hfAdjoinGraphTermAt
          (Term.var 0) (Term.var 1) (Term.var 1))) := by
    simpa [body, oldCode2, step2, index2] using BProv_andE2 hbody
  have hnext : BProv Ax_s C
      (betaTermTermAt (Term.var 0) oldCode2 step2
        (Term.succ index2)) := BProv_andE1 htail
  have hadjoin : BProv Ax_s C
      (hfAdjoinGraphTermAt
        (Term.var 0) (Term.var 1) (Term.var 1)) := BProv_andE2 htail
  have hagreementC0 := BProv_lift_two_contexts_of_sentences
    (B := Ax_s) Ax_s_sentences
    (outer := ex body) (inner := body) hagreement
  have hagreementC : BProv Ax_s C
      (betaPrefixAgreementTermAt
        oldCode2 newCode2 step2 bound2) := by
    simpa [C, oldCode2, newCode2, step2, bound2,
      betaPrefixAgreementTermAt, betaTermTermAt,
      remTermTermAt, ltTermAt, betaModTermTerm,
      rename, Term.rename, SetTheory.up, Term.rename_comp,
      Function.comp_def, Nat.add_assoc] using hagreementC0
  have hltCurrentC0 := BProv_lift_two_contexts_of_sentences
    (B := Ax_s) Ax_s_sentences
    (outer := ex body) (inner := body) hltCurrent
  have hltCurrentC : BProv Ax_s C (ltTermAt index2 bound2) := by
    simpa [C, index2, bound2, ltTermAt,
      rename, Term.rename, SetTheory.up, Term.rename_comp,
      Function.comp_def, Nat.add_assoc] using hltCurrentC0
  have hltNextC0 := BProv_lift_two_contexts_of_sentences
    (B := Ax_s) Ax_s_sentences
    (outer := ex body) (inner := body) hltNext
  have hltNextC : BProv Ax_s C
      (ltTermAt (Term.succ index2) bound2) := by
    simpa [C, index2, bound2, ltTermAt,
      rename, Term.rename, SetTheory.up, Term.rename_comp,
      Function.comp_def, Nat.add_assoc] using hltNextC0
  have hcurrentNew : BProv Ax_s C
      (betaTermTermAt (Term.var 1) newCode2 step2 index2) :=
    BProv_Ax_s_betaPrefixAgreementTermAt_entry_of_ltTerm
      hagreementC hltCurrentC hcurrent
  have hnextNew : BProv Ax_s C
      (betaTermTermAt (Term.var 0) newCode2 step2
        (Term.succ index2)) :=
    BProv_Ax_s_betaPrefixAgreementTermAt_entry_of_ltTerm
      hagreementC hltNextC hnext
  have hnew : BProv Ax_s C
      (ordinalCodeStepWitnessTermAt newCode2 step2 index2) :=
    BProv_Ax_s_ordinalCodeStepWitnessTermAt_of_components
      hcurrentNew hnextNew hadjoin
  simpa [target, C, body, newCode2, step2, index2,
    rename_ordinalCodeStepWitnessTermAt,
    rename, Term.rename, SetTheory.up, Term.rename_comp,
    Function.comp_def, Nat.add_assoc] using hnew

theorem subst_betaPrefixAgreementTermAt
    (sigma : Nat → Term) (oldCode newCode step bound : Term) :
    subst sigma
        (betaPrefixAgreementTermAt oldCode newCode step bound) =
      betaPrefixAgreementTermAt
        (Term.subst sigma oldCode) (Term.subst sigma newCode)
        (Term.subst sigma step) (Term.subst sigma bound) := by
  simp [betaPrefixAgreementTermAt, subst_betaTermTermAt,
    subst_ltTermAt, subst, Term.subst, Term.upSubst,
    Term.subst_rename_succ_up, term_subst_up_up_rename_add_two,
    Term.rename]

theorem rename_betaPrefixAgreementTermAt
    (r : Nat → Nat) (oldCode newCode step bound : Term) :
    rename r
        (betaPrefixAgreementTermAt oldCode newCode step bound) =
      betaPrefixAgreementTermAt
        (Term.rename r oldCode) (Term.rename r newCode)
        (Term.rename r step) (Term.rename r bound) := by
  rw [← subst_var_rename,
    subst_betaPrefixAgreementTermAt]
  simp only [term_subst_var_rename]

theorem subst_betaCodeExtensionTermAt
    (sigma : Nat → Term) (oldCode step target newOut newCode : Term) :
    subst sigma
        (betaCodeExtensionTermAt oldCode step target newOut newCode) =
      betaCodeExtensionTermAt
        (Term.subst sigma oldCode) (Term.subst sigma step)
        (Term.subst sigma target) (Term.subst sigma newOut)
        (Term.subst sigma newCode) := by
  simp [betaCodeExtensionTermAt,
    subst_betaPrefixAgreementTermAt,
    subst_betaTermTermAt, subst]

theorem rename_betaCodeExtensionTermAt
    (r : Nat → Nat) (oldCode step target newOut newCode : Term) :
    rename r
        (betaCodeExtensionTermAt oldCode step target newOut newCode) =
      betaCodeExtensionTermAt
        (Term.rename r oldCode) (Term.rename r step)
        (Term.rename r target) (Term.rename r newOut)
        (Term.rename r newCode) := by
  rw [← subst_var_rename,
    subst_betaCodeExtensionTermAt]
  simp only [term_subst_var_rename]

/-- A one-entry beta-code extension transports the old recurrence and adds
the new final Ackermann-adjoin edge.  This is the local successor invariant
used by the strengthened PA induction. -/
theorem BProv_Ax_s_ordinalCodeStepsTermAt_succ_of_extension
    {G : List Formula}
    {oldSequenceCode newSequenceCode sequenceStep raw oldCoded newCoded : Term}
    (hsteps : BProv Ax_s G
      (ordinalCodeStepsTermAt oldSequenceCode sequenceStep raw))
    (hendpoint : BProv Ax_s G
      (betaTermTermAt oldCoded oldSequenceCode sequenceStep raw))
    (hextension : BProv Ax_s G
      (betaCodeExtensionTermAt oldSequenceCode sequenceStep
        (Term.succ raw) newCoded newSequenceCode))
    (hadjoin : BProv Ax_s G
      (hfAdjoinGraphTermAt newCoded oldCoded oldCoded)) :
    BProv Ax_s G
      (ordinalCodeStepsTermAt
        newSequenceCode sequenceStep (Term.succ raw)) := by
  let antecedent : Formula :=
    ltTermAt (Term.var 0)
      (Term.succ (Term.rename Nat.succ raw))
  let consequent : Formula :=
    ordinalCodeStepWitnessTermAt
      (Term.rename Nat.succ newSequenceCode)
      (Term.rename Nat.succ sequenceStep)
      (Term.var 0)
  let body : Formula := imp antecedent consequent
  have hbody : BProv Ax_s
      (antecedent :: G.map (rename Nat.succ)) consequent := by
    let C : List Formula := antecedent :: G.map (rename Nat.succ)
    let oldSequenceCode1 : Term := Term.rename Nat.succ oldSequenceCode
    let newSequenceCode1 : Term := Term.rename Nat.succ newSequenceCode
    let sequenceStep1 : Term := Term.rename Nat.succ sequenceStep
    let raw1 : Term := Term.rename Nat.succ raw
    let oldCoded1 : Term := Term.rename Nat.succ oldCoded
    let newCoded1 : Term := Term.rename Nat.succ newCoded
    have hltSucc : BProv Ax_s C
        (ltTermAt (Term.var 0) (Term.succ raw1)) := by
      simpa [C, antecedent, raw1] using
        (BProv_ass (B := Ax_s) (G := C) (by simp [C, antecedent]))
    have hcases : BProv Ax_s C
        (or (ltTermAt (Term.var 0) raw1)
          (eq (Term.var 0) raw1)) :=
      BProv_Ax_s_ltTermAt_succ_right_cases hltSucc
    have hstepsRen : BProv Ax_s (G.map (rename Nat.succ))
        (rename Nat.succ
          (ordinalCodeStepsTermAt oldSequenceCode sequenceStep raw)) :=
      BProv_rename_of_sentences
        (B := Ax_s) Ax_s_sentences
        hsteps Nat.succ
    have hstepsC : BProv Ax_s C
        (ordinalCodeStepsTermAt
          oldSequenceCode1 sequenceStep1 raw1) := by
      have hraw := BProv_context_cons (B := Ax_s)
        (a := antecedent) hstepsRen
      simpa [C, oldSequenceCode1, sequenceStep1, raw1,
        rename_ordinalCodeStepsTermAt] using hraw
    have hendpointRen : BProv Ax_s (G.map (rename Nat.succ))
        (rename Nat.succ
          (betaTermTermAt oldCoded oldSequenceCode sequenceStep raw)) :=
      BProv_rename_of_sentences
        (B := Ax_s) Ax_s_sentences
        hendpoint Nat.succ
    have hendpointC : BProv Ax_s C
        (betaTermTermAt oldCoded1 oldSequenceCode1 sequenceStep1 raw1) := by
      have hraw := BProv_context_cons (B := Ax_s)
        (a := antecedent) hendpointRen
      simpa [C, oldCoded1, oldSequenceCode1, sequenceStep1, raw1,
        rename_betaTermTermAt] using hraw
    have hextensionRen : BProv Ax_s (G.map (rename Nat.succ))
        (rename Nat.succ
          (betaCodeExtensionTermAt oldSequenceCode sequenceStep
            (Term.succ raw) newCoded newSequenceCode)) :=
      BProv_rename_of_sentences
        (B := Ax_s) Ax_s_sentences
        hextension Nat.succ
    have hextensionC : BProv Ax_s C
        (betaCodeExtensionTermAt oldSequenceCode1 sequenceStep1
          (Term.succ raw1) newCoded1 newSequenceCode1) := by
      have hraw := BProv_context_cons (B := Ax_s)
        (a := antecedent) hextensionRen
      simpa [C, oldSequenceCode1, sequenceStep1, raw1,
        newCoded1, newSequenceCode1,
        rename_betaCodeExtensionTermAt,
        Term.rename] using hraw
    have hagreementC : BProv Ax_s C
        (betaPrefixAgreementTermAt oldSequenceCode1 newSequenceCode1
          sequenceStep1 (Term.succ raw1)) :=
      BProv_Ax_s_betaPrefixAgreementTermAt_of_betaCodeExtensionTermAt
        hextensionC
    have hadjoinRen : BProv Ax_s (G.map (rename Nat.succ))
        (rename Nat.succ
          (hfAdjoinGraphTermAt newCoded oldCoded oldCoded)) :=
      BProv_rename_of_sentences
        (B := Ax_s) Ax_s_sentences
        hadjoin Nat.succ
    have hadjoinC : BProv Ax_s C
        (hfAdjoinGraphTermAt newCoded1 oldCoded1 oldCoded1) := by
      have hraw := BProv_context_cons (B := Ax_s)
        (a := antecedent) hadjoinRen
      simpa [C, newCoded1, oldCoded1,
        rename_hfAdjoinGraphTermAt_succ] using hraw
    have hbelow : BProv Ax_s
        (ltTermAt (Term.var 0) raw1 :: C) consequent := by
      let D : List Formula := ltTermAt (Term.var 0) raw1 :: C
      have hlt : BProv Ax_s D (ltTermAt (Term.var 0) raw1) :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D])
      have holdWitness : BProv Ax_s D
          (ordinalCodeStepWitnessTermAt
            oldSequenceCode1 sequenceStep1 (Term.var 0)) :=
        BProv_Ax_s_ordinalCodeStepsTermAt_step_of_ltTerm
          (BProv_context_cons (B := Ax_s) hstepsC) hlt
      have hagreementD := BProv_context_cons (B := Ax_s)
        (a := ltTermAt (Term.var 0) raw1) hagreementC
      have hltCurrent : BProv Ax_s D
          (ltTermAt (Term.var 0) (Term.succ raw1)) :=
        BProv_context_cons (B := Ax_s)
          (a := ltTermAt (Term.var 0) raw1) hltSucc
      have hltNext : BProv Ax_s D
          (ltTermAt (Term.succ (Term.var 0)) (Term.succ raw1)) :=
        BProv_Ax_s_ltTermAt_succ_succ hlt
      have hnewWitness : BProv Ax_s D
          (ordinalCodeStepWitnessTermAt
            newSequenceCode1 sequenceStep1 (Term.var 0)) :=
        BProv_Ax_s_ordinalCodeStepWitnessTermAt_of_prefixAgreement
          hagreementD hltCurrent hltNext holdWitness
      simpa [D, C, consequent, newSequenceCode1, sequenceStep1] using
        hnewWitness
    have hequal : BProv Ax_s
        (eq (Term.var 0) raw1 :: C) consequent := by
      let D : List Formula := eq (Term.var 0) raw1 :: C
      have heq : BProv Ax_s D (eq (Term.var 0) raw1) :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D])
      have hagreementD := BProv_context_cons (B := Ax_s)
        (a := eq (Term.var 0) raw1) hagreementC
      have hendpointD := BProv_context_cons (B := Ax_s)
        (a := eq (Term.var 0) raw1) hendpointC
      have holdAtRaw : BProv Ax_s D
          (betaTermTermAt oldCoded1 newSequenceCode1 sequenceStep1 raw1) :=
        BProv_Ax_s_betaPrefixAgreementTermAt_entry_of_ltTerm
          hagreementD (BProv_Ax_s_ltTermAt_self_succ raw1) hendpointD
      have holdAtIndex : BProv Ax_s D
          (betaTermTermAt oldCoded1 newSequenceCode1 sequenceStep1
            (Term.var 0)) :=
        BProv_Ax_s_betaTermTermAt_of_eq_index
          (BProv_eqSym heq) holdAtRaw
      have hnewAtSuccRaw : BProv Ax_s D
          (betaTermTermAt newCoded1 newSequenceCode1 sequenceStep1
            (Term.succ raw1)) :=
        BProv_Ax_s_betaTermTermAt_of_betaCodeExtensionTermAt
          (BProv_context_cons (B := Ax_s)
            (a := eq (Term.var 0) raw1) hextensionC)
      have hnewAtSuccIndex : BProv Ax_s D
          (betaTermTermAt newCoded1 newSequenceCode1 sequenceStep1
            (Term.succ (Term.var 0))) :=
        BProv_Ax_s_betaTermTermAt_of_eq_index
          (BProv_eq_congr_succ (BProv_eqSym heq)) hnewAtSuccRaw
      have hnewWitness : BProv Ax_s D
          (ordinalCodeStepWitnessTermAt
            newSequenceCode1 sequenceStep1 (Term.var 0)) :=
        BProv_Ax_s_ordinalCodeStepWitnessTermAt_of_components
          holdAtIndex hnewAtSuccIndex
          (BProv_context_cons (B := Ax_s)
            (a := eq (Term.var 0) raw1) hadjoinC)
      simpa [D, C, consequent, newSequenceCode1, sequenceStep1] using
        hnewWitness
    exact BProv_orE hcases hbelow hequal
  have himp : BProv Ax_s (G.map (rename Nat.succ)) body := by
    simpa [body] using BProv_impI hbody
  have hall : BProv Ax_s G (all body) :=
    BProv_allI_of_sentences (B := Ax_s)
      Ax_s_sentences himp
  simpa [ordinalCodeStepsTermAt, body, antecedent, consequent,
    Term.rename] using hall

/-- Complete local successor transformer for an explicit ordinal-code trace.
The step is intentionally unchanged; the strengthened induction chooses it
large enough before invoking this theorem. -/
theorem BProv_Ax_s_ordinalCodeGraphBodyTermAt_succ_of_extension
    {G : List Formula}
    {oldSequenceCode newSequenceCode sequenceStep raw oldCoded newCoded : Term}
    (hbody : BProv Ax_s G
      (ordinalCodeGraphBodyTermAt
        oldSequenceCode sequenceStep raw oldCoded))
    (hextension : BProv Ax_s G
      (betaCodeExtensionTermAt oldSequenceCode sequenceStep
        (Term.succ raw) newCoded newSequenceCode))
    (hadjoin : BProv Ax_s G
      (hfAdjoinGraphTermAt newCoded oldCoded oldCoded)) :
    BProv Ax_s G
      (ordinalCodeGraphBodyTermAt
        newSequenceCode sequenceStep (Term.succ raw) newCoded) := by
  have hhead : BProv Ax_s G
      (betaTermTermAt Term.zero oldSequenceCode sequenceStep Term.zero) := by
    simpa [ordinalCodeGraphBodyTermAt] using BProv_andE1 hbody
  have htail : BProv Ax_s G
      (and
        (betaTermTermAt oldCoded oldSequenceCode sequenceStep raw)
        (ordinalCodeStepsTermAt oldSequenceCode sequenceStep raw)) := by
    simpa [ordinalCodeGraphBodyTermAt] using BProv_andE2 hbody
  have hendpoint : BProv Ax_s G
      (betaTermTermAt oldCoded oldSequenceCode sequenceStep raw) :=
    BProv_andE1 htail
  have hsteps : BProv Ax_s G
      (ordinalCodeStepsTermAt oldSequenceCode sequenceStep raw) :=
    BProv_andE2 htail
  have hheadNew : BProv Ax_s G
      (betaTermTermAt Term.zero newSequenceCode sequenceStep Term.zero) :=
    BProv_Ax_s_betaTermTermAt_zero_of_succ_extension
      hhead hextension
  have hendpointNew : BProv Ax_s G
      (betaTermTermAt newCoded newSequenceCode sequenceStep
        (Term.succ raw)) :=
    BProv_Ax_s_betaTermTermAt_of_betaCodeExtensionTermAt hextension
  have hstepsNew : BProv Ax_s G
      (ordinalCodeStepsTermAt
        newSequenceCode sequenceStep (Term.succ raw)) :=
    BProv_Ax_s_ordinalCodeStepsTermAt_succ_of_extension
      hsteps hendpoint hextension hadjoin
  simpa [ordinalCodeGraphBodyTermAt] using
    BProv_andI hheadNew (BProv_andI hendpointNew hstepsNew)

/-- A successor-stage capacity `oldCapacity + newCoded` is sufficient to
re-use the induction hypothesis at the predecessor bound. -/
theorem BProv_Ax_s_betaCodingStepTermAt_old_of_sum_capacity
    {G : List Formula} {raw oldCapacity newCoded step : Term}
    (hcoding : BProv Ax_s G
      (betaCodingStepTermAt (Term.succ raw)
        (Term.add oldCapacity newCoded) step)) :
    BProv Ax_s G
      (betaCodingStepTermAt raw oldCapacity step) := by
  have hcommonSucc : BProv Ax_s G
      (commonMultipleThroughTermAt (Term.succ raw) step) := by
    simpa [betaCodingStepTermAt] using BProv_andE1 hcoding
  have hcommon : BProv Ax_s G
      (commonMultipleThroughTermAt raw step) :=
    BProv_Ax_s_commonMultipleThroughTermAt_of_le hcommonSucc
      (BProv_Ax_s_leTermAt_self_succ raw)
  have hlargeSum : BProv Ax_s G
      (leTermAt (Term.succ (Term.add oldCapacity newCoded)) step) := by
    simpa [betaCodingStepTermAt] using BProv_andE2 hcoding
  have holdLeSum : BProv Ax_s G
      (leTermAt oldCapacity (Term.add oldCapacity newCoded)) :=
    BProv_Ax_s_leTermAt_of_eq_add_right_terms
      (BProv_eqRefl (B := Ax_s) (G := G)
        (Term.add oldCapacity newCoded))
  have hsuccOldLeSum : BProv Ax_s G
      (leTermAt (Term.succ oldCapacity)
        (Term.succ (Term.add oldCapacity newCoded))) :=
    BProv_Ax_s_leTermAt_succ_succ holdLeSum
  have hlargeOld : BProv Ax_s G
      (leTermAt (Term.succ oldCapacity) step) :=
    BProv_Ax_s_leTermAt_trans hsuccOldLeSum hlargeSum
  simpa [betaCodingStepTermAt] using BProv_andI hcommon hlargeOld

/-- The same summed capacity supplies the strict modulus bound needed to
append `newCoded` at index `S raw`. -/
theorem BProv_Ax_s_betaCodeExtensionExistsTermAt_of_sum_capacity
    {G : List Formula}
    {oldSequenceCode raw oldCapacity newCoded step : Term}
    (hcoding : BProv Ax_s G
      (betaCodingStepTermAt (Term.succ raw)
        (Term.add oldCapacity newCoded) step)) :
    BProv Ax_s G
      (betaCodeExtensionExistsTermAt oldSequenceCode step
        (Term.succ raw) newCoded) := by
  have hcommon : BProv Ax_s G
      (commonMultipleThroughTermAt (Term.succ raw) step) := by
    simpa [betaCodingStepTermAt] using BProv_andE1 hcoding
  have hlargeSum : BProv Ax_s G
      (leTermAt (Term.succ (Term.add oldCapacity newCoded)) step) := by
    simpa [betaCodingStepTermAt] using BProv_andE2 hcoding
  have hcomm : BProv Ax_s G
      (eq (Term.add oldCapacity newCoded)
        (Term.add newCoded oldCapacity)) :=
    BProv_Ax_s_add_comm_terms oldCapacity newCoded
  have hnewLeSum : BProv Ax_s G
      (leTermAt newCoded (Term.add oldCapacity newCoded)) :=
    BProv_Ax_s_leTermAt_of_eq_add_right_terms hcomm
  have hsuccNewLeSum : BProv Ax_s G
      (leTermAt (Term.succ newCoded)
        (Term.succ (Term.add oldCapacity newCoded))) :=
    BProv_Ax_s_leTermAt_succ_succ hnewLeSum
  have hlargeNew : BProv Ax_s G
      (leTermAt (Term.succ newCoded) step) :=
    BProv_Ax_s_leTermAt_trans hsuccNewLeSum hlargeSum
  have hstepMod : BProv Ax_s G
      (leTermAt step
        (betaModTermTerm step (Term.succ raw))) :=
    BProv_Ax_s_leTermAt_step_betaModTermTerm step (Term.succ raw)
  have hnewLtMod : BProv Ax_s G
      (ltTermAt newCoded
        (betaModTermTerm step (Term.succ raw))) :=
    BProv_Ax_s_ltTermAt_of_succ_leTermAt
      (BProv_Ax_s_leTermAt_trans hlargeNew hstepMod)
  exact BProv_Ax_s_betaCodeExtensionExistsTermAt_of_common
    hcommon hnewLtMod

/-- Existence of a sequence-code witness for a fixed step and endpoint. -/
def ordinalCodeGraphBodyExistsTermAt
    (step raw coded : Term) : Formula :=
  ex (ordinalCodeGraphBodyTermAt
    (Term.var 0)
    (Term.rename Nat.succ step)
    (Term.rename Nat.succ raw)
    (Term.rename Nat.succ coded))

theorem subst_ordinalCodeGraphBodyExistsTermAt
    (sigma : Nat → Term) (step raw coded : Term) :
    subst sigma
        (ordinalCodeGraphBodyExistsTermAt step raw coded) =
      ordinalCodeGraphBodyExistsTermAt
        (Term.subst sigma step)
        (Term.subst sigma raw)
        (Term.subst sigma coded) := by
  simp [ordinalCodeGraphBodyExistsTermAt,
    subst_ordinalCodeGraphBodyTermAt,
    subst, Term.subst, Term.upSubst,
    Term.subst_rename_succ_up]

theorem rename_ordinalCodeGraphBodyExistsTermAt
    (r : Nat → Nat) (step raw coded : Term) :
    rename r
        (ordinalCodeGraphBodyExistsTermAt step raw coded) =
      ordinalCodeGraphBodyExistsTermAt
        (Term.rename r step)
        (Term.rename r raw)
        (Term.rename r coded) := by
  rw [← subst_var_rename,
    subst_ordinalCodeGraphBodyExistsTermAt]
  simp only [term_subst_var_rename]

theorem BProv_ordinalCodeGraphBodyExistsTermAt_of_term
    {B : Formula → Prop} {G : List Formula}
    {sequenceCode step raw coded : Term}
    (hbody : BProv B G
      (ordinalCodeGraphBodyTermAt sequenceCode step raw coded)) :
    BProv B G
      (ordinalCodeGraphBodyExistsTermAt step raw coded) := by
  apply BProv_exI (t := sequenceCode)
  simpa [ordinalCodeGraphBodyExistsTermAt,
    subst_ordinalCodeGraphBodyTermAt,
    instTerm, Term.subst,
    term_subst_instTerm_rename_succ] using hbody

theorem BProv_Ax_s_ordinalCodeGraphBodyExistsTermAt_elim_opened
    {G : List Formula} {step raw coded : Term} {target : Formula}
    (hopened : BProv Ax_s
      (ordinalCodeGraphBodyTermAt
          (Term.var 0)
          (Term.rename Nat.succ step)
          (Term.rename Nat.succ raw)
          (Term.rename Nat.succ coded) ::
        G.map (rename Nat.succ))
      (rename Nat.succ target))
    (hex : BProv Ax_s G
      (ordinalCodeGraphBodyExistsTermAt step raw coded)) :
    BProv Ax_s G target :=
  BProv_exE_of_sentences
    (B := Ax_s) Ax_s_sentences
    hex (by simpa [ordinalCodeGraphBodyExistsTermAt] using hopened)

/-- For a chosen PA coding step, existence of a sequence code realizing the
ordinal graph body.  The separate `capacity` parameter is a deliberately
arithmetic majorant; it avoids requiring an internal proof that Ackermann
adjunction is monotone in its old code. -/
def ordinalCodeTraceCapacityTermAt
    (raw coded capacity : Term) : Formula :=
  all (imp
    (betaCodingStepTermAt
      (Term.rename Nat.succ raw)
      (Term.rename Nat.succ capacity)
      (Term.var 0))
    (ordinalCodeGraphBodyExistsTermAt
      (Term.var 0)
      (Term.rename Nat.succ raw)
      (Term.rename Nat.succ coded)))

/-- Zero has the explicit sequence code zero at every sufficiently large
chosen step, not merely at the special step zero. -/
theorem BProv_Ax_s_ordinalCodeGraphBodyTermAt_zero_at_step
    {G : List Formula} {step : Term}
    (hlarge : BProv Ax_s G
      (leTermAt (Term.succ Term.zero) step)) :
    BProv Ax_s G
      (ordinalCodeGraphBodyTermAt
        Term.zero step Term.zero Term.zero) := by
  have hentry : BProv Ax_s G
      (betaTermTermAt Term.zero Term.zero step Term.zero) :=
    BProv_Ax_s_betaTermTermAt_self_zero_of_succ_le_step hlarge
  have hsteps : BProv Ax_s G
      (ordinalCodeStepsTermAt Term.zero step Term.zero) :=
    BProv_Ax_s_ordinalCodeStepsTermAt_zero Term.zero step
  simpa [ordinalCodeGraphBodyTermAt] using
    BProv_andI hentry (BProv_andI hentry hsteps)

/-- Base case of the majorant-parametric induction invariant. -/
theorem BProv_Ax_s_ordinalCodeTraceCapacityTermAt_zero
    {G : List Formula} :
    BProv Ax_s G
      (ordinalCodeTraceCapacityTermAt
        Term.zero Term.zero Term.zero) := by
  let antecedent : Formula :=
    betaCodingStepTermAt Term.zero Term.zero (Term.var 0)
  let consequent : Formula :=
    ordinalCodeGraphBodyExistsTermAt
      (Term.var 0) Term.zero Term.zero
  let body : Formula := imp antecedent consequent
  have hbody : BProv Ax_s
      (antecedent :: G.map (rename Nat.succ)) consequent := by
    let C : List Formula := antecedent :: G.map (rename Nat.succ)
    have hcoding : BProv Ax_s C
        (betaCodingStepTermAt Term.zero Term.zero (Term.var 0)) :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C, antecedent])
    have hlarge : BProv Ax_s C
        (leTermAt (Term.succ Term.zero) (Term.var 0)) := by
      simpa [betaCodingStepTermAt] using BProv_andE2 hcoding
    have hzero : BProv Ax_s C
        (ordinalCodeGraphBodyTermAt
          Term.zero (Term.var 0) Term.zero Term.zero) :=
      BProv_Ax_s_ordinalCodeGraphBodyTermAt_zero_at_step hlarge
    apply BProv_exI (t := Term.zero)
    simpa [ordinalCodeGraphBodyExistsTermAt,
      subst_ordinalCodeGraphBodyTermAt,
      instTerm, Term.subst,
      term_subst_instTerm_rename_succ] using hzero
  have himp : BProv Ax_s (G.map (rename Nat.succ)) body := by
    simpa [body] using BProv_impI hbody
  have hall : BProv Ax_s G (all body) :=
    BProv_allI_of_sentences (B := Ax_s)
      Ax_s_sentences himp
  simpa [ordinalCodeTraceCapacityTermAt,
    body, antecedent, consequent, Term.rename] using hall

theorem BProv_Ax_s_ordinalCodeGraphBodyExistsTermAt_succ_of_sum_capacity
    {G : List Formula}
    {step raw oldCoded newCoded oldCapacity : Term}
    (holdTrace : BProv Ax_s G
      (ordinalCodeGraphBodyExistsTermAt
        step raw oldCoded))
    (hcoding : BProv Ax_s G
      (betaCodingStepTermAt (Term.succ raw)
        (Term.add oldCapacity newCoded) step))
    (hadjoin : BProv Ax_s G
      (hfAdjoinGraphTermAt newCoded oldCoded oldCoded)) :
    BProv Ax_s G
      (ordinalCodeGraphBodyExistsTermAt
        step (Term.succ raw) newCoded) := by
  let goal : Formula :=
    ordinalCodeGraphBodyExistsTermAt
      step (Term.succ raw) newCoded
  refine BProv_Ax_s_ordinalCodeGraphBodyExistsTermAt_elim_opened
    (G := G) (step := step) (raw := raw) (coded := oldCoded)
    (target := goal) ?_ holdTrace
  let oldBody : Formula :=
    ordinalCodeGraphBodyTermAt
      (Term.var 0)
      (Term.rename Nat.succ step)
      (Term.rename Nat.succ raw)
      (Term.rename Nat.succ oldCoded)
  let D : List Formula := oldBody :: G.map (rename Nat.succ)
  let step1 : Term := Term.rename Nat.succ step
  let raw1 : Term := Term.rename Nat.succ raw
  let oldCoded1 : Term := Term.rename Nat.succ oldCoded
  let newCoded1 : Term := Term.rename Nat.succ newCoded
  let oldCapacity1 : Term := Term.rename Nat.succ oldCapacity
  have holdBody : BProv Ax_s D
      (ordinalCodeGraphBodyTermAt
        (Term.var 0) step1 raw1 oldCoded1) := by
    simpa [D, oldBody, step1, raw1, oldCoded1] using
      (BProv_ass (B := Ax_s) (G := D) (by simp [D, oldBody]))
  have hcodingRen : BProv Ax_s (G.map (rename Nat.succ))
      (rename Nat.succ
        (betaCodingStepTermAt (Term.succ raw)
          (Term.add oldCapacity newCoded) step)) :=
    BProv_rename_of_sentences
      (B := Ax_s) Ax_s_sentences
      hcoding Nat.succ
  have hcodingD : BProv Ax_s D
      (betaCodingStepTermAt (Term.succ raw1)
        (Term.add oldCapacity1 newCoded1) step1) := by
    have hraw := BProv_context_cons (B := Ax_s)
      (a := oldBody) hcodingRen
    simpa [D, step1, raw1, oldCapacity1, newCoded1,
      rename_betaCodingStepTermAt, Term.rename] using hraw
  have hadjoinRen : BProv Ax_s (G.map (rename Nat.succ))
      (rename Nat.succ
        (hfAdjoinGraphTermAt newCoded oldCoded oldCoded)) :=
    BProv_rename_of_sentences
      (B := Ax_s) Ax_s_sentences
      hadjoin Nat.succ
  have hadjoinD : BProv Ax_s D
      (hfAdjoinGraphTermAt newCoded1 oldCoded1 oldCoded1) := by
    have hraw := BProv_context_cons (B := Ax_s)
      (a := oldBody) hadjoinRen
    simpa [D, newCoded1, oldCoded1,
      rename_hfAdjoinGraphTermAt_succ] using hraw
  have hextExists : BProv Ax_s D
      (betaCodeExtensionExistsTermAt
        (Term.var 0) step1 (Term.succ raw1) newCoded1) :=
    BProv_Ax_s_betaCodeExtensionExistsTermAt_of_sum_capacity
      hcodingD
  refine BProv_Ax_s_betaCodeExtensionExistsTermAt_elim_opened
    (G := D) (oldCode := Term.var 0) (step := step1)
    (target := Term.succ raw1) (newOut := newCoded1)
    (goal := rename Nat.succ goal) ?_ hextExists
  let extensionBody : Formula :=
    betaCodeExtensionExistsTermAtBody
      (Term.var 0) step1 (Term.succ raw1) newCoded1
  let E : List Formula := extensionBody :: D.map (rename Nat.succ)
  let step2 : Term := Term.rename (fun n => n + 2) step
  let raw2 : Term := Term.rename (fun n => n + 2) raw
  let oldCoded2 : Term := Term.rename (fun n => n + 2) oldCoded
  let newCoded2 : Term := Term.rename (fun n => n + 2) newCoded
  have hextension : BProv Ax_s E
      (betaCodeExtensionTermAt
        (Term.var 1) step2 (Term.succ raw2) newCoded2
        (Term.var 0)) := by
    have hraw : BProv Ax_s E extensionBody :=
      BProv_ass (B := Ax_s) (G := E) (by simp [E])
    simpa [extensionBody, betaCodeExtensionExistsTermAtBody,
      step1, raw1, newCoded1, step2, raw2, newCoded2,
      Term.rename, Term.rename_comp, Function.comp_def,
      Nat.add_assoc] using hraw
  have holdBodyE : BProv Ax_s E
      (ordinalCodeGraphBodyTermAt
        (Term.var 1) step2 raw2 oldCoded2) := by
    have hraw : BProv Ax_s E (rename Nat.succ oldBody) :=
      BProv_ass (B := Ax_s) (G := E) (by simp [E, D])
    simpa [oldBody, step1, raw1, oldCoded1,
      step2, raw2, oldCoded2,
      rename_ordinalCodeGraphBodyTermAt,
      Term.rename, Term.rename_comp, Function.comp_def,
      Nat.add_assoc] using hraw
  have hadjoinDRen : BProv Ax_s (D.map (rename Nat.succ))
      (rename Nat.succ
        (hfAdjoinGraphTermAt newCoded1 oldCoded1 oldCoded1)) :=
    BProv_rename_of_sentences
      (B := Ax_s) Ax_s_sentences
      hadjoinD Nat.succ
  have hadjoinE : BProv Ax_s E
      (hfAdjoinGraphTermAt newCoded2 oldCoded2 oldCoded2) := by
    have hraw := BProv_context_cons (B := Ax_s)
      (a := extensionBody) hadjoinDRen
    simpa [E, newCoded1, oldCoded1, newCoded2, oldCoded2,
      rename_hfAdjoinGraphTermAt_succ,
      Term.rename, Term.rename_comp, Function.comp_def,
      Nat.add_assoc] using hraw
  have hnewBody : BProv Ax_s E
      (ordinalCodeGraphBodyTermAt
        (Term.var 0) step2 (Term.succ raw2) newCoded2) :=
    BProv_Ax_s_ordinalCodeGraphBodyTermAt_succ_of_extension
      holdBodyE hextension hadjoinE
  have hnewExists : BProv Ax_s E
      (ordinalCodeGraphBodyExistsTermAt
        step2 (Term.succ raw2) newCoded2) :=
    BProv_ordinalCodeGraphBodyExistsTermAt_of_term hnewBody
  simpa [goal, E, D, extensionBody,
    betaCodeExtensionExistsTermAtBody,
    rename_ordinalCodeGraphBodyExistsTermAt,
    Term.rename, Term.rename_comp, Function.comp_def,
    Nat.add_assoc] using hnewExists

theorem rename_ordinalCodeTraceCapacityTermAt
    (r : Nat → Nat) (raw coded capacity : Term) :
    rename r
        (ordinalCodeTraceCapacityTermAt raw coded capacity) =
      ordinalCodeTraceCapacityTermAt
        (Term.rename r raw) (Term.rename r coded)
        (Term.rename r capacity) := by
  simp [ordinalCodeTraceCapacityTermAt,
    rename_betaCodingStepTermAt,
    rename_ordinalCodeGraphBodyExistsTermAt,
    rename, Term.rename, SetTheory.up, Term.rename_comp]

/-- Instantiate the capacity-parametric trace invariant at one certified
coding step. -/
theorem BProv_Ax_s_ordinalCodeTraceCapacityTermAt_trace_of_coding
    {G : List Formula} {raw coded capacity step : Term}
    (hcapacity : BProv Ax_s G
      (ordinalCodeTraceCapacityTermAt raw coded capacity))
    (hcoding : BProv Ax_s G
      (betaCodingStepTermAt raw capacity step)) :
    BProv Ax_s G
      (ordinalCodeGraphBodyExistsTermAt step raw coded) := by
  have himpRaw := BProv_allE (B := Ax_s) (G := G)
    (t := step) hcapacity
  have himp : BProv Ax_s G
      (imp
        (betaCodingStepTermAt raw capacity step)
        (ordinalCodeGraphBodyExistsTermAt step raw coded)) := by
    simpa [ordinalCodeTraceCapacityTermAt,
      subst_ordinalCodeGraphBodyExistsTermAt,
      betaCodingStepTermAt, commonMultipleThroughTermAt,
      dvdTermTermAt, ltTermAt, leTermAt,
      subst, instTerm, Term.subst, Term.upSubst,
      Term.subst_rename_succ_up,
      term_subst_instTerm_rename_succ,
      term_subst_instTerm_rename_two_succ,
      term_subst_upSubst_instTerm_rename_two_succ,
      term_subst_up_up_instTerm_rename_three_succ,
      Term.rename_comp, Function.comp_def,
      term_subst_up_up_rename_add_two] using himpRaw
  exact BProv_mp Ax_s G _ _ himp hcoding

/-- The capacity-parametric trace invariant advances across one explicit
Ackermann-adjoin edge.  The successor capacity is the arithmetic sum of the
old majorant and the new endpoint. -/
theorem BProv_Ax_s_ordinalCodeTraceCapacityTermAt_succ
    {G : List Formula}
    {raw oldCoded newCoded oldCapacity : Term}
    (holdCapacity : BProv Ax_s G
      (ordinalCodeTraceCapacityTermAt
        raw oldCoded oldCapacity))
    (hadjoin : BProv Ax_s G
      (hfAdjoinGraphTermAt newCoded oldCoded oldCoded)) :
    BProv Ax_s G
      (ordinalCodeTraceCapacityTermAt
        (Term.succ raw) newCoded
        (Term.add oldCapacity newCoded)) := by
  let antecedent : Formula :=
    betaCodingStepTermAt
      (Term.succ (Term.rename Nat.succ raw))
      (Term.add
        (Term.rename Nat.succ oldCapacity)
        (Term.rename Nat.succ newCoded))
      (Term.var 0)
  let consequent : Formula :=
    ordinalCodeGraphBodyExistsTermAt
      (Term.var 0)
      (Term.succ (Term.rename Nat.succ raw))
      (Term.rename Nat.succ newCoded)
  let body : Formula := imp antecedent consequent
  have hbody : BProv Ax_s
      (antecedent :: G.map (rename Nat.succ)) consequent := by
    let C : List Formula := antecedent :: G.map (rename Nat.succ)
    let raw1 : Term := Term.rename Nat.succ raw
    let oldCoded1 : Term := Term.rename Nat.succ oldCoded
    let newCoded1 : Term := Term.rename Nat.succ newCoded
    let oldCapacity1 : Term := Term.rename Nat.succ oldCapacity
    have hcoding : BProv Ax_s C
        (betaCodingStepTermAt
          (Term.succ raw1)
          (Term.add oldCapacity1 newCoded1)
          (Term.var 0)) := by
      simpa [C, antecedent, raw1, oldCapacity1, newCoded1] using
        (BProv_ass (B := Ax_s) (G := C) (by simp [C, antecedent]))
    have holdCapacityRen : BProv Ax_s (G.map (rename Nat.succ))
        (rename Nat.succ
          (ordinalCodeTraceCapacityTermAt
            raw oldCoded oldCapacity)) :=
      BProv_rename_of_sentences
        (B := Ax_s) Ax_s_sentences
        holdCapacity Nat.succ
    have holdCapacityC : BProv Ax_s C
        (ordinalCodeTraceCapacityTermAt
          raw1 oldCoded1 oldCapacity1) := by
      have hraw := BProv_context_cons (B := Ax_s)
        (a := antecedent) holdCapacityRen
      simpa [C, raw1, oldCoded1, oldCapacity1,
        rename_ordinalCodeTraceCapacityTermAt] using hraw
    have hadjoinRen : BProv Ax_s (G.map (rename Nat.succ))
        (rename Nat.succ
          (hfAdjoinGraphTermAt newCoded oldCoded oldCoded)) :=
      BProv_rename_of_sentences
        (B := Ax_s) Ax_s_sentences
        hadjoin Nat.succ
    have hadjoinC : BProv Ax_s C
        (hfAdjoinGraphTermAt newCoded1 oldCoded1 oldCoded1) := by
      have hraw := BProv_context_cons (B := Ax_s)
        (a := antecedent) hadjoinRen
      simpa [C, newCoded1, oldCoded1,
        rename_hfAdjoinGraphTermAt_succ] using hraw
    have holdCoding : BProv Ax_s C
        (betaCodingStepTermAt raw1 oldCapacity1 (Term.var 0)) :=
      BProv_Ax_s_betaCodingStepTermAt_old_of_sum_capacity
        hcoding
    have holdTrace : BProv Ax_s C
        (ordinalCodeGraphBodyExistsTermAt
          (Term.var 0) raw1 oldCoded1) :=
      BProv_Ax_s_ordinalCodeTraceCapacityTermAt_trace_of_coding
        holdCapacityC holdCoding
    have hnewTrace : BProv Ax_s C
        (ordinalCodeGraphBodyExistsTermAt
          (Term.var 0) (Term.succ raw1) newCoded1) :=
      BProv_Ax_s_ordinalCodeGraphBodyExistsTermAt_succ_of_sum_capacity
        holdTrace hcoding hadjoinC
    simpa [C, consequent, raw1, newCoded1] using hnewTrace
  have himp : BProv Ax_s (G.map (rename Nat.succ)) body := by
    simpa [body] using BProv_impI hbody
  have hall : BProv Ax_s G (all body) :=
    BProv_allI_of_sentences (B := Ax_s)
      Ax_s_sentences himp
  simpa [ordinalCodeTraceCapacityTermAt,
    body, antecedent, consequent, Term.rename] using hall

theorem subst_ordinalCodeTraceCapacityTermAt
    (sigma : Nat → Term) (raw coded capacity : Term) :
    subst sigma
        (ordinalCodeTraceCapacityTermAt raw coded capacity) =
      ordinalCodeTraceCapacityTermAt
        (Term.subst sigma raw) (Term.subst sigma coded)
        (Term.subst sigma capacity) := by
  simp [ordinalCodeTraceCapacityTermAt,
    subst_betaCodingStepTermAt,
    subst_ordinalCodeGraphBodyExistsTermAt,
    subst, Term.subst, Term.upSubst,
    Term.subst_rename_succ_up]

/-- Existential PA-induction invariant: a raw number has an ordinal code and
an arithmetic capacity supporting traces at every certified coding step. -/
def ordinalCodeTotalCapacityTermAt (raw : Term) : Formula :=
  ex (ex
    (ordinalCodeTraceCapacityTermAt
      (Term.rename (fun n => n + 2) raw)
      (Term.var 1) (Term.var 0)))

theorem subst_ordinalCodeTotalCapacityTermAt
    (sigma : Nat → Term) (raw : Term) :
    subst sigma (ordinalCodeTotalCapacityTermAt raw) =
      ordinalCodeTotalCapacityTermAt
        (Term.subst sigma raw) := by
  simp [ordinalCodeTotalCapacityTermAt,
    subst_ordinalCodeTraceCapacityTermAt,
    subst, Term.subst, Term.upSubst, Term.rename,
    term_subst_up_up_rename_add_two]

theorem rename_ordinalCodeTotalCapacityTermAt
    (r : Nat → Nat) (raw : Term) :
    rename r (ordinalCodeTotalCapacityTermAt raw) =
      ordinalCodeTotalCapacityTermAt (Term.rename r raw) := by
  rw [← subst_var_rename,
    subst_ordinalCodeTotalCapacityTermAt]
  simp only [term_subst_var_rename]

theorem BProv_ordinalCodeTotalCapacityTermAt_of_terms
    {B : Formula → Prop} {G : List Formula}
    {raw coded capacity : Term}
    (hcapacity : BProv B G
      (ordinalCodeTraceCapacityTermAt raw coded capacity)) :
    BProv B G (ordinalCodeTotalCapacityTermAt raw) := by
  apply BProv_exI (t := coded)
  apply BProv_exI (t := capacity)
  simpa [ordinalCodeTotalCapacityTermAt,
    subst_ordinalCodeTraceCapacityTermAt,
    instTerm, Term.subst, Term.upSubst,
    term_subst_instTerm_rename_succ,
    term_subst_instTerm_rename_two_succ,
    term_subst_upSubst_instTerm_rename_two_succ] using hcapacity

theorem BProv_Ax_s_ordinalCodeTotalCapacityTermAt_zero
    {G : List Formula} :
    BProv Ax_s G
      (ordinalCodeTotalCapacityTermAt Term.zero) :=
  BProv_ordinalCodeTotalCapacityTermAt_of_terms
    BProv_Ax_s_ordinalCodeTraceCapacityTermAt_zero

/-- Unconditional term-parametric Ackermann adjunction, extracted from the
already closed PA proof of translated HF adjunction totality. -/
theorem BProv_Ax_s_hfAdjoinExistsTermAt
    {G : List Formula} (oldCode elemCode : Term) :
    BProv Ax_s G (hfAdjoinExistsTermAt oldCode elemCode) := by
  have hallEmpty : BProv Ax_s [] (all (hfAdjoinTotalAt 0)) :=
    BProv_Ax_s_all_hfAdjoinTotalAt_of_zero_succ
      BProv_Ax_s_hfAdjoinTotalTermAt_zero
      BProv_Ax_s_hfAdjoinTotalTermAt_succ
  have hall : BProv Ax_s G (all (hfAdjoinTotalAt 0)) :=
    BProv_mono Ax_s [] G _ (fun x hx => by cases hx) hallEmpty
  have hallTerm : BProv Ax_s G
      (all (hfAdjoinTotalTermAt (Term.var 0))) := by
    simpa [hfAdjoinTotalTermAt_var] using hall
  have htotal : BProv Ax_s G
      (hfAdjoinTotalTermAt elemCode) :=
    BProv_hfAdjoinTotalTermAt_of_all
      (elemCode := elemCode) hallTerm
  exact BProv_hfAdjoinExistsTermAt_of_total
    (oldCode := oldCode) htotal

/-- Advance the existential totality invariant from explicit predecessor
code/capacity witnesses, opening only the fresh adjunction result. -/
theorem BProv_Ax_s_ordinalCodeTotalCapacityTermAt_succ_of_terms
    {G : List Formula} {raw oldCoded oldCapacity : Term}
    (holdCapacity : BProv Ax_s G
      (ordinalCodeTraceCapacityTermAt
        raw oldCoded oldCapacity)) :
    BProv Ax_s G
      (ordinalCodeTotalCapacityTermAt (Term.succ raw)) := by
  let goal : Formula :=
    ordinalCodeTotalCapacityTermAt (Term.succ raw)
  have hex : BProv Ax_s G
      (hfAdjoinExistsTermAt oldCoded oldCoded) :=
    BProv_Ax_s_hfAdjoinExistsTermAt oldCoded oldCoded
  let graphBody : Formula :=
    hfAdjoinGraphTermAt
      (Term.var 0)
      (Term.rename Nat.succ oldCoded)
      (Term.rename Nat.succ oldCoded)
  have hopened : BProv Ax_s
      (graphBody :: G.map (rename Nat.succ))
      (rename Nat.succ goal) := by
    let D : List Formula := graphBody :: G.map (rename Nat.succ)
    let raw1 : Term := Term.rename Nat.succ raw
    let oldCoded1 : Term := Term.rename Nat.succ oldCoded
    let oldCapacity1 : Term := Term.rename Nat.succ oldCapacity
    have hgraph : BProv Ax_s D
        (hfAdjoinGraphTermAt (Term.var 0) oldCoded1 oldCoded1) := by
      simpa [D, graphBody, oldCoded1] using
        (BProv_ass (B := Ax_s) (G := D) (by simp [D, graphBody]))
    have holdCapacityRen : BProv Ax_s (G.map (rename Nat.succ))
        (rename Nat.succ
          (ordinalCodeTraceCapacityTermAt
            raw oldCoded oldCapacity)) :=
      BProv_rename_of_sentences
        (B := Ax_s) Ax_s_sentences
        holdCapacity Nat.succ
    have holdCapacityD : BProv Ax_s D
        (ordinalCodeTraceCapacityTermAt
          raw1 oldCoded1 oldCapacity1) := by
      have hraw := BProv_context_cons (B := Ax_s)
        (a := graphBody) holdCapacityRen
      simpa [D, raw1, oldCoded1, oldCapacity1,
        rename_ordinalCodeTraceCapacityTermAt] using hraw
    have hnewCapacity : BProv Ax_s D
        (ordinalCodeTraceCapacityTermAt
          (Term.succ raw1) (Term.var 0)
          (Term.add oldCapacity1 (Term.var 0))) :=
      BProv_Ax_s_ordinalCodeTraceCapacityTermAt_succ
        holdCapacityD hgraph
    have hnewTotal : BProv Ax_s D
        (ordinalCodeTotalCapacityTermAt (Term.succ raw1)) :=
      BProv_ordinalCodeTotalCapacityTermAt_of_terms hnewCapacity
    simpa [goal, D, raw1,
      rename_ordinalCodeTotalCapacityTermAt,
      Term.rename] using hnewTotal
  exact BProv_exE_of_sentences
    (B := Ax_s) Ax_s_sentences
    hex (by simpa [hfAdjoinExistsTermAt, graphBody] using hopened)

/-- Successor rule for the existential `(coded, capacity)` induction
invariant. -/
theorem BProv_Ax_s_ordinalCodeTotalCapacityTermAt_succ
    {G : List Formula} {raw : Term}
    (holdTotal : BProv Ax_s G
      (ordinalCodeTotalCapacityTermAt raw)) :
    BProv Ax_s G
      (ordinalCodeTotalCapacityTermAt (Term.succ raw)) := by
  let goal : Formula :=
    ordinalCodeTotalCapacityTermAt (Term.succ raw)
  let pairBody : Formula :=
    ordinalCodeTraceCapacityTermAt
      (Term.rename (fun n => n + 2) raw)
      (Term.var 1) (Term.var 0)
  have holdEx : BProv Ax_s G (ex (ex pairBody)) := by
    simpa [ordinalCodeTotalCapacityTermAt, pairBody] using holdTotal
  refine BProv_two_exE_of_sentences
    (B := Ax_s) Ax_s_sentences holdEx ?_
  let C : List Formula :=
    pairBody :: (ex pairBody :: G.map (rename Nat.succ)).map
      (rename Nat.succ)
  let raw2 : Term := Term.rename (fun n => n + 2) raw
  have hcapacity : BProv Ax_s C
      (ordinalCodeTraceCapacityTermAt
        raw2 (Term.var 1) (Term.var 0)) := by
    simpa [C, pairBody, raw2] using
      (BProv_ass (B := Ax_s) (G := C) (by simp [C, pairBody]))
  have hsucc : BProv Ax_s C
      (ordinalCodeTotalCapacityTermAt (Term.succ raw2)) :=
    BProv_Ax_s_ordinalCodeTotalCapacityTermAt_succ_of_terms hcapacity
  simpa [goal, C, raw2,
    rename_ordinalCodeTotalCapacityTermAt,
    Term.rename, Term.rename_comp, Function.comp_def,
    Nat.add_assoc] using hsucc

/-- PA induction closes the existential code/capacity invariant for every raw
number. -/
theorem BProv_Ax_s_all_ordinalCodeTotalCapacityTermAt
    {G : List Formula} :
    BProv Ax_s G
      (all (ordinalCodeTotalCapacityTermAt (Term.var 0))) := by
  let phi : Formula :=
    ordinalCodeTotalCapacityTermAt (Term.var 0)
  have hzeroRaw : BProv Ax_s G
      (ordinalCodeTotalCapacityTermAt Term.zero) :=
    BProv_Ax_s_ordinalCodeTotalCapacityTermAt_zero
  have hzero : BProv Ax_s G (subst substZero phi) := by
    rw [subst_ordinalCodeTotalCapacityTermAt]
    simpa [phi, substZero, Term.subst] using hzeroRaw
  have hsuccBody : BProv Ax_s
      (phi :: G.map (rename Nat.succ))
      (subst substSuccVar phi) := by
    let C : List Formula := phi :: G.map (rename Nat.succ)
    have hcurrent : BProv Ax_s C
        (ordinalCodeTotalCapacityTermAt (Term.var 0)) := by
      simpa [C, phi] using
        (BProv_ass (B := Ax_s) (G := C) (by simp [C, phi]))
    have hnext : BProv Ax_s C
        (ordinalCodeTotalCapacityTermAt
          (Term.succ (Term.var 0))) :=
      BProv_Ax_s_ordinalCodeTotalCapacityTermAt_succ hcurrent
    rw [subst_ordinalCodeTotalCapacityTermAt]
    simpa [C, phi, substSuccVar, Term.subst] using hnext
  have hsuccImp : BProv Ax_s (G.map (rename Nat.succ))
      (imp phi (subst substSuccVar phi)) :=
    BProv_impI hsuccBody
  have hsuccAll : BProv Ax_s G
      (all (imp phi (subst substSuccVar phi))) :=
    BProv_allI_of_sentences (B := Ax_s)
      Ax_s_sentences hsuccImp
  exact BProv_Ax_s_induction_rule
    (G := G) (phi := phi) hzero hsuccAll

/-- Forget the chosen beta step and sequence-code witness, retaining the
ordinary ordinal-code graph. -/
theorem BProv_Ax_s_ordinalCodeGraphTermAt_of_bodyExists
    {G : List Formula} {step raw coded : Term}
    (htrace : BProv Ax_s G
      (ordinalCodeGraphBodyExistsTermAt step raw coded)) :
    BProv Ax_s G (ordinalCodeGraphTermAt raw coded) := by
  let target : Formula := ordinalCodeGraphTermAt raw coded
  refine BProv_Ax_s_ordinalCodeGraphBodyExistsTermAt_elim_opened
    (G := G) (step := step) (raw := raw) (coded := coded)
    (target := target) ?_ htrace
  let body : Formula :=
    ordinalCodeGraphBodyTermAt
      (Term.var 0)
      (Term.rename Nat.succ step)
      (Term.rename Nat.succ raw)
      (Term.rename Nat.succ coded)
  let D : List Formula := body :: G.map (rename Nat.succ)
  have hbody : BProv Ax_s D body :=
    BProv_ass (B := Ax_s) (G := D) (by simp [D])
  have hgraph : BProv Ax_s D
      (ordinalCodeGraphTermAt
        (Term.rename Nat.succ raw)
        (Term.rename Nat.succ coded)) :=
    BProv_ordinalCodeGraphTermAt_of_body hbody
  simpa [target, D, body,
    rename_ordinalCodeGraphTermAt] using hgraph

/-- Every capacity-parametric code yields the ordinary graph after choosing a
certified beta coding step. -/
theorem BProv_Ax_s_ordinalCodeGraphTermAt_of_capacity
    {G : List Formula} {raw coded capacity : Term}
    (hcapacity : BProv Ax_s G
      (ordinalCodeTraceCapacityTermAt raw coded capacity)) :
    BProv Ax_s G (ordinalCodeGraphTermAt raw coded) := by
  let target : Formula := ordinalCodeGraphTermAt raw coded
  have hstepExists : BProv Ax_s G
      (betaCodingStepExistsTermAt raw capacity) :=
    BProv_Ax_s_betaCodingStepExistsTermAt raw capacity
  refine BProv_Ax_s_betaCodingStepExistsTermAt_elim_opened
    (G := G) (bound := raw) (sourceCode := capacity)
    (target := target) ?_ hstepExists
  let codingBody : Formula :=
    betaCodingStepExistsTermAtBody raw capacity
  let D : List Formula := codingBody :: G.map (rename Nat.succ)
  let raw1 : Term := Term.rename Nat.succ raw
  let coded1 : Term := Term.rename Nat.succ coded
  let capacity1 : Term := Term.rename Nat.succ capacity
  have hcoding : BProv Ax_s D
      (betaCodingStepTermAt raw1 capacity1 (Term.var 0)) := by
    have hraw : BProv Ax_s D codingBody :=
      BProv_ass (B := Ax_s) (G := D) (by simp [D])
    simpa [codingBody, betaCodingStepExistsTermAtBody,
      raw1, capacity1] using hraw
  have hcapacityRen : BProv Ax_s (G.map (rename Nat.succ))
      (rename Nat.succ
        (ordinalCodeTraceCapacityTermAt raw coded capacity)) :=
    BProv_rename_of_sentences
      (B := Ax_s) Ax_s_sentences
      hcapacity Nat.succ
  have hcapacityD : BProv Ax_s D
      (ordinalCodeTraceCapacityTermAt
        raw1 coded1 capacity1) := by
    have hraw := BProv_context_cons (B := Ax_s)
      (a := codingBody) hcapacityRen
    simpa [D, raw1, coded1, capacity1,
      rename_ordinalCodeTraceCapacityTermAt] using hraw
  have htrace : BProv Ax_s D
      (ordinalCodeGraphBodyExistsTermAt
        (Term.var 0) raw1 coded1) :=
    BProv_Ax_s_ordinalCodeTraceCapacityTermAt_trace_of_coding
      hcapacityD hcoding
  have hgraph : BProv Ax_s D
      (ordinalCodeGraphTermAt raw1 coded1) :=
    BProv_Ax_s_ordinalCodeGraphTermAt_of_bodyExists htrace
  simpa [target, D, raw1, coded1,
    rename_ordinalCodeGraphTermAt] using hgraph

def ordinalCodeGraphExistsTermAt (raw : Term) : Formula :=
  ex (ordinalCodeGraphTermAt
    (Term.rename Nat.succ raw) (Term.var 0))

theorem subst_ordinalCodeGraphExistsTermAt
    (sigma : Nat → Term) (raw : Term) :
    subst sigma (ordinalCodeGraphExistsTermAt raw) =
      ordinalCodeGraphExistsTermAt (Term.subst sigma raw) := by
  simp [ordinalCodeGraphExistsTermAt,
    subst_ordinalCodeGraphTermAt,
    subst, Term.subst, Term.upSubst,
    Term.subst_rename_succ_up]

theorem rename_ordinalCodeGraphExistsTermAt
    (r : Nat → Nat) (raw : Term) :
    rename r (ordinalCodeGraphExistsTermAt raw) =
      ordinalCodeGraphExistsTermAt (Term.rename r raw) := by
  rw [← subst_var_rename,
    subst_ordinalCodeGraphExistsTermAt]
  simp only [term_subst_var_rename]

theorem BProv_ordinalCodeGraphExistsTermAt_of_term
    {B : Formula → Prop} {G : List Formula} {raw coded : Term}
    (hgraph : BProv B G (ordinalCodeGraphTermAt raw coded)) :
    BProv B G (ordinalCodeGraphExistsTermAt raw) := by
  apply BProv_exI (t := coded)
  simpa [ordinalCodeGraphExistsTermAt,
    subst_ordinalCodeGraphTermAt,
    instTerm, Term.subst,
    term_subst_instTerm_rename_succ] using hgraph

/-- Project a plain graph witness from the existential code/capacity
invariant. -/
theorem BProv_Ax_s_ordinalCodeGraphExistsTermAt_of_totalCapacity
    {G : List Formula} {raw : Term}
    (htotal : BProv Ax_s G
      (ordinalCodeTotalCapacityTermAt raw)) :
    BProv Ax_s G (ordinalCodeGraphExistsTermAt raw) := by
  let target : Formula := ordinalCodeGraphExistsTermAt raw
  let pairBody : Formula :=
    ordinalCodeTraceCapacityTermAt
      (Term.rename (fun n => n + 2) raw)
      (Term.var 1) (Term.var 0)
  have holdEx : BProv Ax_s G (ex (ex pairBody)) := by
    simpa [ordinalCodeTotalCapacityTermAt, pairBody] using htotal
  refine BProv_two_exE_of_sentences
    (B := Ax_s) Ax_s_sentences holdEx ?_
  let C : List Formula :=
    pairBody :: (ex pairBody :: G.map (rename Nat.succ)).map
      (rename Nat.succ)
  let raw2 : Term := Term.rename (fun n => n + 2) raw
  have hcapacity : BProv Ax_s C
      (ordinalCodeTraceCapacityTermAt
        raw2 (Term.var 1) (Term.var 0)) := by
    simpa [C, pairBody, raw2] using
      (BProv_ass (B := Ax_s) (G := C) (by simp [C, pairBody]))
  have hgraph : BProv Ax_s C
      (ordinalCodeGraphTermAt raw2 (Term.var 1)) :=
    BProv_Ax_s_ordinalCodeGraphTermAt_of_capacity hcapacity
  have hex : BProv Ax_s C
      (ordinalCodeGraphExistsTermAt raw2) :=
    BProv_ordinalCodeGraphExistsTermAt_of_term hgraph
  simpa [target, C, raw2,
    rename_ordinalCodeGraphExistsTermAt,
    Term.rename, Term.rename_comp, Function.comp_def,
    Nat.add_assoc] using hex

/-- Exact proof term for the `OrdinalCodeGraphProofs.total` field. -/
theorem OrdinalCodeGraphProofs_total :
    ∀ (G : List Formula) (raw : Term),
      BProv Ax_s G
        (ex (ordinalCodeGraphTermAt
          (Term.rename Nat.succ raw) (Term.var 0))) := by
  intro G raw
  have hall : BProv Ax_s G
      (all (ordinalCodeTotalCapacityTermAt (Term.var 0))) :=
    BProv_Ax_s_all_ordinalCodeTotalCapacityTermAt
  have hrawRaw := BProv_allE (B := Ax_s) (G := G)
    (t := raw) hall
  have hraw : BProv Ax_s G
      (ordinalCodeTotalCapacityTermAt raw) := by
    rw [subst_ordinalCodeTotalCapacityTermAt] at hrawRaw
    simpa [instTerm, Term.subst] using hrawRaw
  have hex : BProv Ax_s G
      (ordinalCodeGraphExistsTermAt raw) :=
    BProv_Ax_s_ordinalCodeGraphExistsTermAt_of_totalCapacity hraw
  simpa [ordinalCodeGraphExistsTermAt] using hex

/-! ### Ordinal-code graph range reduction -/

/-- Pure PA strong induction for an arbitrary formula whose current value is
stored in slot zero. -/
theorem BProv_Ax_s_all_of_strongStep
    (psi : Formula)
    (hcurrent :
      ∀ {G : List Formula},
        BProv Ax_s G (hfStrongBelowAt psi) →
        BProv Ax_s G psi) :
    BProv Ax_s [] (all psi) := by
  apply BProv_Ax_s_all_of_strongStep_under [] psi
  intro G _ hbelow
  exact hcurrent hbelow

/-- Pointwise range characterization at the current coded value in slot zero. -/
def ordinalCodeGraphRangePoint : Formula :=
  iffForm codedOrdinalDomain
    (ex (ordinalCodeGraphAt 0 1))

/-- Term-parametric existential range predicate. -/
def ordinalCodeGraphRangeExistsTermAt (coded : Term) : Formula :=
  ex (ordinalCodeGraphTermAt
    (Term.var 0) (Term.rename Nat.succ coded))

/-- Instantiating the pointwise range formula at a coded term gives the
term-parametric range predicate. -/
theorem subst_instTerm_ordinalCodeGraphRangePoint
    (coded : Term) :
    subst (instTerm coded) ordinalCodeGraphRangePoint =
      iffForm
        (subst (instTerm coded) codedOrdinalDomain)
        (ordinalCodeGraphRangeExistsTermAt coded) := by
  simp [ordinalCodeGraphRangePoint,
    ordinalCodeGraphRangeExistsTermAt,
    iffForm, ordinalCodeGraphAt,
    subst_ordinalCodeGraphTermAt,
    subst, instTerm, Term.subst, Term.upSubst]

/-- The range point is unchanged by the skip-parameter renaming used in the
strong-induction body. -/
theorem rename_rSkipParam_ordinalCodeGraphRangePoint :
    rename AckermannHF.rSkipParam ordinalCodeGraphRangePoint =
      ordinalCodeGraphRangePoint := by
  have hdomain :
      rename AckermannHF.rSkipParam codedOrdinalDomain =
        codedOrdinalDomain := by
    calc
      rename AckermannHF.rSkipParam codedOrdinalDomain =
          rename (fun n : Nat ↦ n) codedOrdinalDomain := by
        apply rename_ext_free
        intro n hn
        have hn0 := codedOrdinalDomain_free hn
        subst n
        rfl
      _ = codedOrdinalDomain := rename_id codedOrdinalDomain
  simp [ordinalCodeGraphRangePoint, iffForm,
    rename, hdomain, ordinalCodeGraphAt,
    rename_ordinalCodeGraphTermAt,
    SetTheory.up, AckermannHF.rSkipParam, Term.rename]

/-- Binder body saying that the fresh predecessor in slot zero is an
ordinal-like strict predecessor of `current`, and that `current` is its HF
successor. -/
def ordinalCodeDomainSuccBodyTermAt (current : Term) : Formula :=
  and codedOrdinalDomain
    (and
      (ltTermAt (Term.var 0) (Term.rename Nat.succ current))
      (hfAdjoinGraphTermAt
        (Term.rename Nat.succ current) (Term.var 0) (Term.var 0)))

/-- Internal ordinal-like predecessor statement: an ordinal code is empty or
is the HF successor of a smaller ordinal code. -/
def ordinalCodeDomainZeroOrSuccTermAt (current : Term) : Formula :=
  or (eq current Term.zero)
    (ex (ordinalCodeDomainSuccBodyTermAt current))

/-- The sole local mathematical obligation left after generic PA strong
induction has been factored out. -/
def OrdinalCodeGraphRangeStrongStep : Prop :=
  ∀ {G : List Formula},
    BProv Ax_s G (hfStrongBelowAt ordinalCodeGraphRangePoint) →
    BProv Ax_s G ordinalCodeGraphRangePoint

/-- The three mathematical facts sufficient for the local range step.

`domain_decompose` is the finite-ordinal predecessor lemma. `graph_succ` is
closure of the beta-coded graph under its defining recurrence, and
`graph_codomain` says every graph output is ordinal-like. -/
structure OrdinalCodeGraphRangeLocalFacts where
  domain_decompose : ∀ {G : List Formula} {current : Term},
    BProv Ax_s G (subst (instTerm current) codedOrdinalDomain) →
    BProv Ax_s G (ordinalCodeDomainZeroOrSuccTermAt current)
  graph_succ : ∀ {G : List Formula} {raw pred current : Term},
    BProv Ax_s G (ordinalCodeGraphTermAt raw pred) →
    BProv Ax_s G (hfAdjoinGraphTermAt current pred pred) →
    BProv Ax_s G (ordinalCodeGraphTermAt (Term.succ raw) current)
  graph_codomain : ∀ {G : List Formula} {coded : Term},
    BProv Ax_s G (ordinalCodeGraphRangeExistsTermAt coded) →
    BProv Ax_s G (subst (instTerm coded) codedOrdinalDomain)

/-- Open the strong-induction hypothesis at the fresh predecessor in slot
zero while the current code occupies slot one. -/
theorem BProv_ordinalCodeGraphRangePoint_of_strongBelow
    {G : List Formula}
    (hbelow : BProv Ax_s G
      (rename Nat.succ
        (hfStrongBelowAt ordinalCodeGraphRangePoint)))
    (hlt : BProv Ax_s G (ltAt 0 1)) :
    BProv Ax_s G ordinalCodeGraphRangePoint := by
  have himp := BProv_allE_current_of_renamed hbelow
  rw [rename_rSkipParam_ordinalCodeGraphRangePoint] at himp
  exact BProv_mp Ax_s G _ _ himp hlt

/-- The finite-ordinal predecessor lemma, graph successor closure, and graph
codomain safety together discharge the sole local strong-induction step. -/
theorem OrdinalCodeGraphRangeStrongStep_of_localFacts
    (F : OrdinalCodeGraphRangeLocalFacts) :
    OrdinalCodeGraphRangeStrongStep := by
  intro G hbelow
  let domain : Formula := codedOrdinalDomain
  let range : Formula :=
    ordinalCodeGraphRangeExistsTermAt (Term.var 0)
  have hforward : BProv Ax_s G (imp domain range) := by
    let D : List Formula := domain :: G
    have hdomain : BProv Ax_s D domain :=
      BProv_ass (B := Ax_s) (G := D) (by simp [D])
    have hdecomp : BProv Ax_s D
        (ordinalCodeDomainZeroOrSuccTermAt (Term.var 0)) :=
      F.domain_decompose (by
        simpa only [subst_instTerm_var_zero_codedOrdinalDomain]
          using hdomain)
    let zeroCase : Formula := eq (Term.var 0) Term.zero
    let succBody : Formula :=
      ordinalCodeDomainSuccBodyTermAt (Term.var 0)
    let succCase : Formula := ex succBody
    have hzeroBranch : BProv Ax_s (zeroCase :: D) range := by
      let Z : List Formula := zeroCase :: D
      have hzero : BProv Ax_s Z
          (eq (Term.var 0) Term.zero) :=
        BProv_ass (B := Ax_s) (G := Z) (by simp [Z, zeroCase])
      have hgraphZero : BProv Ax_s Z
          (ordinalCodeGraphTermAt Term.zero Term.zero) :=
        BProv_Ax_s_ordinalCodeGraphTermAt_zero
      let graphContext : Formula :=
        ordinalCodeGraphTermAt
          (Term.rename Nat.succ Term.zero) (Term.var 0)
      have hgraphZeroInst : BProv Ax_s Z
          (subst (instTerm Term.zero) graphContext) := by
        simpa [graphContext, subst_ordinalCodeGraphTermAt,
          instTerm, Term.subst, Term.rename,
          term_subst_instTerm_rename_succ] using hgraphZero
      have hgraphCurrent : BProv Ax_s Z
          (ordinalCodeGraphTermAt Term.zero (Term.var 0)) :=
        by
          have htransport := BProv_eqElim
            (B := Ax_s) (G := Z)
            (s := Term.zero) (t := Term.var 0)
            (a := graphContext) (BProv_eqSym hzero) hgraphZeroInst
          simpa [graphContext, subst_ordinalCodeGraphTermAt,
            instTerm, Term.subst,
            term_subst_instTerm_rename_succ] using htransport
      apply BProv_exI (t := Term.zero)
      simpa [range, ordinalCodeGraphRangeExistsTermAt,
        subst_ordinalCodeGraphTermAt,
        subst, instTerm, Term.subst, Term.upSubst,
        Term.rename] using hgraphCurrent
    have hsuccBranch : BProv Ax_s (succCase :: D) range := by
      let S : List Formula := succCase :: D
      have hsuccEx : BProv Ax_s S (ex succBody) := by
        have hraw : BProv Ax_s S succCase :=
          BProv_ass (B := Ax_s) (G := S) (by simp [S])
        simpa [succCase] using hraw
      let C : List Formula := succBody :: S.map (rename Nat.succ)
      have hinner : BProv Ax_s C (rename Nat.succ range) := by
        have hsucc : BProv Ax_s C succBody :=
          BProv_ass (B := Ax_s) (G := C) (by simp [C])
        have hpredDomain : BProv Ax_s C codedOrdinalDomain := by
          simpa [succBody, ordinalCodeDomainSuccBodyTermAt] using
            BProv_andE1 hsucc
        have hrest : BProv Ax_s C
            (and
              (ltTermAt (Term.var 0) (Term.var 1))
              (hfAdjoinGraphTermAt
                (Term.var 1) (Term.var 0) (Term.var 0))) := by
          simpa [succBody, ordinalCodeDomainSuccBodyTermAt,
            Term.rename] using BProv_andE2 hsucc
        have hlt : BProv Ax_s C (ltAt 0 1) := by
          simpa [ltAt, ltTermAt_var] using BProv_andE1 hrest
        have hadjoin : BProv Ax_s C
            (hfAdjoinGraphTermAt
              (Term.var 1) (Term.var 0) (Term.var 0)) :=
          BProv_andE2 hrest
        have hbelowS : BProv Ax_s S
            (hfStrongBelowAt ordinalCodeGraphRangePoint) :=
          BProv_context_two hbelow
        have hbelowC : BProv Ax_s C
            (rename Nat.succ
              (hfStrongBelowAt ordinalCodeGraphRangePoint)) := by
          simpa [C] using
            (BProv_rename_succ_context_cons_of_sentences
              (B := Ax_s) Ax_s_sentences
              (a := succBody) hbelowS)
        have hpredPoint : BProv Ax_s C ordinalCodeGraphRangePoint :=
          BProv_ordinalCodeGraphRangePoint_of_strongBelow hbelowC hlt
        have hpredForward : BProv Ax_s C
            (imp codedOrdinalDomain
              (ordinalCodeGraphRangeExistsTermAt (Term.var 0))) := by
          simpa [ordinalCodeGraphRangePoint,
            ordinalCodeGraphRangeExistsTermAt,
            ordinalCodeGraphAt, iffForm, Term.rename] using
            BProv_andE1 hpredPoint
        have hpredRange : BProv Ax_s C
            (ordinalCodeGraphRangeExistsTermAt (Term.var 0)) :=
          BProv_mp Ax_s C _ _ hpredForward hpredDomain
        let graphBody : Formula :=
          ordinalCodeGraphTermAt (Term.var 0) (Term.var 1)
        let E : List Formula := graphBody :: C.map (rename Nat.succ)
        have hgraphBody : BProv Ax_s E graphBody :=
          BProv_ass (B := Ax_s) (G := E) (by simp [E])
        have hadjoinE : BProv Ax_s E
            (hfAdjoinGraphTermAt
              (Term.var 2) (Term.var 1) (Term.var 1)) := by
          have hraw :=
            BProv_rename_succ_context_cons_of_sentences
              (B := Ax_s) Ax_s_sentences
              (a := graphBody) hadjoin
          simpa [E, rename_hfAdjoinGraphTermAt_succ,
            Term.rename] using hraw
        have hnext : BProv Ax_s E
            (ordinalCodeGraphTermAt
              (Term.succ (Term.var 0)) (Term.var 2)) :=
          F.graph_succ hgraphBody hadjoinE
        have htarget : BProv Ax_s E
            (rename Nat.succ (rename Nat.succ range)) := by
          apply BProv_exI (t := Term.succ (Term.var 0))
          simpa [range, ordinalCodeGraphRangeExistsTermAt,
            rename_ordinalCodeGraphTermAt,
            subst_ordinalCodeGraphTermAt,
            rename, subst, instTerm, Term.rename, Term.subst,
            Term.upSubst, SetTheory.up] using hnext
        exact BProv_exE_of_sentences
          (B := Ax_s) Ax_s_sentences
          (G := C)
          (a := graphBody) (c := rename Nat.succ range)
          (by simpa [graphBody,
              ordinalCodeGraphRangeExistsTermAt,
              Term.rename] using hpredRange)
          (by simpa [E] using htarget)
      exact BProv_exE_of_sentences
        (B := Ax_s) Ax_s_sentences
        (G := S) (a := succBody) (c := range)
        hsuccEx (by simpa [C] using hinner)
    have hrange : BProv Ax_s D range := by
      apply BProv_orE
        (by simpa [zeroCase, succCase,
            ordinalCodeDomainZeroOrSuccTermAt] using hdecomp)
      · simpa [zeroCase] using hzeroBranch
      · simpa [succCase] using hsuccBranch
    simpa [D, domain] using BProv_impI hrange
  have hreverse : BProv Ax_s G (imp range domain) := by
    let D : List Formula := range :: G
    have hrange : BProv Ax_s D range :=
      BProv_ass (B := Ax_s) (G := D) (by simp [D])
    have hdomain : BProv Ax_s D domain :=
      F.graph_codomain (by simpa [range] using hrange)
    simpa [D, range] using BProv_impI hdomain
  simpa [ordinalCodeGraphRangePoint,
    range, domain, iffForm,
    ordinalCodeGraphRangeExistsTermAt,
    ordinalCodeGraphAt, Term.rename] using
    BProv_andI hforward hreverse

/-- A local strong-induction step for ordinal-like codes yields exactly the
`OrdinalCodeGraphProofs.range` field, including arbitrary contexts and coded
terms. -/
theorem OrdinalCodeGraphProofs_range_of_strongStep
    (hstep : OrdinalCodeGraphRangeStrongStep) :
    ∀ (G : List Formula) (coded : Term),
      BProv Ax_s G
        (iffForm
          (subst (instTerm coded) codedOrdinalDomain)
          (ex (ordinalCodeGraphTermAt
            (Term.var 0) (Term.rename Nat.succ coded)))) := by
  intro G coded
  have hall : BProv Ax_s [] (all ordinalCodeGraphRangePoint) :=
    BProv_Ax_s_all_of_strongStep ordinalCodeGraphRangePoint hstep
  have hallG : BProv Ax_s G (all ordinalCodeGraphRangePoint) :=
    BProv_weaken_nil (G := G) hall
  have hinst := BProv_allE (B := Ax_s) (G := G)
    (t := coded) hallG
  simpa [ordinalCodeGraphRangePoint,
    iffForm, ordinalCodeGraphAt, subst_ordinalCodeGraphTermAt,
    subst, instTerm, Term.subst, Term.upSubst, Term.rename,
    term_subst_instTerm_rename_succ] using hinst

/-! #### Finite-ordinal predecessor decomposition -/

/-- An HF object is identified with the empty object by saying that it equals
every empty object.  This avoids choosing an empty constant in the relational
HF language. -/
def HF_ordinalCodeZeroCase : SetTheory.Form :=
  SetTheory.Form.fAll
    (SetTheory.Form.fImp (AckermannHF.HF_emptyAt 0)
      (SetTheory.Form.fEq 1 0))

/-- Under the predecessor binder, slot zero is the predecessor and slot one
is the original ordinal. -/
def HF_ordinalCodeSuccBody : SetTheory.Form :=
  SetTheory.Form.fAnd (AckermannHF.HF_ordinalLikeAt 0)
    (SetTheory.Form.fAnd (SetTheory.Form.fMem 0 1)
      (AckermannHF.HF_succAt 1 0))

/-- Pointwise HF statement that every finite ordinal is empty or a successor
of an ordinal-like member. -/
def HF_ordinalCodeZeroOrSuccPoint : SetTheory.Form :=
  SetTheory.Form.fImp (AckermannHF.HF_ordinalLikeAt 0)
    (SetTheory.Form.fOr HF_ordinalCodeZeroCase
      (SetTheory.Form.fEx HF_ordinalCodeSuccBody))

/-- Universal closure of the finite-ordinal predecessor statement. -/
def HF_ordinalCodeZeroOrSuccSentence : SetTheory.Form :=
  SetTheory.Form.fAll HF_ordinalCodeZeroOrSuccPoint

theorem HF_ordinalCodeZeroOrSuccSentence_sentence :
    SetTheory.Sentence HF_ordinalCodeZeroOrSuccSentence := by
  intro i hi
  simp [HF_ordinalCodeZeroOrSuccSentence,
    HF_ordinalCodeZeroOrSuccPoint,
    HF_ordinalCodeZeroCase,
    HF_ordinalCodeSuccBody,
    AckermannHF.HF_ordinalLikeAt,
    AckermannHF.HF_transitiveAt,
    AckermannHF.HF_memTotalOnAt,
    AckermannHF.HF_emptyAt,
    AckermannHF.HF_succAt,
    AckermannHF.HF_adjoinAt,
    SetTheory.fIff, SetTheory.Free] at hi

/-- HFFin proves that every ordinal-like object is empty or the successor of
an ordinal-like member. -/
theorem BProv_HFFin_ordinalCodeZeroOrSuccSentence :
    SetTheory.BProv AckermannHF.HFFinAx_s []
      HF_ordinalCodeZeroOrSuccSentence := by
  apply SetTheory.completeness_inf AckermannHF.HFFinAx_s
  · exact AckermannHF.Sentences_HFFin
  · exact HF_ordinalCodeZeroOrSuccSentence_sentence
  · intro Dom mem v hHF
    let M := AckermannHF.firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
    intro current hcurrent
    have hordinal : AckermannHF.OrdinalLike M.mem current :=
      (AckermannHF.HF_ordinalLikeAt_spec
        (SetTheory.scons current v) 0).mp hcurrent
    rcases AckermannHF.FirstOrderFiniteAdjunctionModel.ordinalLike_empty_or_succ
        M hordinal with hempty | ⟨pred, hpredMem, hsucc⟩
    · left
      intro empty hemptySat
      have hemptyEq : empty = M.empty :=
        (AckermannHF.FirstOrderAdjunctionModel.HF_emptyAt_empty
          M.toFirstOrderAdjunctionModel
          (SetTheory.scons empty (SetTheory.scons current v)) 0).mp
          hemptySat
      exact hempty.trans hemptyEq.symm
    · right
      refine ⟨pred, ?_, ?_, ?_⟩
      · apply (AckermannHF.HF_ordinalLikeAt_spec
          (SetTheory.scons pred (SetTheory.scons current v)) 0).mpr
        exact AckermannHF.OrdinalLike.of_mem hordinal hpredMem
      · exact hpredMem
      · apply (AckermannHF.FirstOrderAdjunctionModel.HF_succAt_spec
          M.toFirstOrderAdjunctionModel
          (SetTheory.scons pred (SetTheory.scons current v)) 1 0).mpr
        exact hsucc

/-- Translation of the HF empty-identification branch. -/
def ordinalCodeZeroCase : Formula :=
  all (imp (hfEmptyAt 0)
    (eq (Term.var 1) (Term.var 0)))

/-- Translation of the HF successor branch before membership is refined to
strict numeric order. -/
def ordinalCodeMemSuccBody : Formula :=
  and codedOrdinalDomain
    (and (hfMemAt 0 1) (hfAdjoinGraphAt 1 0 0))

def ordinalCodeMemZeroOrSuccPoint : Formula :=
  imp codedOrdinalDomain
    (or ordinalCodeZeroCase
      (ex ordinalCodeMemSuccBody))

theorem translateHFFormula_ordinalCodeZeroOrSuccSentence :
    translateHFFormula HF_ordinalCodeZeroOrSuccSentence =
      all ordinalCodeMemZeroOrSuccPoint := by
  rfl

/-- PA proves the direct Ackermann translation of the HFFin ordinal
predecessor sentence. -/
theorem BProv_Ax_s_ordinalCodeMemZeroOrSuccSentence {G : List Formula} :
    BProv Ax_s G (all ordinalCodeMemZeroOrSuccPoint) := by
  apply BProv_weaken_nil
  have htranslated : BProv translatedHFFinAx []
      (translateHFFormula HF_ordinalCodeZeroOrSuccSentence) :=
    BProv_translateHFFormula_of_BProv_HFFin
      BProv_HFFin_ordinalCodeZeroOrSuccSentence
  have hpa : BProv Ax_s []
      (translateHFFormula HF_ordinalCodeZeroOrSuccSentence) :=
    BProv_lift_translatedHFFinAx_to_PA
      (fun f hf => BProv_Ax_s_of_translatedHFFinAx hf)
      htranslated
  rwa [translateHFFormula_ordinalCodeZeroOrSuccSentence] at hpa

def ordinalCodeZeroCaseTermAt (current : Term) : Formula :=
  all (imp (hfEmptyAt 0)
    (eq (Term.rename Nat.succ current) (Term.var 0)))

def ordinalCodeMemSuccBodyTermAt (current : Term) : Formula :=
  and codedOrdinalDomain
    (and
      (hfMemTermAt 0 (Term.rename Nat.succ current))
      (hfAdjoinGraphTermAt
        (Term.rename Nat.succ current) (Term.var 0) (Term.var 0)))

def ordinalCodeMemZeroOrSuccTermAt (current : Term) : Formula :=
  or (ordinalCodeZeroCaseTermAt current)
    (ex (ordinalCodeMemSuccBodyTermAt current))

theorem subst_up_inst_hfEmptyAt_zero (current : Term) :
    subst (Term.upSubst (instTerm current)) (hfEmptyAt 0) =
      hfEmptyAt 0 := by
  change subst (Term.upSubst (instTerm current))
      (hfEmptyTermAt (Term.var 0)) =
    hfEmptyTermAt (Term.var 0)
  rw [subst_hfEmptyTermAt]
  rfl

theorem subst_up_inst_codedOrdinalDomain (current : Term) :
    subst (Term.upSubst (instTerm current)) codedOrdinalDomain =
      codedOrdinalDomain := by
  calc
    subst (Term.upSubst (instTerm current)) codedOrdinalDomain =
        subst (fun n : Nat => Term.var n) codedOrdinalDomain := by
      apply subst_ext_free
      intro n hn
      have hn0 := codedOrdinalDomain_free hn
      subst n
      rfl
    _ = codedOrdinalDomain := subst_id codedOrdinalDomain

theorem subst_up_inst_hfMemAt_zero_one (current : Term) :
    subst (Term.upSubst (instTerm current)) (hfMemAt 0 1) =
      hfMemTermAt 0 (Term.rename Nat.succ current) := by
  have h := subst_up_hfMemTermAt_zero_rename_succ
    (instTerm current) (Term.var 0)
  simpa [hfMemTermAt_var, Term.rename, Term.subst,
    instTerm] using h

theorem subst_up_inst_hfAdjoinGraphAt_one_zero_zero
    (current : Term) :
    subst (Term.upSubst (instTerm current))
        (hfAdjoinGraphAt 1 0 0) =
      hfAdjoinGraphTermAt
        (Term.rename Nat.succ current) (Term.var 0) (Term.var 0) := by
  change subst (Term.upSubst (instTerm current))
      (hfAdjoinGraphTermAt
        (Term.var 1) (Term.var 0) (Term.var 0)) = _
  rw [subst_hfAdjoinGraphTermAt]
  simp [Term.subst, Term.upSubst, instTerm]

theorem subst_instTerm_ordinalCodeMemZeroOrSuccPoint
    (current : Term) :
    subst (instTerm current) ordinalCodeMemZeroOrSuccPoint =
      imp (subst (instTerm current) codedOrdinalDomain)
        (ordinalCodeMemZeroOrSuccTermAt current) := by
  simp [ordinalCodeMemZeroOrSuccPoint,
    ordinalCodeZeroCase,
    ordinalCodeMemSuccBody,
    ordinalCodeZeroCaseTermAt,
    ordinalCodeMemSuccBodyTermAt,
    ordinalCodeMemZeroOrSuccTermAt,
    subst_up_inst_hfEmptyAt_zero,
    subst_up_inst_codedOrdinalDomain,
    subst_up_inst_hfMemAt_zero_one,
    subst_up_inst_hfAdjoinGraphAt_one_zero_zero,
    subst, instTerm, Term.subst, Term.upSubst]

/-- The closed PA numeral zero codes an empty HF object. -/
theorem BProv_Ax_s_hfEmptyTermAt_zero {G : List Formula} :
    BProv Ax_s G (hfEmptyTermAt Term.zero) := by
  apply BProv_weaken_nil
  have hraw := BProv_Ax_s_HF_empty_zero_body_of_member_bot
    BProv_Ax_s_HF_empty_zero_member_bot
  simpa [hfEmptyTermAt, subst,
    subst_up_inst_hfMemAt_zero_one] using hraw

/-- A term-parametric empty code has no member in any selected slot. -/
theorem BProv_hfEmptyTermAt_not_mem
    {B : Formula → Prop} {G : List Formula}
    {setCode : Term} {elem : Nat}
    (hempty : BProv B G (hfEmptyTermAt setCode)) :
    BProv B G (imp (hfMemTermAt elem setCode) bot) := by
  have hraw := BProv_allE (B := B) (G := G)
    (t := Term.var elem) hempty
  simpa only [hfEmptyTermAt, subst,
    subst_instTerm_var_hfMemTermAt_zero_rename_succ] using hraw

/-- Any two term-parametric empty codes have pointwise identical Ackermann
membership predicates. -/
theorem BProv_Ax_s_same_members_of_hfEmptyTermAt
    {G : List Formula} {left right : Term}
    (hleft : BProv Ax_s G (hfEmptyTermAt left))
    (hright : BProv Ax_s G (hfEmptyTermAt right)) :
    BProv Ax_s G
      (all (iffForm
        (hfMemTermAt 0 (Term.rename Nat.succ left))
        (hfMemTermAt 0 (Term.rename Nat.succ right)))) := by
  let Q : List Formula := G.map (rename Nat.succ)
  have hleftRenRaw : BProv Ax_s Q
      (rename Nat.succ (hfEmptyTermAt left)) :=
    BProv_rename_of_sentences
      (B := Ax_s) Ax_s_sentences
      hleft Nat.succ
  have hleftRen : BProv Ax_s Q
      (hfEmptyTermAt (Term.rename Nat.succ left)) := by
    simpa [rename_hfEmptyTermAt] using hleftRenRaw
  have hrightRenRaw : BProv Ax_s Q
      (rename Nat.succ (hfEmptyTermAt right)) :=
    BProv_rename_of_sentences
      (B := Ax_s) Ax_s_sentences
      hright Nat.succ
  have hrightRen : BProv Ax_s Q
      (hfEmptyTermAt (Term.rename Nat.succ right)) := by
    simpa [rename_hfEmptyTermAt] using hrightRenRaw
  let leftMem : Formula :=
    hfMemTermAt 0 (Term.rename Nat.succ left)
  let rightMem : Formula :=
    hfMemTermAt 0 (Term.rename Nat.succ right)
  have hforward : BProv Ax_s Q (imp leftMem rightMem) := by
    let C : List Formula := leftMem :: Q
    have hmem : BProv Ax_s C leftMem :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hnot : BProv Ax_s C (imp leftMem bot) :=
      BProv_context_cons (B := Ax_s) (a := leftMem)
        (BProv_hfEmptyTermAt_not_mem hleftRen)
    have hbot : BProv Ax_s C bot :=
      BProv_mp Ax_s C leftMem bot hnot hmem
    simpa [C] using BProv_impI (BProv_botE (a := rightMem) hbot)
  have hreverse : BProv Ax_s Q (imp rightMem leftMem) := by
    let C : List Formula := rightMem :: Q
    have hmem : BProv Ax_s C rightMem :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hnot : BProv Ax_s C (imp rightMem bot) :=
      BProv_context_cons (B := Ax_s) (a := rightMem)
        (BProv_hfEmptyTermAt_not_mem hrightRen)
    have hbot : BProv Ax_s C bot :=
      BProv_mp Ax_s C rightMem bot hnot hmem
    simpa [C] using BProv_impI (BProv_botE (a := leftMem) hbot)
  have hbody : BProv Ax_s Q (iffForm leftMem rightMem) :=
    BProv_andI hforward hreverse
  simpa [leftMem, rightMem] using
    (BProv_allI_of_sentences
      (B := Ax_s) (G := G)
      Ax_s_sentences hbody)

/-- Ackermann extensionality identifies any two term-parametric empty codes. -/
theorem BProv_Ax_s_eq_of_hfEmptyTermAt_hfEmptyTermAt
    {G : List Formula} {left right : Term}
    (hleft : BProv Ax_s G (hfEmptyTermAt left))
    (hright : BProv Ax_s G (hfEmptyTermAt right)) :
    BProv Ax_s G (eq left right) :=
  BProv_Ax_s_eq_of_hfSameMembersTermAt
    (BProv_Ax_s_same_members_of_hfEmptyTermAt hleft hright)

/-- A PA variable satisfying the translated empty predicate equals the closed
Ackermann empty code `0`. -/
theorem BProv_Ax_s_eq_zero_of_hfEmptyAt
    {G : List Formula} {set : Nat}
    (hempty : BProv Ax_s G (hfEmptyAt set)) :
    BProv Ax_s G (eq (Term.var set) Term.zero) := by
  apply BProv_Ax_s_eq_of_hfEmptyTermAt_hfEmptyTermAt
    (by simpa [hfEmptyAt] using hempty)
  exact BProv_Ax_s_hfEmptyTermAt_zero

/-- The only coded endpoint of the ordinal-code graph at raw zero is the
closed Ackermann empty code. -/
theorem BProv_Ax_s_eq_zero_of_ordinalCodeGraphTermAt_zero
    {G : List Formula} {coded : Term}
    (hgraph : BProv Ax_s G
      (ordinalCodeGraphTermAt Term.zero coded)) :
    BProv Ax_s G (eq coded Term.zero) :=
  BProv_Ax_s_ordinalCodeGraphTermAt_functional_of_traceAgreement
    ordinalCodeTraceAgreementProof hgraph
    BProv_Ax_s_ordinalCodeGraphTermAt_zero

theorem BProv_Ax_s_ordinalCodeMemZeroOrSuccTermAt_of_domain
    {G : List Formula} {current : Term}
    (hdomain : BProv Ax_s G
      (subst (instTerm current) codedOrdinalDomain)) :
    BProv Ax_s G (ordinalCodeMemZeroOrSuccTermAt current) := by
  have hall : BProv Ax_s G (all ordinalCodeMemZeroOrSuccPoint) :=
    BProv_Ax_s_ordinalCodeMemZeroOrSuccSentence
  have hpointRaw := BProv_allE
    (B := Ax_s) (G := G) (t := current) hall
  have hpoint : BProv Ax_s G
      (imp (subst (instTerm current) codedOrdinalDomain)
        (ordinalCodeMemZeroOrSuccTermAt current)) := by
    rw [subst_instTerm_ordinalCodeMemZeroOrSuccPoint] at hpointRaw
    exact hpointRaw
  exact BProv_mp Ax_s G _ _ hpoint hdomain

theorem rename_up_succ_codedOrdinalDomain :
    rename (SetTheory.up Nat.succ) codedOrdinalDomain =
      codedOrdinalDomain := by
  calc
    rename (SetTheory.up Nat.succ) codedOrdinalDomain =
        rename (fun n : Nat => n) codedOrdinalDomain := by
      apply rename_ext_free
      intro n hn
      have hn0 := codedOrdinalDomain_free hn
      subst n
      rfl
    _ = codedOrdinalDomain := rename_id codedOrdinalDomain

theorem subst_inst_var_zero_rename_up_succ_ordinalCode_lt :
    subst (instTerm (Term.var 0))
        (rename (SetTheory.up Nat.succ)
          (ltTermAt (Term.var 0)
            (Term.rename Nat.succ (Term.var 0)))) =
      ltTermAt (Term.var 0)
        (Term.rename Nat.succ (Term.var 0)) := by
  rfl

theorem subst_inst_var_zero_rename_up_succ_ordinalCode_adjoin :
    subst (instTerm (Term.var 0))
        (rename (SetTheory.up Nat.succ)
          (hfAdjoinGraphTermAt
            (Term.rename Nat.succ (Term.var 0))
            (Term.var 0) (Term.var 0))) =
      hfAdjoinGraphTermAt
        (Term.rename Nat.succ (Term.var 0))
        (Term.var 0) (Term.var 0) := by
  rfl

/-- Variable-slot form of the exact arithmetic predecessor decomposition. -/
theorem BProv_Ax_s_ordinalCodeDomainZeroOrSuccAt_of_domain
    {G : List Formula}
    (hdomain : BProv Ax_s G codedOrdinalDomain) :
    BProv Ax_s G
      (ordinalCodeDomainZeroOrSuccTermAt (Term.var 0)) := by
  have hcases : BProv Ax_s G
      (ordinalCodeMemZeroOrSuccTermAt (Term.var 0)) :=
    BProv_Ax_s_ordinalCodeMemZeroOrSuccTermAt_of_domain
      (by simpa only [subst_instTerm_var_zero_codedOrdinalDomain]
        using hdomain)
  let zeroCase : Formula :=
    ordinalCodeZeroCaseTermAt (Term.var 0)
  let succBody : Formula :=
    ordinalCodeMemSuccBodyTermAt (Term.var 0)
  let succCase : Formula := ex succBody
  have hzero : BProv Ax_s (zeroCase :: G)
      (ordinalCodeDomainZeroOrSuccTermAt (Term.var 0)) := by
    let Z : List Formula := zeroCase :: G
    have hall : BProv Ax_s Z zeroCase :=
      BProv_ass (B := Ax_s) (G := Z) (by simp [Z])
    have himpRaw := BProv_allE
      (B := Ax_s) (G := Z) (t := Term.zero) hall
    have himp : BProv Ax_s Z
        (imp (hfEmptyTermAt Term.zero)
          (eq (Term.var 0) Term.zero)) := by
      simpa [zeroCase, ordinalCodeZeroCaseTermAt,
        hfEmptyAt, subst_hfEmptyTermAt,
        subst, instTerm, Term.subst, Term.upSubst,
        Term.rename] using himpRaw
    have hempty : BProv Ax_s Z (hfEmptyTermAt Term.zero) :=
      BProv_Ax_s_hfEmptyTermAt_zero
    have heq : BProv Ax_s Z (eq (Term.var 0) Term.zero) :=
      BProv_mp Ax_s Z _ _ himp hempty
    exact BProv_orI1 (B := Ax_s) (G := Z)
      (b := ex (ordinalCodeDomainSuccBodyTermAt (Term.var 0))) heq
  have hsucc : BProv Ax_s (succCase :: G)
      (ordinalCodeDomainZeroOrSuccTermAt (Term.var 0)) := by
    let S : List Formula := succCase :: G
    have hex : BProv Ax_s S (ex succBody) := by
      have hraw : BProv Ax_s S succCase :=
        BProv_ass (B := Ax_s) (G := S) (by simp [S])
      simpa [succCase] using hraw
    let C : List Formula := succBody :: S.map (rename Nat.succ)
    have hinner : BProv Ax_s C
        (rename Nat.succ
          (ordinalCodeDomainZeroOrSuccTermAt (Term.var 0))) := by
      have hbody : BProv Ax_s C succBody :=
        BProv_ass (B := Ax_s) (G := C) (by simp [C])
      have hpredDomain : BProv Ax_s C codedOrdinalDomain := by
        simpa [succBody,
          ordinalCodeMemSuccBodyTermAt] using BProv_andE1 hbody
      have hrest : BProv Ax_s C
          (and (hfMemAt 0 1) (hfAdjoinGraphAt 1 0 0)) := by
        simpa [succBody,
          ordinalCodeMemSuccBodyTermAt,
          hfMemTermAt_var, hfAdjoinGraphAt,
          Term.rename] using BProv_andE2 hbody
      have hmem : BProv Ax_s C (hfMemAt 0 1) :=
        BProv_andE1 hrest
      have hlt : BProv Ax_s C (ltAt 0 1) :=
        BProv_Ax_s_ltAt_of_hfMemAt hmem
      have hadjoin : BProv Ax_s C (hfAdjoinGraphAt 1 0 0) :=
        BProv_andE2 hrest
      have hprodBody : BProv Ax_s C
          (ordinalCodeDomainSuccBodyTermAt (Term.var 0)) := by
        simpa [ordinalCodeDomainSuccBodyTermAt,
          ltAt, ltTermAt_var, hfAdjoinGraphAt,
          Term.rename] using
          BProv_andI hpredDomain (BProv_andI hlt hadjoin)
      have hexTarget : BProv Ax_s C
          (rename Nat.succ
            (ex (ordinalCodeDomainSuccBodyTermAt (Term.var 0)))) := by
        apply BProv_exI (t := Term.var 0)
        simpa [ordinalCodeDomainSuccBodyTermAt,
          rename_up_succ_codedOrdinalDomain,
          subst_instTerm_var_zero_codedOrdinalDomain,
          subst_inst_var_zero_rename_up_succ_ordinalCode_lt,
          subst_inst_var_zero_rename_up_succ_ordinalCode_adjoin,
          rename, subst] using hprodBody
      simpa [ordinalCodeDomainZeroOrSuccTermAt, rename] using
        (BProv_orI2 (B := Ax_s) (G := C)
          (a := rename Nat.succ (eq (Term.var 0) Term.zero))
          hexTarget)
    exact BProv_exE_of_sentences
      (B := Ax_s) Ax_s_sentences
      (G := S) (a := succBody)
      (c := ordinalCodeDomainZeroOrSuccTermAt (Term.var 0))
      hex (by simpa [C] using hinner)
  apply BProv_orE
    (by simpa [zeroCase, succBody, succCase,
        ordinalCodeMemZeroOrSuccTermAt] using hcases)
  · simpa [zeroCase] using hzero
  · simpa [succCase] using hsucc

theorem subst_ordinalCodeDomainZeroOrSuccTermAt
    (sigma : Nat → Term) (current : Term) :
    subst sigma (ordinalCodeDomainZeroOrSuccTermAt current) =
      ordinalCodeDomainZeroOrSuccTermAt (Term.subst sigma current) := by
  have hdomain :
      subst (Term.upSubst sigma) codedOrdinalDomain =
        codedOrdinalDomain := by
    calc
      subst (Term.upSubst sigma) codedOrdinalDomain =
          subst (fun n : Nat => Term.var n) codedOrdinalDomain := by
        apply subst_ext_free
        intro n hn
        have hn0 := codedOrdinalDomain_free hn
        subst n
        rfl
      _ = codedOrdinalDomain := subst_id codedOrdinalDomain
  simp [ordinalCodeDomainZeroOrSuccTermAt,
    ordinalCodeDomainSuccBodyTermAt,
    subst_ltTermAt, subst_hfAdjoinGraphTermAt,
    hdomain, subst, Term.subst, Term.upSubst,
    Term.subst_rename_succ_up]

/-- PA proves the universal finite-ordinal predecessor decomposition. -/
theorem BProv_Ax_s_all_ordinalCodeDomainZeroOrSucc {G : List Formula} :
    BProv Ax_s G
      (all
        (imp codedOrdinalDomain
          (ordinalCodeDomainZeroOrSuccTermAt (Term.var 0)))) := by
  apply BProv_weaken_nil
  let D : List Formula := [codedOrdinalDomain]
  have hdomain : BProv Ax_s D codedOrdinalDomain :=
    BProv_ass (B := Ax_s) (G := D) (by simp [D])
  have htarget : BProv Ax_s D
      (ordinalCodeDomainZeroOrSuccTermAt (Term.var 0)) :=
    BProv_Ax_s_ordinalCodeDomainZeroOrSuccAt_of_domain hdomain
  have himp : BProv Ax_s []
      (imp codedOrdinalDomain
        (ordinalCodeDomainZeroOrSuccTermAt (Term.var 0))) := by
    simpa [D] using BProv_impI htarget
  exact BProv_allI_of_sentences
    (B := Ax_s) (G := [])
    Ax_s_sentences himp

/-- Exact proof term for
`OrdinalCodeGraphRangeLocalFacts.domain_decompose`. -/
theorem OrdinalCodeGraphRangeLocalFacts_domain_decompose :
    ∀ {G : List Formula} {current : Term},
      BProv Ax_s G (subst (instTerm current) codedOrdinalDomain) →
      BProv Ax_s G (ordinalCodeDomainZeroOrSuccTermAt current) := by
  intro G current hdomain
  have hall : BProv Ax_s G
      (all
        (imp codedOrdinalDomain
          (ordinalCodeDomainZeroOrSuccTermAt (Term.var 0)))) :=
    BProv_Ax_s_all_ordinalCodeDomainZeroOrSucc
  have himpRaw := BProv_allE
    (B := Ax_s) (G := G) (t := current) hall
  have himp : BProv Ax_s G
      (imp
        (subst (instTerm current) codedOrdinalDomain)
        (ordinalCodeDomainZeroOrSuccTermAt current)) := by
    simpa [subst, subst_ordinalCodeDomainZeroOrSuccTermAt,
      instTerm, Term.subst, Term.upSubst] using himpRaw
  exact BProv_mp Ax_s G _ _ himp hdomain

/-- Remaining successor-closure obligation for the ordinal-code graph. -/
def OrdinalCodeGraphSuccClosure : Prop :=
  ∀ {G : List Formula} {raw pred current : Term},
    BProv Ax_s G (ordinalCodeGraphTermAt raw pred) →
    BProv Ax_s G (hfAdjoinGraphTermAt current pred pred) →
    BProv Ax_s G (ordinalCodeGraphTermAt (Term.succ raw) current)

/-- Remaining codomain-safety obligation for the ordinal-code graph. -/
def OrdinalCodeGraphCodomain : Prop :=
  ∀ {G : List Formula} {coded : Term},
    BProv Ax_s G (ordinalCodeGraphRangeExistsTermAt coded) →
    BProv Ax_s G (subst (instTerm coded) codedOrdinalDomain)

/-- The proved finite-ordinal decomposition reduces the local range package to
successor closure and codomain safety alone. -/
theorem OrdinalCodeGraphRangeLocalFacts_of_succ_codomain
    (hsucc : OrdinalCodeGraphSuccClosure)
    (hcodomain : OrdinalCodeGraphCodomain) :
    OrdinalCodeGraphRangeLocalFacts where
  domain_decompose := OrdinalCodeGraphRangeLocalFacts_domain_decompose
  graph_succ := hsucc
  graph_codomain := hcodomain

/-- Successor closure and codomain safety now imply the exact public graph
range field; predecessor decomposition is fully discharged. -/
theorem OrdinalCodeGraphProofs_range_of_succ_codomain
    (hsucc : OrdinalCodeGraphSuccClosure)
    (hcodomain : OrdinalCodeGraphCodomain) :
    ∀ (G : List Formula) (coded : Term),
      BProv Ax_s G
        (iffForm
          (subst (instTerm coded) codedOrdinalDomain)
          (ex (ordinalCodeGraphTermAt
            (Term.var 0) (Term.rename Nat.succ coded)))) :=
  OrdinalCodeGraphProofs_range_of_strongStep
    (OrdinalCodeGraphRangeStrongStep_of_localFacts
      (OrdinalCodeGraphRangeLocalFacts_of_succ_codomain
        hsucc hcodomain))

/-! ### Atomic equality through ordinal codes -/

/-- Binder-free equality comparison through a common ordinal-code witness. -/
def codeEqualityBodyTermAt
    (leftCode rightCode leftRaw rightRaw : Term) : Formula :=
  and
    (ordinalCodeGraphTermAt leftRaw leftCode)
    (and
      (ordinalCodeGraphTermAt rightRaw rightCode)
      (eq leftCode rightCode))

/-- Relational equality obtained by evaluating both raw terms into coded
finite ordinals and comparing those codes. -/
def codeEqualityTermAt (leftRaw rightRaw : Term) : Formula :=
  ex (ex
    (codeEqualityBodyTermAt
      (Term.var 1) (Term.var 0)
      (Term.rename (fun n ↦ n+2) leftRaw)
      (Term.rename (fun n ↦ n+2) rightRaw)))

theorem subst_codeEqualityBodyTermAt
    (sigma : Nat → Term)
    (leftCode rightCode leftRaw rightRaw : Term) :
    subst sigma
        (codeEqualityBodyTermAt
          leftCode rightCode leftRaw rightRaw) =
      codeEqualityBodyTermAt
        (Term.subst sigma leftCode)
        (Term.subst sigma rightCode)
        (Term.subst sigma leftRaw)
        (Term.subst sigma rightRaw) := by
  simp [codeEqualityBodyTermAt,
    subst_ordinalCodeGraphTermAt, subst]

theorem subst_codeEqualityTermAt
    (sigma : Nat → Term) (leftRaw rightRaw : Term) :
    subst sigma (codeEqualityTermAt leftRaw rightRaw) =
      codeEqualityTermAt
        (Term.subst sigma leftRaw)
        (Term.subst sigma rightRaw) := by
  simp [codeEqualityTermAt,
    subst_codeEqualityBodyTermAt,
    subst, Term.subst, Term.upSubst, Term.rename,
    term_subst_up_up_rename_add_two]

theorem rename_codeEqualityTermAt
    (r : Nat → Nat) (leftRaw rightRaw : Term) :
    rename r (codeEqualityTermAt leftRaw rightRaw) =
      codeEqualityTermAt
        (Term.rename r leftRaw) (Term.rename r rightRaw) := by
  rw [← subst_var_rename, subst_codeEqualityTermAt]
  simp only [term_subst_var_rename]

theorem subst_instTerm_codeEqualityBody_inner
    (leftCode rightCode leftRaw rightRaw : Term) :
    subst (instTerm rightCode)
        (codeEqualityBodyTermAt
          (Term.rename Nat.succ leftCode)
          (Term.var 0)
          (Term.rename Nat.succ leftRaw)
          (Term.rename Nat.succ rightRaw)) =
      codeEqualityBodyTermAt
        leftCode rightCode leftRaw rightRaw := by
  rw [subst_codeEqualityBodyTermAt]
  simp [instTerm, Term.subst, term_subst_instTerm_rename_succ]

theorem subst_instTerm_codeEqualityBody_outer
    (leftCode leftRaw rightRaw : Term) :
    subst (instTerm leftCode)
        (ex (codeEqualityBodyTermAt
          (Term.var 1) (Term.var 0)
          (Term.rename (fun n ↦ n+2) leftRaw)
          (Term.rename (fun n ↦ n+2) rightRaw))) =
      ex (codeEqualityBodyTermAt
        (Term.rename Nat.succ leftCode) (Term.var 0)
        (Term.rename Nat.succ leftRaw)
        (Term.rename Nat.succ rightRaw)) := by
  simp only [subst, subst_codeEqualityBodyTermAt]
  simp [instTerm, Term.subst, Term.upSubst,
    term_subst_upSubst_instTerm_rename_two_succ]

/-- Package two explicit code witnesses and their equality into relational
equality. -/
theorem BProv_codeEqualityTermAt_of_components
    {B : Formula → Prop} {G : List Formula}
    {leftCode rightCode leftRaw rightRaw : Term}
    (hleft : BProv B G
      (ordinalCodeGraphTermAt leftRaw leftCode))
    (hright : BProv B G
      (ordinalCodeGraphTermAt rightRaw rightCode))
    (heq : BProv B G (eq leftCode rightCode)) :
    BProv B G (codeEqualityTermAt leftRaw rightRaw) := by
  have hbody : BProv B G
      (codeEqualityBodyTermAt
        leftCode rightCode leftRaw rightRaw) := by
    simpa [codeEqualityBodyTermAt] using
      BProv_andI hleft (BProv_andI hright heq)
  have hinnerInst : BProv B G
      (subst (instTerm rightCode)
        (codeEqualityBodyTermAt
          (Term.rename Nat.succ leftCode)
          (Term.var 0)
          (Term.rename Nat.succ leftRaw)
          (Term.rename Nat.succ rightRaw))) := by
    rw [subst_instTerm_codeEqualityBody_inner]
    exact hbody
  have hinner : BProv B G
      (ex (codeEqualityBodyTermAt
        (Term.rename Nat.succ leftCode) (Term.var 0)
        (Term.rename Nat.succ leftRaw)
        (Term.rename Nat.succ rightRaw))) :=
    BProv_exI hinnerInst
  have houterInst : BProv B G
      (subst (instTerm leftCode)
        (ex (codeEqualityBodyTermAt
          (Term.var 1) (Term.var 0)
          (Term.rename (fun n ↦ n+2) leftRaw)
          (Term.rename (fun n ↦ n+2) rightRaw)))) := by
    rw [subst_instTerm_codeEqualityBody_outer]
    exact hinner
  simpa [codeEqualityTermAt] using
    (BProv_exI houterInst)

/-! ### Term-language compatibility reduction -/

/-- The exact dual of `OrdinalCodeGraphProofs.injective` needed by translated
term graphs: a raw PA value has at most one ordinal code. -/
def OrdinalCodeGraphFunctional : Prop :=
  ∀ {G : List Formula} {raw coded₁ coded₂ : Term},
    BProv Ax_s G (ordinalCodeGraphTermAt raw coded₁) →
    BProv Ax_s G (ordinalCodeGraphTermAt raw coded₂) →
    BProv Ax_s G (eq coded₁ coded₂)

/-- The trace-agreement induction frontier canonically supplies graph
functionality. -/
theorem OrdinalCodeGraphFunctional_of_traceAgreement
    (hagreement : OrdinalCodeTraceAgreementProof) :
    OrdinalCodeGraphFunctional := by
  intro G raw coded₁ coded₂ hgraph₁ hgraph₂
  exact BProv_Ax_s_ordinalCodeGraphTermAt_functional_of_traceAgreement
    hagreement hgraph₁ hgraph₂

/-- PA proves that the ordinal-code graph is single-valued in its coded
output.  This is the direct public endpoint of the concrete trace-agreement
induction. -/
theorem BProv_Ax_s_ordinalCodeGraphTermAt_functional
    {G : List Formula} {raw coded₁ coded₂ : Term}
    (hgraph₁ : BProv Ax_s G
      (ordinalCodeGraphTermAt raw coded₁))
    (hgraph₂ : BProv Ax_s G
      (ordinalCodeGraphTermAt raw coded₂)) :
    BProv Ax_s G (eq coded₁ coded₂) :=
  BProv_Ax_s_ordinalCodeGraphTermAt_functional_of_traceAgreement
    ordinalCodeTraceAgreementProof hgraph₁ hgraph₂

/-- Concrete operation-facing functionality package for the ordinal-code
term-graph induction. -/
theorem ordinalCodeGraphFunctional : OrdinalCodeGraphFunctional :=
  OrdinalCodeGraphFunctional_of_traceAgreement
    ordinalCodeTraceAgreementProof

theorem rename_hfAdjoinGraphTermAt
    (r : Nat → Nat) (newCode oldCode elemCode : Term) :
    rename r (hfAdjoinGraphTermAt newCode oldCode elemCode) =
      hfAdjoinGraphTermAt
        (Term.rename r newCode)
        (Term.rename r oldCode)
        (Term.rename r elemCode) := by
  rw [← subst_var_rename, subst_hfAdjoinGraphTermAt]
  simp only [term_subst_var_rename]

/-- Restrict a bounded ordinal-code recurrence to a smaller raw bound. -/
theorem BProv_Ax_s_ordinalCodeStepsTermAt_of_leTerm
    {G : List Formula}
    {sequenceCode sequenceStep low high : Term}
    (hsteps : BProv Ax_s G
      (ordinalCodeStepsTermAt sequenceCode sequenceStep high))
    (hle : BProv Ax_s G (leTermAt low high)) :
    BProv Ax_s G
      (ordinalCodeStepsTermAt sequenceCode sequenceStep low) := by
  let antecedent : Formula :=
    ltTermAt (Term.var 0) (Term.rename Nat.succ low)
  let consequent : Formula :=
    ordinalCodeStepWitnessTermAt
      (Term.rename Nat.succ sequenceCode)
      (Term.rename Nat.succ sequenceStep)
      (Term.var 0)
  let Q : List Formula := G.map (rename Nat.succ)
  have hstepsRaw := BProv_rename_of_sentences
    (B := Ax_s) Ax_s_sentences
    hsteps Nat.succ
  have hstepsQ : BProv Ax_s Q
      (ordinalCodeStepsTermAt
        (Term.rename Nat.succ sequenceCode)
        (Term.rename Nat.succ sequenceStep)
        (Term.rename Nat.succ high)) := by
    simpa [Q, rename_ordinalCodeStepsTermAt] using hstepsRaw
  have hleRaw := BProv_rename_of_sentences
    (B := Ax_s) Ax_s_sentences
    hle Nat.succ
  have hleQ : BProv Ax_s Q
      (leTermAt (Term.rename Nat.succ low)
        (Term.rename Nat.succ high)) := by
    simpa [Q, rename_leTermAt] using hleRaw
  have hbody : BProv Ax_s (antecedent :: Q) consequent := by
    let C : List Formula := antecedent :: Q
    have hltLow : BProv Ax_s C
        (ltTermAt (Term.var 0) (Term.rename Nat.succ low)) :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C, antecedent])
    have hleC : BProv Ax_s C
        (leTermAt (Term.rename Nat.succ low)
          (Term.rename Nat.succ high)) :=
      BProv_context_cons (B := Ax_s) (a := antecedent) hleQ
    have hltHigh : BProv Ax_s C
        (ltTermAt (Term.var 0) (Term.rename Nat.succ high)) :=
      BProv_Ax_s_ltTermAt_of_lt_leTermAt hltLow hleC
    have hstepsC : BProv Ax_s C
        (ordinalCodeStepsTermAt
          (Term.rename Nat.succ sequenceCode)
          (Term.rename Nat.succ sequenceStep)
          (Term.rename Nat.succ high)) :=
      BProv_context_cons (B := Ax_s) (a := antecedent) hstepsQ
    exact BProv_Ax_s_ordinalCodeStepsTermAt_step_of_ltTerm
      hstepsC hltHigh
  have himp : BProv Ax_s Q (imp antecedent consequent) := by
    exact BProv_impI hbody
  simpa [ordinalCodeStepsTermAt, antecedent, consequent] using
    (BProv_allI_of_sentences
      (B := Ax_s) (G := G)
      Ax_s_sentences himp)

def HF_zeroDomainSentence : SetTheory.Form :=
  SetTheory.Form.fAll
    (SetTheory.Form.fImp
      (AckermannHF.HF_emptyAt 0)
      AckermannHF.PAInHF.domainForm)

theorem HF_zeroDomainSentence_sentence :
    SetTheory.Sentence HF_zeroDomainSentence := by
  intro i hi
  simp [HF_zeroDomainSentence,
    AckermannHF.PAInHF.domainForm,
    AckermannHF.HF_ordinalLikeAt,
    AckermannHF.HF_transitiveAt,
    AckermannHF.HF_memTotalOnAt,
    AckermannHF.HF_emptyAt,
    SetTheory.Free] at hi

theorem BProv_HFFin_zeroDomainSentence :
    SetTheory.BProv AckermannHF.HFFinAx_s []
      HF_zeroDomainSentence := by
  apply SetTheory.completeness_inf AckermannHF.HFFinAx_s
  · exact AckermannHF.Sentences_HFFin
  · exact HF_zeroDomainSentence_sentence
  · intro Dom mem v hHF
    let M := AckermannHF.firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
    intro empty hempty
    apply (AckermannHF.HF_ordinalLikeAt_spec
      (SetTheory.scons empty v) 0).mpr
    have hemptyEq : empty = M.empty :=
      (AckermannHF.FirstOrderAdjunctionModel.HF_emptyAt_empty
        M.toFirstOrderAdjunctionModel
        (SetTheory.scons empty v) 0).mp hempty
    rw [hemptyEq]
    exact AckermannHF.FirstOrderAdjunctionModel.ordinalLike_empty
      M.toFirstOrderAdjunctionModel

theorem translateHFFormula_zeroDomainSentence :
    translateHFFormula HF_zeroDomainSentence =
      all (imp (hfEmptyAt 0) codedOrdinalDomain) := by
  rfl

theorem BProv_Ax_s_zeroDomainSentence {G : List Formula} :
    BProv Ax_s G (all (imp (hfEmptyAt 0) codedOrdinalDomain)) := by
  apply BProv_weaken_nil
  have htranslated : BProv translatedHFFinAx []
      (translateHFFormula HF_zeroDomainSentence) :=
    BProv_translateHFFormula_of_BProv_HFFin
      BProv_HFFin_zeroDomainSentence
  have hpa : BProv Ax_s []
      (translateHFFormula HF_zeroDomainSentence) :=
    BProv_lift_translatedHFFinAx_to_PA
      (fun f hf => BProv_Ax_s_of_translatedHFFinAx hf)
      htranslated
  rwa [translateHFFormula_zeroDomainSentence] at hpa

theorem BProv_Ax_s_codedOrdinalDomain_zero
    {G : List Formula} :
    BProv Ax_s G (subst (instTerm Term.zero) codedOrdinalDomain) := by
  have hall : BProv Ax_s G
      (all (imp (hfEmptyAt 0) codedOrdinalDomain)) :=
    BProv_Ax_s_zeroDomainSentence
  have himpRaw := BProv_allE (B := Ax_s) (G := G)
    (t := Term.zero) hall
  have himp : BProv Ax_s G
      (imp
        (hfEmptyTermAt Term.zero)
        (subst (instTerm Term.zero) codedOrdinalDomain)) := by
    simpa [hfEmptyAt, subst_hfEmptyTermAt,
      subst, instTerm, Term.subst, Term.upSubst] using himpRaw
  exact BProv_mp Ax_s G _ _ himp
    (BProv_Ax_s_hfEmptyTermAt_zero)

def HF_domainSuccSentence : SetTheory.Form :=
  SetTheory.Form.fAll (SetTheory.Form.fAll
    (SetTheory.Form.fImp
      (AckermannHF.HF_ordinalLikeAt 1)
      (SetTheory.Form.fImp
        (AckermannHF.HF_succAt 0 1)
        (AckermannHF.HF_ordinalLikeAt 0))))

theorem HF_domainSuccSentence_sentence :
    SetTheory.Sentence HF_domainSuccSentence := by
  intro i hi
  simp [HF_domainSuccSentence,
    AckermannHF.HF_ordinalLikeAt,
    AckermannHF.HF_transitiveAt,
    AckermannHF.HF_memTotalOnAt,
    AckermannHF.HF_succAt,
    AckermannHF.HF_adjoinAt,
    SetTheory.fIff, SetTheory.Free] at hi

theorem BProv_HFFin_domainSuccSentence :
    SetTheory.BProv AckermannHF.HFFinAx_s []
      HF_domainSuccSentence := by
  apply SetTheory.completeness_inf AckermannHF.HFFinAx_s
  · exact AckermannHF.Sentences_HFFin
  · exact HF_domainSuccSentence_sentence
  · intro Dom mem v hHF
    let M := AckermannHF.firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
    intro input output hinput hsucc
    have hinput' : AckermannHF.OrdinalLike M.mem input :=
      (AckermannHF.HF_ordinalLikeAt_spec
        (SetTheory.scons output (SetTheory.scons input v)) 1).mp hinput
    have hsucc' : output = M.adjoin input input :=
      (AckermannHF.FirstOrderAdjunctionModel.HF_succAt_spec
        M.toFirstOrderAdjunctionModel
        (SetTheory.scons output (SetTheory.scons input v)) 0 1).mp hsucc
    apply (AckermannHF.HF_ordinalLikeAt_spec
      (SetTheory.scons output (SetTheory.scons input v)) 0).mpr
    exact AckermannHF.FirstOrderAdjunctionModel.ordinalLike_adjoin_self
      M.toFirstOrderAdjunctionModel hinput' hsucc'

theorem translateHFFormula_domainSuccSentence :
    translateHFFormula HF_domainSuccSentence =
      all (all
        (imp
          (rename Nat.succ codedOrdinalDomain)
          (imp
            (hfAdjoinGraphAt 0 1 1)
            codedOrdinalDomain))) := by
  rfl

theorem BProv_Ax_s_domainSuccSentence {G : List Formula} :
    BProv Ax_s G
      (all (all
        (imp
          (rename Nat.succ codedOrdinalDomain)
          (imp
            (hfAdjoinGraphAt 0 1 1)
            codedOrdinalDomain)))) := by
  apply BProv_weaken_nil
  have htranslated : BProv translatedHFFinAx []
      (translateHFFormula HF_domainSuccSentence) :=
    BProv_translateHFFormula_of_BProv_HFFin
      BProv_HFFin_domainSuccSentence
  have hpa : BProv Ax_s []
      (translateHFFormula HF_domainSuccSentence) :=
    BProv_lift_translatedHFFinAx_to_PA
      (fun f hf => BProv_Ax_s_of_translatedHFFinAx hf)
      htranslated
  rwa [translateHFFormula_domainSuccSentence] at hpa

theorem BProv_Ax_s_codedOrdinalDomain_adjoin_self
    {G : List Formula} {pred current : Term}
    (hpred : BProv Ax_s G
      (subst (instTerm pred) codedOrdinalDomain))
    (hadjoin : BProv Ax_s G
      (hfAdjoinGraphTermAt current pred pred)) :
    BProv Ax_s G
      (subst (instTerm current) codedOrdinalDomain) := by
  have hall : BProv Ax_s G
      (all (all
        (imp
          (rename Nat.succ codedOrdinalDomain)
          (imp
            (hfAdjoinGraphAt 0 1 1)
            codedOrdinalDomain)))) :=
    BProv_Ax_s_domainSuccSentence
  have hpredRaw := BProv_allE (B := Ax_s) (G := G)
    (t := pred) hall
  have hcurrentRaw := BProv_allE (B := Ax_s) (G := G)
    (t := current) hpredRaw
  have hpredNorm :
      subst (instTerm current)
          (subst (Term.upSubst (instTerm pred))
            (rename Nat.succ codedOrdinalDomain)) =
        subst (instTerm pred) codedOrdinalDomain := by
    rw [subst_rename_succ_up, subst_instTerm_rename_succ]
  have hcurrentNorm :
      subst (instTerm current)
          (subst (Term.upSubst (instTerm pred)) codedOrdinalDomain) =
        subst (instTerm current) codedOrdinalDomain := by
    rw [subst_up_inst_codedOrdinalDomain]
  change BProv Ax_s G
    (imp
      (subst (instTerm current)
        (subst (Term.upSubst (instTerm pred))
          (rename Nat.succ codedOrdinalDomain)))
      (imp
        (subst (instTerm current)
          (subst (Term.upSubst (instTerm pred))
            (hfAdjoinGraphAt 0 1 1)))
        (subst (instTerm current)
          (subst (Term.upSubst (instTerm pred))
            codedOrdinalDomain)))) at hcurrentRaw
  rw [hpredNorm, hcurrentNorm] at hcurrentRaw
  have himp : BProv Ax_s G
      (imp
        (subst (instTerm pred) codedOrdinalDomain)
        (imp
          (hfAdjoinGraphTermAt current pred pred)
          (subst (instTerm current) codedOrdinalDomain))) := by
    simpa [hfAdjoinGraphAt, subst_hfAdjoinGraphTermAt,
      subst, instTerm, Term.subst, Term.upSubst,
      Term.subst_rename_succ_up,
      term_subst_instTerm_rename_succ] using hcurrentRaw
  have hstep := BProv_mp Ax_s G _ _ himp hpred
  exact BProv_mp Ax_s G _ _ hstep hadjoin

def ordinalCodePredEdgeTermAt (raw coded : Term) : Formula :=
  ex
    (and
      (ordinalCodeGraphTermAt
        (Term.rename Nat.succ raw) (Term.var 0))
      (hfAdjoinGraphTermAt
        (Term.rename Nat.succ coded) (Term.var 0) (Term.var 0)))

/-- Invert a successor ordinal-code graph into its predecessor graph and
the final Ackermann-adjoin edge. -/
theorem BProv_Ax_s_ordinalCodePredEdgeTermAt_of_succ_graph
    {G : List Formula} {raw coded : Term}
    (hgraph : BProv Ax_s G
      (ordinalCodeGraphTermAt (Term.succ raw) coded)) :
    BProv Ax_s G (ordinalCodePredEdgeTermAt raw coded) := by
  let target : Formula := ordinalCodePredEdgeTermAt raw coded
  refine BProv_Ax_s_ordinalCodeGraphTermAt_elim_opened
    (raw := Term.succ raw) (coded := coded)
    (target := target) hgraph ?_
  let graphBody : Formula :=
    ordinalCodeGraphBodyTermAt
      (Term.var 1) (Term.var 0)
      (Term.rename (fun n ↦ n+2) (Term.succ raw))
      (Term.rename (fun n ↦ n+2) coded)
  let graphInner : Formula := ex graphBody
  let C : List Formula :=
    graphBody ::
      (graphInner :: G.map (rename Nat.succ)).map (rename Nat.succ)
  have hbodyC : BProv Ax_s C graphBody :=
    BProv_ass (B := Ax_s) (G := C) (by simp [C])
  let raw₂ : Term := Term.rename (fun n ↦ n+2) raw
  let coded₂ : Term := Term.rename (fun n ↦ n+2) coded
  have hzeroC : BProv Ax_s C
      (betaTermTermAt Term.zero (Term.var 1) (Term.var 0) Term.zero) := by
    simpa [graphBody, ordinalCodeGraphBodyTermAt,
      Term.rename] using BProv_andE1 hbodyC
  have htailC := BProv_andE2 hbodyC
  have hendC : BProv Ax_s C
      (betaTermTermAt coded₂ (Term.var 1) (Term.var 0)
        (Term.succ raw₂)) := by
    simpa [graphBody, ordinalCodeGraphBodyTermAt,
      raw₂, coded₂, Term.rename] using BProv_andE1 htailC
  have hstepsC : BProv Ax_s C
      (ordinalCodeStepsTermAt
        (Term.var 1) (Term.var 0) (Term.succ raw₂)) := by
    simpa [graphBody, ordinalCodeGraphBodyTermAt,
      raw₂, Term.rename] using BProv_andE2 htailC
  have hltC : BProv Ax_s C (ltTermAt raw₂ (Term.succ raw₂)) :=
    BProv_Ax_s_ltTermAt_self_succ raw₂
  have hstepC : BProv Ax_s C
      (ordinalCodeStepWitnessTermAt (Term.var 1) (Term.var 0) raw₂) :=
    BProv_Ax_s_ordinalCodeStepsTermAt_step_of_ltTerm hstepsC hltC
  let raw₄ : Term := Term.rename (fun n ↦ n+4) raw
  let coded₄ : Term := Term.rename (fun n ↦ n+4) coded
  let stepBody : Formula :=
    and
      (betaTermTermAt (Term.var 1)
        (Term.var 3) (Term.var 2) raw₄)
      (and
        (betaTermTermAt (Term.var 0)
          (Term.var 3) (Term.var 2) (Term.succ raw₄))
        (hfAdjoinGraphTermAt
          (Term.var 0) (Term.var 1) (Term.var 1)))
  let stepInner : Formula := ex stepBody
  have hstepEx : BProv Ax_s C (ex (ex stepBody)) := by
    simpa [ordinalCodeStepWitnessTermAt, stepBody,
      raw₂, raw₄, Term.rename, Term.rename_comp,
      Function.comp_def, Nat.add_assoc] using hstepC
  refine BProv_two_exE_of_sentences
    (B := Ax_s) (G := C) (body := stepBody)
    (target := rename Nat.succ (rename Nat.succ target))
    Ax_s_sentences hstepEx ?_
  let D : List Formula :=
    stepBody ::
      (stepInner :: C.map (rename Nat.succ)).map (rename Nat.succ)
  change BProv Ax_s D
    (rename Nat.succ (rename Nat.succ
      (rename Nat.succ (rename Nat.succ target))))
  have hstepBodyD : BProv Ax_s D stepBody :=
    BProv_ass (B := Ax_s) (G := D) (by simp [D])
  have lift2ToD : ∀ {phi : Formula}, BProv Ax_s C phi →
      BProv Ax_s D (rename Nat.succ (rename Nat.succ phi)) := by
    intro phi hphi
    simpa [D] using
      (BProv_lift_two_contexts_of_sentences
        (B := Ax_s) Ax_s_sentences
        (outer := stepInner) (inner := stepBody) hphi)
  have hzeroDRaw := lift2ToD hzeroC
  have hzeroD : BProv Ax_s D
      (betaTermTermAt Term.zero (Term.var 3) (Term.var 2) Term.zero) := by
    simpa [rename_betaTermTermAt, rename, Term.rename] using hzeroDRaw
  have hendDRaw := lift2ToD hendC
  have hendD : BProv Ax_s D
      (betaTermTermAt coded₄ (Term.var 3) (Term.var 2)
        (Term.succ raw₄)) := by
    simpa [raw₂, coded₂, raw₄, coded₄,
      rename_betaTermTermAt, rename, Term.rename,
      Term.rename_comp, Function.comp_def, Nat.add_assoc] using hendDRaw
  have hstepsDRaw := lift2ToD hstepsC
  have hstepsD : BProv Ax_s D
      (ordinalCodeStepsTermAt
        (Term.var 3) (Term.var 2) (Term.succ raw₄)) := by
    simpa [raw₂, raw₄,
      rename_ordinalCodeStepsTermAt, rename, Term.rename,
      Term.rename_comp, Function.comp_def, Nat.add_assoc] using hstepsDRaw
  have hcurrentD : BProv Ax_s D
      (betaTermTermAt (Term.var 1)
        (Term.var 3) (Term.var 2) raw₄) := by
    simpa [stepBody] using BProv_andE1 hstepBodyD
  have hstepTailD := BProv_andE2 hstepBodyD
  have hnextD : BProv Ax_s D
      (betaTermTermAt (Term.var 0)
        (Term.var 3) (Term.var 2) (Term.succ raw₄)) := by
    simpa [stepBody] using BProv_andE1 hstepTailD
  have hadjoinD : BProv Ax_s D
      (hfAdjoinGraphTermAt
        (Term.var 0) (Term.var 1) (Term.var 1)) := by
    simpa [stepBody] using BProv_andE2 hstepTailD
  have hnextEq : BProv Ax_s D (eq (Term.var 0) coded₄) :=
    BProv_Ax_s_eq_of_betaTermTermAt_betaTermTermAt_same_index
      hendD hnextD
  have hadjoinCodedD : BProv Ax_s D
      (hfAdjoinGraphTermAt
        coded₄ (Term.var 1) (Term.var 1)) :=
    BProv_hfAdjoinGraphTermAt_of_new_eq_term hadjoinD hnextEq
  have hleD : BProv Ax_s D (leTermAt raw₄ (Term.succ raw₄)) :=
    BProv_Ax_s_leTermAt_self_succ raw₄
  have hstepsLowD : BProv Ax_s D
      (ordinalCodeStepsTermAt (Term.var 3) (Term.var 2) raw₄) :=
    BProv_Ax_s_ordinalCodeStepsTermAt_of_leTerm hstepsD hleD
  have hpredGraphD : BProv Ax_s D
      (ordinalCodeGraphTermAt raw₄ (Term.var 1)) :=
    BProv_ordinalCodeGraphTermAt_of_body
      (BProv_andI hzeroD (BProv_andI hcurrentD hstepsLowD))
  have hpairD : BProv Ax_s D
      (and
        (ordinalCodeGraphTermAt raw₄ (Term.var 1))
        (hfAdjoinGraphTermAt coded₄ (Term.var 1) (Term.var 1))) :=
    BProv_andI hpredGraphD hadjoinCodedD
  have hexD : BProv Ax_s D
      (ordinalCodePredEdgeTermAt raw₄ coded₄) := by
    apply BProv_exI (t := Term.var 1)
    simpa [ordinalCodePredEdgeTermAt,
      subst_ordinalCodeGraphTermAt, subst_hfAdjoinGraphTermAt,
      subst, instTerm, Term.subst, Term.upSubst,
      Term.subst_rename_succ_up,
      term_subst_instTerm_rename_succ] using hpairD
  simpa [target, ordinalCodePredEdgeTermAt,
    raw₄, coded₄,
    rename_ordinalCodeGraphTermAt,
    rename_hfAdjoinGraphTermAt,
    rename, Term.rename, Term.rename_comp,
    Function.comp_def, SetTheory.up, Nat.add_assoc] using hexD

/-- Every endpoint of the ordinal-code graph at one fixed raw input lies in
the translated finite-ordinal domain. -/
def ordinalCodeCodomainTermAt (raw : Term) : Formula :=
  all
    (imp
      (ordinalCodeGraphTermAt
        (Term.rename Nat.succ raw) (Term.var 0))
      codedOrdinalDomain)

theorem subst_ordinalCodeCodomainTermAt
    (sigma : Nat → Term) (raw : Term) :
    subst sigma (ordinalCodeCodomainTermAt raw) =
      ordinalCodeCodomainTermAt (Term.subst sigma raw) := by
  have hdomain :
      subst (Term.upSubst sigma) codedOrdinalDomain =
        codedOrdinalDomain := by
    calc
      subst (Term.upSubst sigma) codedOrdinalDomain =
          subst (fun n : Nat => Term.var n) codedOrdinalDomain := by
        apply subst_ext_free
        intro n hn
        have hn0 := codedOrdinalDomain_free hn
        subst n
        rfl
      _ = codedOrdinalDomain := subst_id codedOrdinalDomain
  simp [ordinalCodeCodomainTermAt,
    subst_ordinalCodeGraphTermAt, subst,
    Term.subst, Term.upSubst,
    Term.subst_rename_succ_up, hdomain]

theorem rename_ordinalCodeCodomainTermAt
    (r : Nat → Nat) (raw : Term) :
    rename r (ordinalCodeCodomainTermAt raw) =
      ordinalCodeCodomainTermAt (Term.rename r raw) := by
  rw [← subst_var_rename,
    subst_ordinalCodeCodomainTermAt]
  simp only [term_subst_var_rename]

theorem BProv_Ax_s_ordinalCodeCodomainTermAt_zero
    {G : List Formula} :
    BProv Ax_s G
      (ordinalCodeCodomainTermAt Term.zero) := by
  let graph : Formula :=
    ordinalCodeGraphTermAt Term.zero (Term.var 0)
  let Q : List Formula := G.map (rename Nat.succ)
  have hbody : BProv Ax_s Q
      (imp graph codedOrdinalDomain) := by
    let C : List Formula := graph :: Q
    have hgraph : BProv Ax_s C graph :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C, graph])
    have hzero : BProv Ax_s C
        (ordinalCodeGraphTermAt Term.zero Term.zero) :=
      BProv_Ax_s_ordinalCodeGraphTermAt_zero
    have heq : BProv Ax_s C
        (eq Term.zero (Term.var 0)) :=
      BProv_Ax_s_ordinalCodeGraphTermAt_functional hzero hgraph
    have hdomainZero : BProv Ax_s C
        (subst (instTerm Term.zero) codedOrdinalDomain) :=
      BProv_Ax_s_codedOrdinalDomain_zero
    have hdomainRaw := BProv_eqElim
      (B := Ax_s) (G := C)
      (a := codedOrdinalDomain) heq hdomainZero
    have hdomain : BProv Ax_s C codedOrdinalDomain := by
      simpa only [subst_instTerm_var_zero_codedOrdinalDomain]
        using hdomainRaw
    simpa [C, graph] using BProv_impI hdomain
  simpa [ordinalCodeCodomainTermAt, graph,
    Term.rename] using
    (BProv_allI_of_sentences
      (B := Ax_s) (G := G)
      Ax_s_sentences hbody)

theorem subst_instTerm_var_one_codedOrdinalDomain :
    subst (instTerm (Term.var 1)) codedOrdinalDomain =
      rename Nat.succ codedOrdinalDomain := by
  rw [subst_instTerm_var]
  apply rename_ext_free
  intro n hn
  have hn0 := codedOrdinalDomain_free hn
  subst n
  rfl

theorem BProv_Ax_s_ordinalCodeCodomainTermAt_succ
    {G : List Formula} {raw : Term}
    (hih : BProv Ax_s G
      (ordinalCodeCodomainTermAt raw)) :
    BProv Ax_s G
      (ordinalCodeCodomainTermAt (Term.succ raw)) := by
  let raw₁ : Term := Term.rename Nat.succ raw
  let graph : Formula :=
    ordinalCodeGraphTermAt (Term.succ raw₁) (Term.var 0)
  let Q : List Formula := G.map (rename Nat.succ)
  have hihRaw := BProv_rename_of_sentences
    (B := Ax_s) Ax_s_sentences
    hih Nat.succ
  have hihQ : BProv Ax_s Q
      (ordinalCodeCodomainTermAt raw₁) := by
    simpa [Q, raw₁, rename_ordinalCodeCodomainTermAt]
      using hihRaw
  have hbody : BProv Ax_s Q (imp graph codedOrdinalDomain) := by
    let C : List Formula := graph :: Q
    have hgraph : BProv Ax_s C graph :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C, graph])
    have hedge : BProv Ax_s C
        (ordinalCodePredEdgeTermAt raw₁ (Term.var 0)) :=
      BProv_Ax_s_ordinalCodePredEdgeTermAt_of_succ_graph
        (by simpa [graph] using hgraph)
    let raw₂ : Term := Term.rename Nat.succ raw₁
    let edgeBody : Formula :=
      and
        (ordinalCodeGraphTermAt raw₂ (Term.var 0))
        (hfAdjoinGraphTermAt
          (Term.var 1) (Term.var 0) (Term.var 0))
    let D : List Formula := edgeBody :: C.map (rename Nat.succ)
    have hopened : BProv Ax_s D
        (rename Nat.succ codedOrdinalDomain) := by
      have hedgeBody : BProv Ax_s D edgeBody :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D])
      have hpred : BProv Ax_s D
          (ordinalCodeGraphTermAt raw₂ (Term.var 0)) := by
        simpa [edgeBody] using BProv_andE1 hedgeBody
      have hadjoin : BProv Ax_s D
          (hfAdjoinGraphTermAt
            (Term.var 1) (Term.var 0) (Term.var 0)) := by
        simpa [edgeBody] using BProv_andE2 hedgeBody
      have hihRen := BProv_rename_of_sentences
        (B := Ax_s) Ax_s_sentences
        hihQ Nat.succ
      have hihD₀ := BProv_context_prefix
        (B := Ax_s) [edgeBody, rename Nat.succ graph] hihRen
      have hihD : BProv Ax_s D
          (ordinalCodeCodomainTermAt raw₂) := by
        simpa [D, C, Q, raw₁, raw₂,
          rename_ordinalCodeCodomainTermAt,
          List.map_map, Function.comp_def, Term.rename_comp,
          Nat.add_assoc] using hihD₀
      have himpRaw := BProv_allE
        (B := Ax_s) (G := D) (t := Term.var 0) hihD
      have himp : BProv Ax_s D
          (imp
            (ordinalCodeGraphTermAt raw₂ (Term.var 0))
            codedOrdinalDomain) := by
        simpa [ordinalCodeCodomainTermAt,
          subst_ordinalCodeGraphTermAt,
          subst_instTerm_var_zero_codedOrdinalDomain,
          subst, instTerm, Term.subst,
          term_subst_instTerm_rename_succ] using himpRaw
      have hpredDomain : BProv Ax_s D codedOrdinalDomain :=
        BProv_mp Ax_s D _ _ himp hpred
      have hcurrentDomain :=
        BProv_Ax_s_codedOrdinalDomain_adjoin_self
          (pred := Term.var 0) (current := Term.var 1)
          (by simpa only [subst_instTerm_var_zero_codedOrdinalDomain]
            using hpredDomain)
          hadjoin
      simpa only [subst_instTerm_var_one_codedOrdinalDomain]
        using hcurrentDomain
    have hdomain : BProv Ax_s C codedOrdinalDomain :=
      BProv_exE_of_sentences
        (B := Ax_s) Ax_s_sentences
        (G := C) (a := edgeBody) (c := codedOrdinalDomain)
        (by simpa [ordinalCodePredEdgeTermAt,
            edgeBody, raw₁, raw₂, Term.rename] using hedge)
        (by simpa [D] using hopened)
    simpa [C, graph] using BProv_impI hdomain
  simpa [ordinalCodeCodomainTermAt, graph, raw₁,
    Term.rename] using
    (BProv_allI_of_sentences
      (B := Ax_s) (G := G)
      Ax_s_sentences hbody)

/-- PA induction over the raw input proves codomain safety uniformly in the
graph output. -/
theorem BProv_Ax_s_all_ordinalCodeCodomain {G : List Formula} :
    BProv Ax_s G
      (all
        (ordinalCodeCodomainTermAt (Term.var 0))) := by
  apply BProv_weaken_nil
  let phi : Formula :=
    ordinalCodeCodomainTermAt (Term.var 0)
  have hzero : BProv Ax_s [] (subst substZero phi) := by
    have hbase :=
      BProv_Ax_s_ordinalCodeCodomainTermAt_zero (G := [])
    simpa [phi, subst_ordinalCodeCodomainTermAt,
      substZero, Term.subst] using hbase
  have hsuccImp : BProv Ax_s []
      (imp phi (subst substSuccVar phi)) := by
    let C : List Formula := [phi]
    have hih : BProv Ax_s C phi :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hnext : BProv Ax_s C
        (ordinalCodeCodomainTermAt
          (Term.succ (Term.var 0))) :=
      BProv_Ax_s_ordinalCodeCodomainTermAt_succ hih
    have hnextSub : BProv Ax_s C (subst substSuccVar phi) := by
      simpa [phi, subst_ordinalCodeCodomainTermAt,
        substSuccVar, Term.subst] using hnext
    simpa [C] using BProv_impI hnextSub
  have hsucc : BProv Ax_s []
      (all (imp phi (subst substSuccVar phi))) :=
    BProv_allI_of_sentences
      (B := Ax_s) (G := [])
      Ax_s_sentences hsuccImp
  simpa [phi] using BProv_Ax_s_induction_rule hzero hsucc

theorem rename_subst_instTerm_codedOrdinalDomain
    (coded : Term) :
    rename Nat.succ
        (subst (instTerm coded) codedOrdinalDomain) =
      subst (instTerm (Term.rename Nat.succ coded))
        codedOrdinalDomain := by
  rw [rename_subst]
  apply subst_ext_free
  intro n hn
  have hn0 := codedOrdinalDomain_free hn
  subst n
  rfl

/-- Exact proof of the remaining graph-codomain field: every beta-coded
ordinal trace ends at an ordinal-like Ackermann code. -/
theorem ordinalCodeGraphCodomain :
    OrdinalCodeGraphCodomain := by
  intro G coded hrange
  let graph : Formula :=
    ordinalCodeGraphTermAt
      (Term.var 0) (Term.rename Nat.succ coded)
  let C : List Formula := graph :: G.map (rename Nat.succ)
  have hinner : BProv Ax_s C
      (rename Nat.succ
        (subst (instTerm coded) codedOrdinalDomain)) := by
    have hall : BProv Ax_s C
        (all
          (ordinalCodeCodomainTermAt (Term.var 0))) :=
      BProv_Ax_s_all_ordinalCodeCodomain
    have hrawPoint := BProv_allE
      (B := Ax_s) (G := C) (t := Term.var 0) hall
    have hpoint : BProv Ax_s C
        (ordinalCodeCodomainTermAt (Term.var 0)) := by
      rw [subst_ordinalCodeCodomainTermAt] at hrawPoint
      simpa [instTerm, Term.subst] using hrawPoint
    have himpRaw := BProv_allE
      (B := Ax_s) (G := C)
      (t := Term.rename Nat.succ coded) hpoint
    have himp : BProv Ax_s C
        (imp graph
          (subst (instTerm (Term.rename Nat.succ coded))
            codedOrdinalDomain)) := by
      simpa [ordinalCodeCodomainTermAt, graph,
        subst_ordinalCodeGraphTermAt,
        subst, instTerm, Term.subst,
        term_subst_instTerm_rename_succ] using himpRaw
    have hgraph : BProv Ax_s C graph :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C, graph])
    have hdomain := BProv_mp Ax_s C _ _ himp hgraph
    simpa only [rename_subst_instTerm_codedOrdinalDomain]
      using hdomain
  exact BProv_exE_of_sentences
    (B := Ax_s) Ax_s_sentences
    (G := G) (a := graph)
    (c := subst (instTerm coded) codedOrdinalDomain)
    (by simpa [ordinalCodeGraphRangeExistsTermAt, graph] using hrange)
    (by simpa [C] using hinner)

/-- Totality, predecessor inversion, and the two functionality theorems make
the ordinal-code graph closed under its Ackermann successor recurrence. -/
theorem ordinalCodeGraphSuccClosure :
    OrdinalCodeGraphSuccClosure := by
  intro G raw pred current hpred hadjoin
  let target : Formula :=
    ordinalCodeGraphTermAt (Term.succ raw) current
  let outGraph : Formula :=
    ordinalCodeGraphTermAt
      (Term.succ (Term.rename Nat.succ raw)) (Term.var 0)
  have htotal : BProv Ax_s G (ex outGraph) := by
    simpa [outGraph, Term.rename] using
      (OrdinalCodeGraphProofs_total G (Term.succ raw))
  let C : List Formula := outGraph :: G.map (rename Nat.succ)
  have hinner : BProv Ax_s C (rename Nat.succ target) := by
    have hout : BProv Ax_s C outGraph :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    let raw₁ : Term := Term.rename Nat.succ raw
    have hedge : BProv Ax_s C
        (ordinalCodePredEdgeTermAt raw₁ (Term.var 0)) :=
      BProv_Ax_s_ordinalCodePredEdgeTermAt_of_succ_graph
        (by simpa [outGraph, raw₁] using hout)
    let raw₂ : Term := Term.rename Nat.succ raw₁
    let pred₂ : Term := Term.rename (fun n ↦ n+2) pred
    let current₂ : Term := Term.rename (fun n ↦ n+2) current
    let edgeBody : Formula :=
      and
        (ordinalCodeGraphTermAt raw₂ (Term.var 0))
        (hfAdjoinGraphTermAt
          (Term.var 1) (Term.var 0) (Term.var 0))
    let D : List Formula := edgeBody :: C.map (rename Nat.succ)
    have hopened : BProv Ax_s D
        (rename Nat.succ (rename Nat.succ target)) := by
      have hedgeBody : BProv Ax_s D edgeBody :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D])
      have hedgePred : BProv Ax_s D
          (ordinalCodeGraphTermAt raw₂ (Term.var 0)) := by
        simpa [edgeBody] using BProv_andE1 hedgeBody
      have hedgeAdjoin : BProv Ax_s D
          (hfAdjoinGraphTermAt
            (Term.var 1) (Term.var 0) (Term.var 0)) := by
        simpa [edgeBody] using BProv_andE2 hedgeBody
      have lift2 : ∀ {phi : Formula}, BProv Ax_s G phi →
          BProv Ax_s D
            (rename Nat.succ (rename Nat.succ phi)) := by
        intro phi hphi
        simpa [D, C] using
          (BProv_lift_two_contexts_of_sentences
            (B := Ax_s) Ax_s_sentences
            (outer := outGraph) (inner := edgeBody) hphi)
      have hpredD : BProv Ax_s D
          (ordinalCodeGraphTermAt raw₂ pred₂) := by
        have hraw := lift2 hpred
        simpa [raw₁, raw₂, pred₂,
          rename_ordinalCodeGraphTermAt,
          Term.rename, Term.rename_comp,
          Function.comp_def, Nat.add_assoc] using hraw
      have hadjoinD : BProv Ax_s D
          (hfAdjoinGraphTermAt current₂ pred₂ pred₂) := by
        have hraw := lift2 hadjoin
        simpa [pred₂, current₂,
          rename_hfAdjoinGraphTermAt,
          Term.rename, Term.rename_comp,
          Function.comp_def, Nat.add_assoc] using hraw
      have houtD₀ := BProv_rename_succ_context_cons_of_sentences
        (B := Ax_s) Ax_s_sentences
        (a := edgeBody) hout
      have houtD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.succ raw₂) (Term.var 1)) := by
        simpa [D, C, outGraph, raw₁, raw₂,
          rename_ordinalCodeGraphTermAt,
          Term.rename, Term.rename_comp,
          Function.comp_def, Nat.add_assoc] using houtD₀
      have hpredEq : BProv Ax_s D
          (eq pred₂ (Term.var 0)) :=
        BProv_Ax_s_ordinalCodeGraphTermAt_functional
          hpredD hedgePred
      have hedgeAdjoin' : BProv Ax_s D
          (hfAdjoinGraphTermAt
            (Term.var 1) pred₂ pred₂) :=
        BProv_Ax_s_hfAdjoinGraphTermAt_congr_inputs
          (BProv_eqSym hpredEq) (BProv_eqSym hpredEq)
          hedgeAdjoin
      have houtEq : BProv Ax_s D
          (eq (Term.var 1) current₂) :=
        BProv_Ax_s_hfAdjoinGraphTermAt_functional
          hedgeAdjoin' hadjoinD
      have hresult : BProv Ax_s D
          (ordinalCodeGraphTermAt (Term.succ raw₂) current₂) :=
        BProv_ordinalCodeGraphTermAt_congr_coded houtEq houtD
      simpa [target, raw₁, raw₂, current₂,
        rename_ordinalCodeGraphTermAt,
        Term.rename, Term.rename_comp,
        Function.comp_def, Nat.add_assoc] using hresult
    exact BProv_exE_of_sentences
      (B := Ax_s) Ax_s_sentences
      (G := C) (a := edgeBody) (c := rename Nat.succ target)
      (by simpa [ordinalCodePredEdgeTermAt,
          edgeBody, raw₁, raw₂, Term.rename] using hedge)
      (by simpa [D] using hopened)
  exact BProv_exE_of_sentences
    (B := Ax_s) Ax_s_sentences
    (G := G) (a := outGraph) (c := target)
    htotal (by simpa [C] using hinner)

/-- The ordinal-code graph has exactly the translated finite ordinals as its
range.  Both local range obligations are now concrete PA theorems. -/
theorem BProv_Ax_s_ordinalCodeGraph_range_exact :
    ∀ (G : List Formula) (coded : Term),
      BProv Ax_s G
        (iffForm
          (subst (instTerm coded) codedOrdinalDomain)
          (ex (ordinalCodeGraphTermAt
            (Term.var 0) (Term.rename Nat.succ coded)))) :=
  OrdinalCodeGraphProofs_range_of_succ_codomain
    ordinalCodeGraphSuccClosure ordinalCodeGraphCodomain

/-- Functionality is exactly sufficient for the variable constructor of the
 ordinal-code term-graph induction. -/
theorem BProv_Ax_s_term_graph_var
    (hfunctional : OrdinalCodeGraphFunctional)
    (G : List Formula) (n : Nat)
    (rawMap codedMap : Nat → Nat) (codedOut : Nat)
    (hcode : ∀ k, Term.Free k (Term.var n) →
      BProv Ax_s G
        (ordinalCodeGraphAt (rawMap k) (codedMap k))) :
    BProv Ax_s G
      (iffForm
        (compositeTermGraphAt codedOut codedMap (Term.var n))
        (ordinalCodeGraphTermAt
          (Term.rename rawMap (Term.var n)) (Term.var codedOut))) := by
  have hinput : BProv Ax_s G
      (ordinalCodeGraphTermAt
        (Term.var (rawMap n)) (Term.var (codedMap n))) := by
    simpa [ordinalCodeGraphAt] using hcode n rfl
  have hforward : BProv Ax_s G
      (imp
        (eq (Term.var codedOut) (Term.var (codedMap n)))
        (ordinalCodeGraphTermAt
          (Term.var (rawMap n)) (Term.var codedOut))) := by
    apply BProv_impI
    let C : List Formula :=
      eq (Term.var codedOut) (Term.var (codedMap n)) :: G
    have heq : BProv Ax_s C
        (eq (Term.var codedOut) (Term.var (codedMap n))) :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hinputC : BProv Ax_s C
        (ordinalCodeGraphTermAt
          (Term.var (rawMap n)) (Term.var (codedMap n))) :=
      BProv_context_cons hinput
    exact BProv_ordinalCodeGraphTermAt_congr_coded
      (BProv_eqSym heq) hinputC
  have hreverse : BProv Ax_s G
      (imp
        (ordinalCodeGraphTermAt
          (Term.var (rawMap n)) (Term.var codedOut))
        (eq (Term.var codedOut) (Term.var (codedMap n)))) := by
    apply BProv_impI
    let C : List Formula :=
      ordinalCodeGraphTermAt
        (Term.var (rawMap n)) (Term.var codedOut) :: G
    have hout : BProv Ax_s C
        (ordinalCodeGraphTermAt
          (Term.var (rawMap n)) (Term.var codedOut)) :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hinputC : BProv Ax_s C
        (ordinalCodeGraphTermAt
          (Term.var (rawMap n)) (Term.var (codedMap n))) :=
      BProv_context_cons hinput
    exact BProv_eqSym (hfunctional hinputC hout)
  have hiff : BProv Ax_s G
      (iffForm
        (eq (Term.var codedOut) (Term.var (codedMap n)))
        (ordinalCodeGraphTermAt
          (Term.var (rawMap n)) (Term.var codedOut))) :=
    BProv_andI hforward hreverse
  simpa [compositeTermGraphAt, codedTermSlotMap,
    AckermannHF.PAInHF.termGraphAt, hfFormulaAt, Term.rename] using hiff

/-- Reverse translation of a successor term exposes exactly one fresh
intermediate slot for the translated operand, followed by HF adjunction of
that operand to itself. -/
theorem compositeTermGraphAt_succ
    (codedOut : Nat) (codedMap : Nat → Nat) (t : Term) :
    compositeTermGraphAt codedOut codedMap (Term.succ t) =
      ex (and
        (compositeTermGraphAt 0 (fun n ↦ codedMap n + 1) t)
        (hfAdjoinGraphAt (codedOut + 1) 0 0)) := by
  have hterm :
      hfFormulaAt (hfUpVarMap (codedTermSlotMap codedOut codedMap))
          (AckermannHF.PAInHF.termGraphAt (fun n ↦ n + 2) 0 t) =
        compositeTermGraphAt 0 (fun n ↦ codedMap n + 1) t := by
    let graph : SetTheory.Form :=
      AckermannHF.PAInHF.termGraphAt (fun n ↦ n + 1) 0 t
    have hgraph : SetTheory.rename (SetTheory.up Nat.succ) graph =
        AckermannHF.PAInHF.termGraphAt (fun n ↦ n + 2) 0 t := by
      simpa [graph, SetTheory.up] using
        (AckermannHF.PAInHF.termGraphAt_rename t
          (ρ := fun n ↦ n + 1) (out := 0)
          (r := SetTheory.up Nat.succ))
    rw [← hgraph]
    rw [hfFormulaAt_source_rename]
    apply hfFormulaAt_ext
    intro n
    cases n <;> rfl
  have hsucc :
      hfFormulaAt (hfUpVarMap (codedTermSlotMap codedOut codedMap))
          (AckermannHF.HF_succAt 1 0) =
        hfAdjoinGraphAt (codedOut + 1) 0 0 := by
    rfl
  simp [compositeTermGraphAt,
    AckermannHF.PAInHF.termGraphAt,
    hfFormulaAt, hterm, hsucc]

/-- Successor closure, graph functionality, and unconditional HF-adjoin
totality strengthen the one-way graph recurrence to the exact equivalence
needed by the successor term constructor. -/
theorem BProv_Ax_s_hfAdjoinGraphTermAt_iff_ordinalCodeGraphTermAt_succ
    (hsucc : OrdinalCodeGraphSuccClosure)
    (hfunctional : OrdinalCodeGraphFunctional)
    {G : List Formula} {raw pred codedOut : Term}
    (hpred : BProv Ax_s G (ordinalCodeGraphTermAt raw pred)) :
    BProv Ax_s G
      (iffForm
        (hfAdjoinGraphTermAt codedOut pred pred)
        (ordinalCodeGraphTermAt (Term.succ raw) codedOut)) := by
  have hforward : BProv Ax_s G
      (imp
        (hfAdjoinGraphTermAt codedOut pred pred)
        (ordinalCodeGraphTermAt (Term.succ raw) codedOut)) := by
    apply BProv_impI
    let C : List Formula :=
      hfAdjoinGraphTermAt codedOut pred pred :: G
    have hadjoin : BProv Ax_s C
        (hfAdjoinGraphTermAt codedOut pred pred) :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hpredC : BProv Ax_s C
        (ordinalCodeGraphTermAt raw pred) :=
      BProv_context_cons (B := Ax_s) hpred
    exact hsucc hpredC hadjoin
  have hreverse : BProv Ax_s G
      (imp
        (ordinalCodeGraphTermAt (Term.succ raw) codedOut)
        (hfAdjoinGraphTermAt codedOut pred pred)) := by
    apply BProv_impI
    let C : List Formula :=
      ordinalCodeGraphTermAt (Term.succ raw) codedOut :: G
    have htarget : BProv Ax_s C
        (ordinalCodeGraphTermAt (Term.succ raw) codedOut) :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hpredC : BProv Ax_s C
        (ordinalCodeGraphTermAt raw pred) :=
      BProv_context_cons (B := Ax_s) hpred
    have hall : BProv Ax_s C
        (all (hfAdjoinTotalTermAt (Term.var 0))) := by
      have hbase := BProv_Ax_s_all_hfAdjoinTotalAt_of_zero_succ
        BProv_Ax_s_hfAdjoinTotalTermAt_zero
        BProv_Ax_s_hfAdjoinTotalTermAt_succ
      simpa [hfAdjoinTotalTermAt_var] using
        (BProv_weaken_nil (G := C) hbase)
    have htotal : BProv Ax_s C (hfAdjoinTotalTermAt pred) :=
      BProv_hfAdjoinTotalTermAt_of_all hall
    have hex : BProv Ax_s C (hfAdjoinExistsTermAt pred pred) :=
      BProv_hfAdjoinExistsTermAt_of_total htotal
    let body : Formula :=
      hfAdjoinGraphTermAt
        (Term.var 0) (Term.rename Nat.succ pred)
        (Term.rename Nat.succ pred)
    let D : List Formula := body :: C.map (rename Nat.succ)
    have hinner : BProv Ax_s D
        (rename Nat.succ
          (hfAdjoinGraphTermAt codedOut pred pred)) := by
      have hadjoin : BProv Ax_s D body :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D])
      have hpredD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.rename Nat.succ raw)
            (Term.rename Nat.succ pred)) := by
        have hren := BProv_rename_succ_context_cons_of_sentences
          (B := Ax_s) Ax_s_sentences
          (a := body) hpredC
        simpa [D, C, rename_ordinalCodeGraphTermAt] using hren
      have hnew : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.succ (Term.rename Nat.succ raw))
            (Term.var 0)) :=
        hsucc hpredD hadjoin
      have htargetD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.succ (Term.rename Nat.succ raw))
            (Term.rename Nat.succ codedOut)) := by
        have hren := BProv_rename_succ_context_cons_of_sentences
          (B := Ax_s) Ax_s_sentences
          (a := body) htarget
        simpa [D, C, rename_ordinalCodeGraphTermAt,
          Term.rename] using hren
      have heq : BProv Ax_s D
          (eq (Term.var 0) (Term.rename Nat.succ codedOut)) :=
        hfunctional hnew htargetD
      have htransport :=
        BProv_hfAdjoinGraphTermAt_of_new_eq_term hadjoin heq
      simpa [body, rename_hfAdjoinGraphTermAt_succ]
        using htransport
    exact BProv_exE_of_sentences
      (B := Ax_s) Ax_s_sentences
      (G := C) (a := body)
      (c := hfAdjoinGraphTermAt codedOut pred pred)
      (by simpa [hfAdjoinExistsTermAt, body] using hex)
      (by simpa [D] using hinner)
  exact BProv_iffForm_intro hforward hreverse

/-- Complete ordinal-code term-graph induction property for one PA term.
Constructor laws consume this polymorphic property, so recursive hypotheses
remain available after opening fresh intermediate-output binders. -/
def OrdinalCodeTermGraphProof (t : Term) : Prop :=
  ∀ (G : List Formula) (rawMap codedMap : Nat → Nat) (codedOut : Nat),
    (∀ n, Term.Free n t →
      BProv Ax_s G
        (ordinalCodeGraphAt (rawMap n) (codedMap n))) →
    BProv Ax_s G
      (iffForm
        (compositeTermGraphAt codedOut codedMap t)
        (ordinalCodeGraphTermAt
          (Term.rename rawMap t) (Term.var codedOut)))

/-- Operation-facing interface for the remaining term-graph proof.  Recursive
constructors consume the complete graph property of each operand instead of a
premature specialization to one output slot. -/
structure OrdinalCodeTermCompatibilityProofs where
  graph_functional : OrdinalCodeGraphFunctional
  zero_compatible : OrdinalCodeTermGraphProof Term.zero
  succ_compatible : ∀ t,
    OrdinalCodeTermGraphProof t →
    OrdinalCodeTermGraphProof (Term.succ t)
  add_compatible : ∀ a b,
    OrdinalCodeTermGraphProof a →
    OrdinalCodeTermGraphProof b →
    OrdinalCodeTermGraphProof (Term.add a b)
  mul_compatible : ∀ a b,
    OrdinalCodeTermGraphProof a →
    OrdinalCodeTermGraphProof b →
    OrdinalCodeTermGraphProof (Term.mul a b)

/-- Exact zero-constructor field of `OrdinalCodeTermCompatibilityProofs`.
The reverse-translated composite is the HF-empty predicate, which is
equivalent to the unique ordinal-code graph endpoint at raw zero. -/
theorem OrdinalCodeTermCompatibilityProofs_zero_compatible :
    ∀ (G : List Formula) (codedMap : Nat → Nat) (codedOut : Nat),
      BProv Ax_s G
        (iffForm
          (compositeTermGraphAt codedOut codedMap Term.zero)
          (ordinalCodeGraphTermAt Term.zero (Term.var codedOut))) := by
  intro G codedMap codedOut
  have hnormal :
      compositeTermGraphAt codedOut codedMap Term.zero =
        hfEmptyAt codedOut := by
    simp [compositeTermGraphAt, codedTermSlotMap,
      AckermannHF.PAInHF.termGraphAt,
      AckermannHF.HF_emptyAt, hfFormulaAt, hfUpVarMap,
      hfEmptyAt, hfEmptyTermAt, hfMemTermAt_var,
      Term.rename]
  rw [hnormal]
  have hforward : BProv Ax_s G
      (imp
        (hfEmptyAt codedOut)
        (ordinalCodeGraphTermAt Term.zero (Term.var codedOut))) := by
    let C : List Formula := hfEmptyAt codedOut :: G
    have hempty : BProv Ax_s C (hfEmptyAt codedOut) :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have heq : BProv Ax_s C
        (eq (Term.var codedOut) Term.zero) :=
      BProv_Ax_s_eq_zero_of_hfEmptyAt hempty
    have hzero : BProv Ax_s C
        (ordinalCodeGraphTermAt Term.zero Term.zero) :=
      BProv_Ax_s_ordinalCodeGraphTermAt_zero
    have hgraph : BProv Ax_s C
        (ordinalCodeGraphTermAt Term.zero (Term.var codedOut)) :=
      BProv_ordinalCodeGraphTermAt_congr_coded
        (BProv_eqSym heq) hzero
    simpa [C] using BProv_impI hgraph
  have hreverse : BProv Ax_s G
      (imp
        (ordinalCodeGraphTermAt Term.zero (Term.var codedOut))
        (hfEmptyAt codedOut)) := by
    let C : List Formula :=
      ordinalCodeGraphTermAt Term.zero (Term.var codedOut) :: G
    have hgraph : BProv Ax_s C
        (ordinalCodeGraphTermAt Term.zero (Term.var codedOut)) :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have heq : BProv Ax_s C
        (eq (Term.var codedOut) Term.zero) :=
      BProv_Ax_s_eq_zero_of_ordinalCodeGraphTermAt_zero hgraph
    have hzero : BProv Ax_s C (eqConstAt codedOut 0) := by
      simpa [eqConstAt, Term.numeral] using heq
    have hempty : BProv Ax_s C (hfEmptyAt codedOut) :=
      BProv_Ax_s_hfEmptyAt_of_eqConst_zero hzero
    simpa [C] using BProv_impI hempty
  exact BProv_iffForm_intro hforward hreverse

/-- The normalized zero theorem supplies the complete induction property;
raw-variable data are vacuous because zero has no free variables. -/
theorem OrdinalCodeTermGraphProof_zero :
    OrdinalCodeTermGraphProof Term.zero := by
  intro G rawMap codedMap codedOut hcode
  exact OrdinalCodeTermCompatibilityProofs_zero_compatible
    G codedMap codedOut

/-- Successor compatibility after the recursive operand theorem has been
instantiated at the fresh output slot introduced by the translated successor
graph. -/
theorem BProv_Ax_s_term_graph_succ_of_shifted_operand
    (hsucc : OrdinalCodeGraphSuccClosure)
    (G : List Formula) (t : Term)
    (rawMap codedMap : Nat → Nat) (codedOut : Nat)
    (hoperand : BProv Ax_s (G.map (rename Nat.succ))
      (iffForm
        (compositeTermGraphAt 0 (fun n ↦ codedMap n + 1) t)
        (ordinalCodeGraphTermAt
          (Term.rename Nat.succ (Term.rename rawMap t))
          (Term.var 0)))) :
    BProv Ax_s G
      (iffForm
        (compositeTermGraphAt codedOut codedMap (Term.succ t))
        (ordinalCodeGraphTermAt
          (Term.rename rawMap (Term.succ t))
          (Term.var codedOut))) := by
  let raw : Term := Term.rename rawMap t
  let composite : Formula :=
    compositeTermGraphAt codedOut codedMap (Term.succ t)
  let target : Formula :=
    ordinalCodeGraphTermAt (Term.succ raw) (Term.var codedOut)
  let operandComposite : Formula :=
    compositeTermGraphAt 0 (fun n ↦ codedMap n + 1) t
  let operandGraph : Formula :=
    ordinalCodeGraphTermAt
      (Term.rename Nat.succ raw) (Term.var 0)
  let adjoinGraph : Formula :=
    hfAdjoinGraphAt (codedOut + 1) 0 0
  let body : Formula := and operandComposite adjoinGraph
  have hforward : BProv Ax_s G (imp composite target) := by
    apply BProv_impI
    let C : List Formula := composite :: G
    have hcomposite : BProv Ax_s C composite :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hex : BProv Ax_s C (ex body) := by
      simpa [composite, body, operandComposite, adjoinGraph,
        compositeTermGraphAt_succ] using hcomposite
    let D : List Formula := body :: C.map (rename Nat.succ)
    have hinner : BProv Ax_s D (rename Nat.succ target) := by
      have hbody : BProv Ax_s D body :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D])
      have hoperandComposite : BProv Ax_s D operandComposite :=
        BProv_andE1 hbody
      have hadjoin : BProv Ax_s D adjoinGraph :=
        BProv_andE2 hbody
      have hoperandD : BProv Ax_s D
          (iffForm operandComposite operandGraph) := by
        have hctx := BProv_context_cons (B := Ax_s)
          (a := rename Nat.succ composite) hoperand
        have hctx' := BProv_context_cons (B := Ax_s)
          (a := body) hctx
        simpa [D, C, raw, operandComposite, operandGraph]
          using hctx'
      have hoperandForward : BProv Ax_s D
          (imp operandComposite operandGraph) := by
        simpa [iffForm] using BProv_andE1 hoperandD
      have hgraph : BProv Ax_s D operandGraph :=
        BProv_mp Ax_s D _ _ hoperandForward hoperandComposite
      have hstep :=
        BProv_Ax_s_hfAdjoinGraphTermAt_iff_ordinalCodeGraphTermAt_succ
          hsucc ordinalCodeGraphFunctional
          (codedOut := Term.var (codedOut + 1)) hgraph
      have hstepForward : BProv Ax_s D
          (imp adjoinGraph
            (ordinalCodeGraphTermAt
              (Term.succ (Term.rename Nat.succ raw))
              (Term.var (codedOut + 1)))) := by
        simpa [iffForm, operandGraph, adjoinGraph,
          hfAdjoinGraphAt] using BProv_andE1 hstep
      have hnext := BProv_mp Ax_s D _ _ hstepForward hadjoin
      simpa [target, raw, rename_ordinalCodeGraphTermAt,
        Term.rename] using hnext
    exact BProv_exE_of_sentences
      (B := Ax_s) Ax_s_sentences
      (G := C) (a := body) (c := target)
      hex (by simpa [D] using hinner)
  have hreverse : BProv Ax_s G (imp target composite) := by
    apply BProv_impI
    let C : List Formula := target :: G
    have htarget : BProv Ax_s C target :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have htotal : BProv Ax_s C (ex operandGraph) := by
      simpa [operandGraph, raw] using
        (OrdinalCodeGraphProofs_total C raw)
    let D : List Formula := operandGraph :: C.map (rename Nat.succ)
    have hinner : BProv Ax_s D (rename Nat.succ composite) := by
      have hgraph : BProv Ax_s D operandGraph :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D])
      have hoperandD : BProv Ax_s D
          (iffForm operandComposite operandGraph) := by
        have hctx := BProv_context_cons (B := Ax_s)
          (a := rename Nat.succ target) hoperand
        have hctx' := BProv_context_cons (B := Ax_s)
          (a := operandGraph) hctx
        simpa [D, C, raw, operandComposite, operandGraph]
          using hctx'
      have hoperandReverse : BProv Ax_s D
          (imp operandGraph operandComposite) := by
        simpa [iffForm] using BProv_andE2 hoperandD
      have hoperandComposite : BProv Ax_s D operandComposite :=
        BProv_mp Ax_s D _ _ hoperandReverse hgraph
      have htargetD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.succ (Term.rename Nat.succ raw))
            (Term.var (codedOut + 1))) := by
        have hren := BProv_rename_succ_context_cons_of_sentences
          (B := Ax_s) Ax_s_sentences
          (a := operandGraph) htarget
        simpa [D, C, target,
          rename_ordinalCodeGraphTermAt, Term.rename] using hren
      have hstep :=
        BProv_Ax_s_hfAdjoinGraphTermAt_iff_ordinalCodeGraphTermAt_succ
          hsucc ordinalCodeGraphFunctional
          (codedOut := Term.var (codedOut + 1)) hgraph
      have hstepReverse : BProv Ax_s D
          (imp
            (ordinalCodeGraphTermAt
              (Term.succ (Term.rename Nat.succ raw))
              (Term.var (codedOut + 1)))
            adjoinGraph) := by
        simpa [iffForm, operandGraph, adjoinGraph,
          hfAdjoinGraphAt] using BProv_andE2 hstep
      have hadjoin : BProv Ax_s D adjoinGraph :=
        BProv_mp Ax_s D _ _ hstepReverse htargetD
      have hbody : BProv Ax_s D body :=
        BProv_andI hoperandComposite hadjoin
      change BProv Ax_s D
        (rename Nat.succ
          (compositeTermGraphAt codedOut codedMap (Term.succ t)))
      rw [compositeTermGraphAt_succ]
      apply BProv_exI (t := Term.var 0)
      rw [subst_instTerm_var_zero_rename_up_succ]
      simpa [body, operandComposite, adjoinGraph] using hbody
    exact BProv_exE_of_sentences
      (B := Ax_s) Ax_s_sentences
      (G := C) (a := operandGraph) (c := composite)
      htotal (by simpa [D] using hinner)
  simpa [iffForm, composite, target, raw, Term.rename] using
    BProv_andI hforward hreverse

/-- Successor preserves the complete term-graph induction property.  The
recursive theorem is instantiated after opening the constructor's fresh
operand-output slot, with all ambient input slots shifted by one. -/
theorem OrdinalCodeTermGraphProof_succ
    (hsucc : OrdinalCodeGraphSuccClosure) (t : Term)
    (ih : OrdinalCodeTermGraphProof t) :
    OrdinalCodeTermGraphProof (Term.succ t) := by
  intro G rawMap codedMap codedOut hcode
  let rawMap₁ : Nat → Nat := fun n ↦ rawMap n + 1
  let codedMap₁ : Nat → Nat := fun n ↦ codedMap n + 1
  have hcode₁ : ∀ n, Term.Free n t →
      BProv Ax_s (G.map (rename Nat.succ))
        (ordinalCodeGraphAt (rawMap₁ n) (codedMap₁ n)) := by
    intro n hn
    have hren := BProv_rename_of_sentences
      (B := Ax_s) Ax_s_sentences
      (hcode n hn) Nat.succ
    simpa [rawMap₁, codedMap₁, ordinalCodeGraphAt,
      rename_ordinalCodeGraphTermAt, Term.rename] using hren
  have hoperand₀ := ih
    (G.map (rename Nat.succ)) rawMap₁ codedMap₁ 0 hcode₁
  have hoperand : BProv Ax_s (G.map (rename Nat.succ))
      (iffForm
        (compositeTermGraphAt 0 (fun n ↦ codedMap n + 1) t)
        (ordinalCodeGraphTermAt
          (Term.rename Nat.succ (Term.rename rawMap t))
          (Term.var 0))) := by
    simpa [rawMap₁, codedMap₁, Term.rename_comp,
      Function.comp_def, Nat.add_assoc] using hoperand₀
  exact BProv_Ax_s_term_graph_succ_of_shifted_operand
    hsucc G t rawMap codedMap codedOut hoperand

/-- Concrete successor constructor for the complete term-graph induction
property. -/
theorem ordinalCodeTermGraphProof_succ (t : Term)
    (ih : OrdinalCodeTermGraphProof t) :
    OrdinalCodeTermGraphProof (Term.succ t) :=
  OrdinalCodeTermGraphProof_succ
    ordinalCodeGraphSuccClosure t ih

/-- Remaining addition-constructor obligation for the complete term-graph
induction. -/
def OrdinalCodeTermAddCompatibility : Prop :=
  ∀ a b,
    OrdinalCodeTermGraphProof a →
    OrdinalCodeTermGraphProof b →
    OrdinalCodeTermGraphProof (Term.add a b)

/-! ## Addition compatibility for ordinal-code term graphs -/

private def addLeftShift : Nat → Nat
  | 0 => 1
  | n+1 => n+3

private def addRightShift : Nat → Nat
  | 0 => 0
  | n+1 => n+3

theorem hfFormulaAt_add_left_termGraph_eq_composite
    (codedOut : Nat) (codedMap : Nat → Nat) (t : Term) :
    hfFormulaAt
        (hfUpVarMap (hfUpVarMap
          (codedTermSlotMap codedOut codedMap)))
        (AckermannHF.PAInHF.termGraphAt (fun n ↦ n+3) 1 t) =
      compositeTermGraphAt 1 (fun n ↦ codedMap n + 2) t := by
  let graph : Form :=
    AckermannHF.PAInHF.termGraphAt (fun n ↦ n+1) 0 t
  have hgraph : SetTheory.rename addLeftShift graph =
      AckermannHF.PAInHF.termGraphAt (fun n ↦ n+3) 1 t := by
    simpa [graph, addLeftShift] using
      (AckermannHF.PAInHF.termGraphAt_rename t
        (ρ := fun n ↦ n+1) (out := 0) (r := addLeftShift))
  rw [← hgraph, hfFormulaAt_source_rename]
  apply hfFormulaAt_ext
  intro n
  cases n <;> rfl

theorem hfFormulaAt_add_right_termGraph_eq_composite
    (codedOut : Nat) (codedMap : Nat → Nat) (t : Term) :
    hfFormulaAt
        (hfUpVarMap (hfUpVarMap
          (codedTermSlotMap codedOut codedMap)))
        (AckermannHF.PAInHF.termGraphAt (fun n ↦ n+3) 0 t) =
      compositeTermGraphAt 0 (fun n ↦ codedMap n + 2) t := by
  let graph : Form :=
    AckermannHF.PAInHF.termGraphAt (fun n ↦ n+1) 0 t
  have hgraph : SetTheory.rename addRightShift graph =
      AckermannHF.PAInHF.termGraphAt (fun n ↦ n+3) 0 t := by
    simpa [graph, addRightShift] using
      (AckermannHF.PAInHF.termGraphAt_rename t
        (ρ := fun n ↦ n+1) (out := 0) (r := addRightShift))
  rw [← hgraph, hfFormulaAt_source_rename]
  apply hfFormulaAt_ext
  intro n
  cases n <;> rfl

def compositeAddGraphAt
    (codedOut : Nat) (codedMap : Nat → Nat) : Formula :=
  hfFormulaAt
    (hfUpVarMap (hfUpVarMap
      (codedTermSlotMap codedOut codedMap)))
    (AckermannHF.PAInHF.addGraphAt 2 1 0)

private def compositeAddCoreSlotMap (codedOut : Nat) : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => codedOut + n + 2

def compositeAddCoreAt (codedOut : Nat) : Formula :=
  hfFormulaAt (compositeAddCoreSlotMap codedOut)
    (AckermannHF.PAInHF.addGraphAt 2 1 0)

theorem compositeAddGraphAt_eq_core
    (codedOut : Nat) (codedMap : Nat → Nat) :
    compositeAddGraphAt codedOut codedMap =
      compositeAddCoreAt codedOut := by
  apply hfFormulaAt_ext_free
  intro n hn
  rcases AckermannHF.PAInHF.addGraphAt_free hn with rfl | rfl | rfl
  · rfl
  · rfl
  · rfl

theorem compositeTermGraphAt_add_normalForm
    (codedOut : Nat) (codedMap : Nat → Nat) (a b : Term) :
    compositeTermGraphAt codedOut codedMap (Term.add a b) =
      ex (ex
        (and
          (compositeTermGraphAt 1 (fun n ↦ codedMap n + 2) a)
          (and
            (compositeTermGraphAt 0 (fun n ↦ codedMap n + 2) b)
            (compositeAddCoreAt codedOut)))) := by
  rw [← compositeAddGraphAt_eq_core codedOut codedMap]
  simp [compositeTermGraphAt,
    AckermannHF.PAInHF.termGraphAt, hfFormulaAt,
    compositeAddGraphAt,
    hfFormulaAt_add_left_termGraph_eq_composite,
    hfFormulaAt_add_right_termGraph_eq_composite]

/-- Arithmetic kernel left after the recursive subterm graphs have been
normalized: the translated HF addition graph agrees with the beta-coded
ordinal graph of PA addition. -/
private def OrdinalCodeAddCoreCompatibility : Prop :=
  ∀ {G : List Formula} {leftRaw rightRaw : Term} {codedOut : Nat},
    BProv Ax_s G
      (ordinalCodeGraphTermAt leftRaw (Term.var 1)) →
    BProv Ax_s G
      (ordinalCodeGraphTermAt rightRaw (Term.var 0)) →
    BProv Ax_s G
      (iffForm
        (compositeAddCoreAt codedOut)
        (ordinalCodeGraphTermAt
          (Term.add leftRaw rightRaw) (Term.var (codedOut+2))))

/-- Reverse translation of the HF addition graph while retaining explicit PA
variable slots. -/
def hfAddGraphAt (out left right : Nat) : Formula :=
  hfFormulaAt (fun n : Nat ↦ n)
    (AckermannHF.PAInHF.addGraphAt out left right)

def addHFOrdinalLikeAt (slot : Nat) : Formula :=
  hfFormulaAt (fun n : Nat ↦ n)
    (AckermannHF.HF_ordinalLikeAt slot)

def HF_addZeroRightSentence : SetTheory.Form :=
  SetTheory.Form.fAll (SetTheory.Form.fAll (SetTheory.Form.fAll
    (SetTheory.Form.fImp
      (AckermannHF.HF_emptyAt 1)
      (SetTheory.Form.fImp
        (SetTheory.Form.fEq 0 2)
        (AckermannHF.PAInHF.addGraphAt 0 2 1)))))

theorem HF_addZeroRightSentence_sentence :
    SetTheory.Sentence HF_addZeroRightSentence := by
  intro i hi
  simp only [HF_addZeroRightSentence, SetTheory.Free] at hi
  rcases hi with hempty | heq | hadd
  · have := AckermannHF.HF_emptyAt_free hempty
    omega
  · rcases heq with heq | heq <;> omega
  · rcases AckermannHF.PAInHF.addGraphAt_free hadd with
      hadd | hadd | hadd <;> omega

theorem BProv_HFFin_addZeroRightSentence :
    SetTheory.BProv AckermannHF.HFFinAx_s []
      HF_addZeroRightSentence := by
  apply SetTheory.completeness_inf AckermannHF.HFFinAx_s
  · exact AckermannHF.Sentences_HFFin
  · exact HF_addZeroRightSentence_sentence
  · intro Dom mem v hHF
    let M := AckermannHF.firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
    intro left right out hright hout
    let e : Nat → Dom :=
      SetTheory.scons out (SetTheory.scons right (SetTheory.scons left v))
    have hrightM : SetTheory.Sat M.mem e
        (AckermannHF.HF_emptyAt 1) := by
      change SetTheory.Sat mem e (AckermannHF.HF_emptyAt 1)
      simpa [e, SetTheory.scons] using hright
    apply AckermannHF.PAInHF.addGraphAt_zero_right_model
      M.toFirstOrderAdjunctionModel e 0 2 1
    · simpa [e, M, SetTheory.scons, SetTheory.Sat] using hout
    · exact
        (AckermannHF.FirstOrderAdjunctionModel.HF_emptyAt_empty
          M.toFirstOrderAdjunctionModel e 1).mp
          hrightM

theorem translateHFFormula_addZeroRightSentence :
    translateHFFormula HF_addZeroRightSentence =
      all (all (all
        (imp
          (hfEmptyAt 1)
          (imp
            (eq (Term.var 0) (Term.var 2))
            (hfAddGraphAt 0 2 1))))) := by
  let ρ : Nat → Nat :=
    hfUpVarMap (hfUpVarMap
      (hfUpVarMap (fun n : Nat ↦ n)))
  change all (all (all
    (imp
      (hfFormulaAt ρ (AckermannHF.HF_emptyAt 1))
      (imp
        (eq (Term.var (ρ 0)) (Term.var (ρ 2)))
        (hfFormulaAt ρ
          (AckermannHF.PAInHF.addGraphAt 0 2 1)))))) = _
  have hρ : ∀ n, ρ n = n := by
    intro n
    simp only [ρ, hfUpVarMap_id]
  rw [hfFormulaAt_ext _ hρ, hfFormulaAt_ext _ hρ,
    hρ 0, hρ 2]
  rfl

theorem BProv_Ax_s_addZeroRightSentence :
    BProv Ax_s []
      (all (all (all
        (imp
          (hfEmptyAt 1)
          (imp
            (eq (Term.var 0) (Term.var 2))
            (hfAddGraphAt 0 2 1)))))) := by
  have htranslated : BProv translatedHFFinAx []
      (translateHFFormula HF_addZeroRightSentence) :=
    BProv_translateHFFormula_of_BProv_HFFin
      BProv_HFFin_addZeroRightSentence
  have hpa : BProv Ax_s []
      (translateHFFormula HF_addZeroRightSentence) :=
    BProv_lift_translatedHFFinAx_to_PA
      (fun f hf ↦ BProv_Ax_s_of_translatedHFFinAx hf)
      htranslated
  rwa [translateHFFormula_addZeroRightSentence] at hpa

def HF_addSuccRightSentence : SetTheory.Form :=
  SetTheory.Form.fAll (SetTheory.Form.fAll (SetTheory.Form.fAll
    (SetTheory.Form.fAll (SetTheory.Form.fAll
      (SetTheory.Form.fImp
        (AckermannHF.HF_ordinalLikeAt 3)
        (SetTheory.Form.fImp
          (AckermannHF.HF_succAt 2 3)
          (SetTheory.Form.fImp
            (AckermannHF.HF_succAt 0 1)
            (SetTheory.Form.fImp
              (AckermannHF.PAInHF.addGraphAt 1 4 3)
              (AckermannHF.PAInHF.addGraphAt 0 4 2)))))))))

theorem HF_addSuccRightSentence_sentence :
    SetTheory.Sentence HF_addSuccRightSentence := by
  intro i hi
  simp only [HF_addSuccRightSentence, SetTheory.Free] at hi
  rcases hi with hord | hright | hout | hadd | hnext
  · have := AckermannHF.HF_ordinalLikeAt_free hord
    omega
  · rcases AckermannHF.HF_succAt_free hright with h | h <;> omega
  · rcases AckermannHF.HF_succAt_free hout with h | h <;> omega
  · rcases AckermannHF.PAInHF.addGraphAt_free hadd with
      h | h | h <;> omega
  · rcases AckermannHF.PAInHF.addGraphAt_free hnext with
      h | h | h <;> omega

theorem BProv_HFFin_addSuccRightSentence :
    SetTheory.BProv AckermannHF.HFFinAx_s []
      HF_addSuccRightSentence := by
  apply SetTheory.completeness_inf AckermannHF.HFFinAx_s
  · exact AckermannHF.Sentences_HFFin
  · exact HF_addSuccRightSentence_sentence
  · intro Dom mem v hHF
    let M := AckermannHF.firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
    intro left right rightSucc out outSucc
      hrightOrd hrightSucc houtSucc hadd
    let e : Nat → Dom :=
      SetTheory.scons outSucc
        (SetTheory.scons out
          (SetTheory.scons rightSucc
            (SetTheory.scons right (SetTheory.scons left v))))
    have hrightOrdM : SetTheory.Sat M.mem e
        (AckermannHF.HF_ordinalLikeAt 3) := by
      change SetTheory.Sat mem e (AckermannHF.HF_ordinalLikeAt 3)
      simpa [e, SetTheory.scons] using hrightOrd
    have hrightSuccM : SetTheory.Sat M.mem e
        (AckermannHF.HF_succAt 2 3) := by
      change SetTheory.Sat mem e (AckermannHF.HF_succAt 2 3)
      simpa [e, SetTheory.scons] using hrightSucc
    have houtSuccM : SetTheory.Sat M.mem e
        (AckermannHF.HF_succAt 0 1) := by
      change SetTheory.Sat mem e (AckermannHF.HF_succAt 0 1)
      simpa [e, SetTheory.scons] using houtSucc
    have haddM : SetTheory.Sat M.mem e
        (AckermannHF.PAInHF.addGraphAt 1 4 3) := by
      change SetTheory.Sat mem e
        (AckermannHF.PAInHF.addGraphAt 1 4 3)
      simpa [e, SetTheory.scons] using hadd
    apply AckermannHF.PAInHF.addGraphAt_succ_right_of_addGraphAt_model
      M.toFirstOrderAdjunctionModel e 0 1 4 2 3
    · exact
        (AckermannHF.HF_ordinalLikeAt_spec e 3).mp
          hrightOrdM
    · exact
        (AckermannHF.FirstOrderAdjunctionModel.HF_succAt_spec
          M.toFirstOrderAdjunctionModel e 2 3).mp
          hrightSuccM
    · exact
        (AckermannHF.FirstOrderAdjunctionModel.HF_succAt_spec
          M.toFirstOrderAdjunctionModel e 0 1).mp
          houtSuccM
    · exact haddM

theorem translateHFFormula_addSuccRightSentence :
    translateHFFormula HF_addSuccRightSentence =
      all (all (all (all (all
        (imp
          (addHFOrdinalLikeAt 3)
          (imp
            (hfAdjoinGraphAt 2 3 3)
            (imp
              (hfAdjoinGraphAt 0 1 1)
              (imp
                (hfAddGraphAt 1 4 3)
                (hfAddGraphAt 0 4 2))))))))) := by
  let ρ : Nat → Nat :=
    hfUpVarMap (hfUpVarMap (hfUpVarMap
      (hfUpVarMap (hfUpVarMap (fun n : Nat ↦ n)))))
  change all (all (all (all (all
    (imp
      (hfFormulaAt ρ (AckermannHF.HF_ordinalLikeAt 3))
      (imp
        (hfFormulaAt ρ (AckermannHF.HF_succAt 2 3))
        (imp
          (hfFormulaAt ρ (AckermannHF.HF_succAt 0 1))
          (imp
            (hfFormulaAt ρ
              (AckermannHF.PAInHF.addGraphAt 1 4 3))
            (hfFormulaAt ρ
              (AckermannHF.PAInHF.addGraphAt 0 4 2)))))))))) = _
  have hρ : ∀ n, ρ n = n := by
    intro n
    simp only [ρ, hfUpVarMap_id]
  rw [hfFormulaAt_ext _ hρ, hfFormulaAt_ext _ hρ,
    hfFormulaAt_ext _ hρ, hfFormulaAt_ext _ hρ,
    hfFormulaAt_ext _ hρ]
  rfl

theorem BProv_Ax_s_addSuccRightSentence :
    BProv Ax_s []
      (all (all (all (all (all
        (imp
          (addHFOrdinalLikeAt 3)
          (imp
            (hfAdjoinGraphAt 2 3 3)
            (imp
              (hfAdjoinGraphAt 0 1 1)
              (imp
                (hfAddGraphAt 1 4 3)
                (hfAddGraphAt 0 4 2)))))))))) := by
  have htranslated : BProv translatedHFFinAx []
      (translateHFFormula HF_addSuccRightSentence) :=
    BProv_translateHFFormula_of_BProv_HFFin
      BProv_HFFin_addSuccRightSentence
  have hpa : BProv Ax_s []
      (translateHFFormula HF_addSuccRightSentence) :=
    BProv_lift_translatedHFFinAx_to_PA
      (fun f hf ↦ BProv_Ax_s_of_translatedHFFinAx hf)
      htranslated
  rwa [translateHFFormula_addSuccRightSentence] at hpa

def HF_addFunctionalSentence : SetTheory.Form :=
  SetTheory.Form.fAll (SetTheory.Form.fAll (SetTheory.Form.fAll
    (SetTheory.Form.fAll
      (SetTheory.Form.fImp
        (AckermannHF.HF_ordinalLikeAt 2)
        (SetTheory.Form.fImp
          (AckermannHF.PAInHF.addGraphAt 1 3 2)
          (SetTheory.Form.fImp
            (AckermannHF.PAInHF.addGraphAt 0 3 2)
            (SetTheory.Form.fEq 1 0)))))))

theorem HF_addFunctionalSentence_sentence :
    SetTheory.Sentence HF_addFunctionalSentence := by
  intro i hi
  simp only [HF_addFunctionalSentence, SetTheory.Free] at hi
  rcases hi with hord | hadd₁ | hadd₂ | heq
  · have := AckermannHF.HF_ordinalLikeAt_free hord
    omega
  · rcases AckermannHF.PAInHF.addGraphAt_free hadd₁ with
      h | h | h <;> omega
  · rcases AckermannHF.PAInHF.addGraphAt_free hadd₂ with
      h | h | h <;> omega
  · rcases heq with h | h <;> omega

theorem BProv_HFFin_addFunctionalSentence :
    SetTheory.BProv AckermannHF.HFFinAx_s []
      HF_addFunctionalSentence := by
  apply SetTheory.completeness_inf AckermannHF.HFFinAx_s
  · exact AckermannHF.Sentences_HFFin
  · exact HF_addFunctionalSentence_sentence
  · intro Dom mem v hHF
    let M := AckermannHF.firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
    intro left right out₁ out₂ hrightOrd hadd₁ hadd₂
    let e : Nat → Dom :=
      SetTheory.scons out₂
        (SetTheory.scons out₁
          (SetTheory.scons right (SetTheory.scons left v)))
    have hrightOrdM : SetTheory.Sat M.mem e
        (AckermannHF.HF_ordinalLikeAt 2) := by
      change SetTheory.Sat mem e (AckermannHF.HF_ordinalLikeAt 2)
      simpa [e, SetTheory.scons] using hrightOrd
    have hadd₁M : SetTheory.Sat M.mem e
        (AckermannHF.PAInHF.addGraphAt 1 3 2) := by
      change SetTheory.Sat mem e
        (AckermannHF.PAInHF.addGraphAt 1 3 2)
      simpa [e, SetTheory.scons] using hadd₁
    have hadd₂M : SetTheory.Sat M.mem e
        (AckermannHF.PAInHF.addGraphAt 0 3 2) := by
      change SetTheory.Sat mem e
        (AckermannHF.PAInHF.addGraphAt 0 3 2)
      simpa [e, SetTheory.scons] using hadd₂
    exact AckermannHF.PAInHF.addGraphAt_value_unique_finite_model
      M e 1 0 3 2
      ((AckermannHF.HF_ordinalLikeAt_spec e 2).mp
        hrightOrdM)
      hadd₁M hadd₂M

theorem translateHFFormula_addFunctionalSentence :
    translateHFFormula HF_addFunctionalSentence =
      all (all (all (all
        (imp
          (addHFOrdinalLikeAt 2)
          (imp
            (hfAddGraphAt 1 3 2)
            (imp
              (hfAddGraphAt 0 3 2)
              (eq (Term.var 1) (Term.var 0)))))))) := by
  let ρ : Nat → Nat :=
    hfUpVarMap (hfUpVarMap
      (hfUpVarMap (hfUpVarMap (fun n : Nat ↦ n))))
  change all (all (all (all
    (imp
      (hfFormulaAt ρ (AckermannHF.HF_ordinalLikeAt 2))
      (imp
        (hfFormulaAt ρ
          (AckermannHF.PAInHF.addGraphAt 1 3 2))
        (imp
          (hfFormulaAt ρ
            (AckermannHF.PAInHF.addGraphAt 0 3 2))
          (eq (Term.var (ρ 1)) (Term.var (ρ 0))))))))) = _
  have hρ : ∀ n, ρ n = n := by
    intro n
    simp only [ρ, hfUpVarMap_id]
  rw [hfFormulaAt_ext _ hρ, hfFormulaAt_ext _ hρ,
    hfFormulaAt_ext _ hρ, hρ 1, hρ 0]
  rfl

theorem BProv_Ax_s_addFunctionalSentence :
    BProv Ax_s []
      (all (all (all (all
        (imp
          (addHFOrdinalLikeAt 2)
          (imp
            (hfAddGraphAt 1 3 2)
            (imp
              (hfAddGraphAt 0 3 2)
              (eq (Term.var 1) (Term.var 0))))))))) := by
  have htranslated : BProv translatedHFFinAx []
      (translateHFFormula HF_addFunctionalSentence) :=
    BProv_translateHFFormula_of_BProv_HFFin
      BProv_HFFin_addFunctionalSentence
  have hpa : BProv Ax_s []
      (translateHFFormula HF_addFunctionalSentence) :=
    BProv_lift_translatedHFFinAx_to_PA
      (fun f hf ↦ BProv_Ax_s_of_translatedHFFinAx hf)
      htranslated
  rwa [translateHFFormula_addFunctionalSentence] at hpa

private def addTermSubst
    (out left right : Term) : Nat → Term
  | 0 => right
  | 1 => left
  | 2 => out
  | n+3 => Term.var (n+3)

/-- Term-parametric form of the reverse-translated HF addition graph. -/
def hfAddGraphTermAt
    (out left right : Term) : Formula :=
  subst (addTermSubst out left right)
    (hfAddGraphAt 2 1 0)

theorem hfAddGraphAt_eq_termAt
    (out left right : Nat) :
    hfAddGraphAt out left right =
      hfAddGraphTermAt
        (Term.var out) (Term.var left) (Term.var right) := by
  let r : Nat → Nat
    | 0 => right
    | 1 => left
    | 2 => out
    | n+3 => n+3
  have hsubst :
      addTermSubst
          (Term.var out) (Term.var left) (Term.var right) =
        fun n ↦ Term.var (r n) := by
    funext n
    rcases n with _ | _ | _ | n <;> rfl
  have hsource :
      SetTheory.rename r
          (AckermannHF.PAInHF.addGraphAt 2 1 0) =
        AckermannHF.PAInHF.addGraphAt out left right := by
    simpa [r] using
      (AckermannHF.PAInHF.rename_addGraphAt r 2 1 0)
  simp only [hfAddGraphTermAt, hsubst, subst_var_rename,
    hfAddGraphAt]
  rw [← hsource]
  exact hfFormulaAt_id_rename _ _

theorem subst_hfAddGraphTermAt
    (sigma : Nat → Term) (out left right : Term) :
    subst sigma (hfAddGraphTermAt out left right) =
      hfAddGraphTermAt
        (Term.subst sigma out)
        (Term.subst sigma left)
        (Term.subst sigma right) := by
  simp only [hfAddGraphTermAt, subst_comp]
  apply subst_ext_free
  intro n hn
  rcases hfFormulaAt_free _ hn with ⟨m, hm, rfl⟩
  rcases AckermannHF.PAInHF.addGraphAt_free hm with rfl | rfl | rfl
  · rfl
  · rfl
  · rfl

theorem rename_hfAddGraphTermAt
    (r : Nat → Nat) (out left right : Term) :
    rename r (hfAddGraphTermAt out left right) =
      hfAddGraphTermAt
        (Term.rename r out)
        (Term.rename r left)
        (Term.rename r right) := by
  rw [← subst_var_rename]
  simp only [subst_hfAddGraphTermAt,
    term_subst_var_rename]

theorem compositeAddCoreAt_eq_termAt
    (codedOut : Nat) :
    compositeAddCoreAt codedOut =
      hfAddGraphTermAt
        (Term.var (codedOut+2)) (Term.var 1) (Term.var 0) := by
  rw [← hfAddGraphAt_eq_termAt]
  simp only [compositeAddCoreAt, hfAddGraphAt]
  let r : Nat → Nat := compositeAddCoreSlotMap codedOut
  have hsource :
      SetTheory.rename r
          (AckermannHF.PAInHF.addGraphAt 2 1 0) =
        AckermannHF.PAInHF.addGraphAt (codedOut+2) 1 0 := by
    simpa [r, compositeAddCoreSlotMap] using
      (AckermannHF.PAInHF.rename_addGraphAt r 2 1 0)
  rw [← hsource, hfFormulaAt_source_rename]

theorem BProv_Ax_s_hfAddGraphTermAt_zero_right
    {G : List Formula} {out left right : Term}
    (hright : BProv Ax_s G (hfEmptyTermAt right))
    (hout : BProv Ax_s G (eq out left)) :
    BProv Ax_s G (hfAddGraphTermAt out left right) := by
  have hall : BProv Ax_s G
      (all (all (all
        (imp
          (hfEmptyTermAt (Term.var 1))
          (imp
            (eq (Term.var 0) (Term.var 2))
            (hfAddGraphTermAt
              (Term.var 0) (Term.var 2) (Term.var 1))))))) := by
    simpa only [hfEmptyAt, hfAddGraphAt_eq_termAt] using
      (BProv_weaken_nil
        (G := G) BProv_Ax_s_addZeroRightSentence)
  have hleft := BProv_allE (B := Ax_s) (G := G) (t := left) hall
  have hright₀ := BProv_allE (B := Ax_s) (G := G) (t := right) hleft
  have hout₀ := BProv_allE (B := Ax_s) (G := G) (t := out) hright₀
  have himp : BProv Ax_s G
      (imp
        (hfEmptyTermAt right)
        (imp (eq out left)
          (hfAddGraphTermAt out left right))) := by
    simpa [subst_hfEmptyTermAt,
      subst_hfAddGraphTermAt,
      subst, instTerm, Term.subst, Term.upSubst,
      Term.subst_rename_succ_up,
      term_subst_instTerm_rename_succ] using hout₀
  have hstep := BProv_mp Ax_s G _ _ himp hright
  exact BProv_mp Ax_s G _ _ hstep hout

theorem addHFOrdinalLikeAt_eq_domainTermAt (slot : Nat) :
    addHFOrdinalLikeAt slot =
      subst (instTerm (Term.var slot)) codedOrdinalDomain := by
  have hsource :
      SetTheory.rename (SetTheory.inst slot)
          AckermannHF.PAInHF.domainForm =
        AckermannHF.HF_ordinalLikeAt slot := by
    simp [AckermannHF.PAInHF.domainForm,
      AckermannHF.HF_ordinalLikeAt,
      AckermannHF.HF_transitiveAt,
      AckermannHF.HF_memTotalOnAt,
      SetTheory.rename, SetTheory.up, SetTheory.inst]
  simp only [addHFOrdinalLikeAt, codedOrdinalDomain,
    translateHFFormula, subst_instTerm_var]
  rw [← hsource]
  exact hfFormulaAt_id_rename _ _

theorem subst_domainTermAt
    (sigma : Nat → Term) (coded : Term) :
    subst sigma (subst (instTerm coded) codedOrdinalDomain) =
      subst (instTerm (Term.subst sigma coded))
        codedOrdinalDomain := by
  rw [subst_comp]
  apply subst_ext_free
  intro n hn
  have hn₀ := codedOrdinalDomain_free hn
  subst n
  rfl

theorem BProv_Ax_s_hfAddGraphTermAt_succ_right
    {G : List Formula}
    {outSucc out left rightSucc right : Term}
    (hrightDomain : BProv Ax_s G
      (subst (instTerm right) codedOrdinalDomain))
    (hrightSucc : BProv Ax_s G
      (hfAdjoinGraphTermAt rightSucc right right))
    (houtSucc : BProv Ax_s G
      (hfAdjoinGraphTermAt outSucc out out))
    (hadd : BProv Ax_s G
      (hfAddGraphTermAt out left right)) :
    BProv Ax_s G
      (hfAddGraphTermAt outSucc left rightSucc) := by
  have hall : BProv Ax_s G
      (all (all (all (all (all
        (imp
          (subst (instTerm (Term.var 3)) codedOrdinalDomain)
          (imp
            (hfAdjoinGraphTermAt
              (Term.var 2) (Term.var 3) (Term.var 3))
            (imp
              (hfAdjoinGraphTermAt
                (Term.var 0) (Term.var 1) (Term.var 1))
              (imp
                (hfAddGraphTermAt
                  (Term.var 1) (Term.var 4) (Term.var 3))
                (hfAddGraphTermAt
                  (Term.var 0) (Term.var 4) (Term.var 2))))))))))) := by
    simpa only [addHFOrdinalLikeAt_eq_domainTermAt,
      hfAdjoinGraphAt, hfAddGraphAt_eq_termAt] using
      (BProv_weaken_nil
        (G := G) BProv_Ax_s_addSuccRightSentence)
  have hleft := BProv_allE (B := Ax_s) (G := G) (t := left) hall
  have hright₀ := BProv_allE (B := Ax_s) (G := G) (t := right) hleft
  have hrightSucc₀ :=
    BProv_allE (B := Ax_s) (G := G) (t := rightSucc) hright₀
  have hout₀ := BProv_allE (B := Ax_s) (G := G) (t := out) hrightSucc₀
  have houtSucc₀ :=
    BProv_allE (B := Ax_s) (G := G) (t := outSucc) hout₀
  have himp : BProv Ax_s G
      (imp
        (subst (instTerm right) codedOrdinalDomain)
        (imp
          (hfAdjoinGraphTermAt rightSucc right right)
          (imp
            (hfAdjoinGraphTermAt outSucc out out)
            (imp
              (hfAddGraphTermAt out left right)
              (hfAddGraphTermAt outSucc left rightSucc))))) := by
    simpa [subst_domainTermAt,
      subst_hfAdjoinGraphTermAt,
      subst_hfAddGraphTermAt,
      subst, instTerm, Term.subst, Term.upSubst,
      Term.subst_rename_succ_up,
      term_subst_instTerm_rename_succ] using houtSucc₀
  have h₁ := BProv_mp Ax_s G _ _ himp hrightDomain
  have h₂ := BProv_mp Ax_s G _ _ h₁ hrightSucc
  have h₃ := BProv_mp Ax_s G _ _ h₂ houtSucc
  exact BProv_mp Ax_s G _ _ h₃ hadd

theorem BProv_Ax_s_hfAddGraphTermAt_functional
    {G : List Formula} {out₁ out₂ left right : Term}
    (hrightDomain : BProv Ax_s G
      (subst (instTerm right) codedOrdinalDomain))
    (hadd₁ : BProv Ax_s G
      (hfAddGraphTermAt out₁ left right))
    (hadd₂ : BProv Ax_s G
      (hfAddGraphTermAt out₂ left right)) :
    BProv Ax_s G (eq out₁ out₂) := by
  have hall : BProv Ax_s G
      (all (all (all (all
        (imp
          (subst (instTerm (Term.var 2)) codedOrdinalDomain)
          (imp
            (hfAddGraphTermAt
              (Term.var 1) (Term.var 3) (Term.var 2))
            (imp
              (hfAddGraphTermAt
                (Term.var 0) (Term.var 3) (Term.var 2))
              (eq (Term.var 1) (Term.var 0))))))))) := by
    simpa only [addHFOrdinalLikeAt_eq_domainTermAt,
      hfAddGraphAt_eq_termAt] using
      (BProv_weaken_nil
        (G := G) BProv_Ax_s_addFunctionalSentence)
  have hleft := BProv_allE (B := Ax_s) (G := G) (t := left) hall
  have hright₀ := BProv_allE (B := Ax_s) (G := G) (t := right) hleft
  have hout₁₀ := BProv_allE (B := Ax_s) (G := G) (t := out₁) hright₀
  have hout₂₀ := BProv_allE (B := Ax_s) (G := G) (t := out₂) hout₁₀
  have himp : BProv Ax_s G
      (imp
        (subst (instTerm right) codedOrdinalDomain)
        (imp
          (hfAddGraphTermAt out₁ left right)
          (imp
            (hfAddGraphTermAt out₂ left right)
            (eq out₁ out₂)))) := by
    simpa [subst_domainTermAt,
      subst_hfAddGraphTermAt,
      subst, instTerm, Term.subst, Term.upSubst,
      Term.subst_rename_succ_up,
      term_subst_instTerm_rename_succ] using hout₂₀
  have h₁ := BProv_mp Ax_s G _ _ himp hrightDomain
  have h₂ := BProv_mp Ax_s G _ _ h₁ hadd₁
  exact BProv_mp Ax_s G _ _ h₂ hadd₂

theorem BProv_Ax_s_codedOrdinalDomain_of_graph
    {G : List Formula} {raw coded : Term}
    (hgraph : BProv Ax_s G
      (ordinalCodeGraphTermAt raw coded)) :
    BProv Ax_s G
      (subst (instTerm coded) codedOrdinalDomain) := by
  have hrange : BProv Ax_s G
      (ordinalCodeGraphRangeExistsTermAt coded) := by
    apply BProv_exI (t := raw)
    simpa [ordinalCodeGraphRangeExistsTermAt,
      subst_ordinalCodeGraphTermAt,
      subst, instTerm, Term.subst,
      term_subst_instTerm_rename_succ] using hgraph
  exact ordinalCodeGraphCodomain hrange

theorem BProv_Ax_s_hfEmptyTermAt_of_eq_zero
    {G : List Formula} {term : Term}
    (heq : BProv Ax_s G (eq term Term.zero)) :
    BProv Ax_s G (hfEmptyTermAt term) := by
  let context : Formula := hfEmptyTermAt (Term.var 0)
  have hzero : BProv Ax_s G
      (subst (instTerm Term.zero) context) := by
    simpa [context, subst_hfEmptyTermAt,
      instTerm, Term.subst] using
      (BProv_weaken_nil (G := G) BProv_Ax_s_hfEmptyTermAt_zero)
  have htransport := BProv_eqElim
    (B := Ax_s) (G := G) (a := context)
    (BProv_eqSym heq) hzero
  simpa [context, subst_hfEmptyTermAt,
    instTerm, Term.subst,
    term_subst_instTerm_rename_succ] using htransport

/-- Base case of ordinal-code addition: HF successor recursion at the empty
right code agrees exactly with PA addition by zero. -/
theorem BProv_Ax_s_ordinalCodeAddCore_zero
    {G : List Formula} {leftRaw leftCode rightCode out : Term}
    (hleft : BProv Ax_s G
      (ordinalCodeGraphTermAt leftRaw leftCode))
    (hright : BProv Ax_s G
      (ordinalCodeGraphTermAt Term.zero rightCode)) :
    BProv Ax_s G
      (iffForm
        (hfAddGraphTermAt out leftCode rightCode)
        (ordinalCodeGraphTermAt
          (Term.add leftRaw Term.zero) out)) := by
  have hrightEq : BProv Ax_s G (eq rightCode Term.zero) :=
    BProv_Ax_s_eq_zero_of_ordinalCodeGraphTermAt_zero hright
  have hrightEmpty : BProv Ax_s G (hfEmptyTermAt rightCode) :=
    BProv_Ax_s_hfEmptyTermAt_of_eq_zero hrightEq
  have hrightDomain :=
    BProv_Ax_s_codedOrdinalDomain_of_graph hright
  have hbase : BProv Ax_s G
      (hfAddGraphTermAt leftCode leftCode rightCode) :=
    BProv_Ax_s_hfAddGraphTermAt_zero_right
      hrightEmpty (BProv_eqRefl leftCode)
  have haddZero : BProv Ax_s G
      (eq (Term.add leftRaw Term.zero) leftRaw) :=
    (BProv_Ax_s_addZero_term leftRaw)
  have hforward : BProv Ax_s G
      (imp
        (hfAddGraphTermAt out leftCode rightCode)
        (ordinalCodeGraphTermAt
          (Term.add leftRaw Term.zero) out)) := by
    apply BProv_impI
    let C : List Formula :=
      hfAddGraphTermAt out leftCode rightCode :: G
    have hadd : BProv Ax_s C
        (hfAddGraphTermAt out leftCode rightCode) :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have houtEq : BProv Ax_s C (eq out leftCode) :=
      BProv_Ax_s_hfAddGraphTermAt_functional
        (BProv_context_cons hrightDomain)
        hadd (BProv_context_cons hbase)
    exact BProv_ordinalCodeGraphTermAt_congr
      (BProv_eqSym (BProv_context_cons haddZero))
      (BProv_eqSym houtEq) (BProv_context_cons hleft)
  have hreverse : BProv Ax_s G
      (imp
        (ordinalCodeGraphTermAt
          (Term.add leftRaw Term.zero) out)
        (hfAddGraphTermAt out leftCode rightCode)) := by
    apply BProv_impI
    let C : List Formula :=
      ordinalCodeGraphTermAt
        (Term.add leftRaw Term.zero) out :: G
    have htarget : BProv Ax_s C
        (ordinalCodeGraphTermAt
          (Term.add leftRaw Term.zero) out) :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have houtGraph : BProv Ax_s C
        (ordinalCodeGraphTermAt leftRaw out) :=
      BProv_ordinalCodeGraphTermAt_congr_raw
        (BProv_context_cons haddZero) htarget
    have houtEq : BProv Ax_s C (eq out leftCode) :=
      BProv_Ax_s_ordinalCodeGraphTermAt_functional
        houtGraph (BProv_context_cons hleft)
    exact BProv_Ax_s_hfAddGraphTermAt_zero_right
      (BProv_context_cons hrightEmpty) houtEq
  exact BProv_iffForm_intro hforward hreverse

def ordinalCodeAddOutputTermAt
    (leftRaw leftCode rightRaw rightCode : Term) : Formula :=
  all
    (iffForm
      (hfAddGraphTermAt
        (Term.var 0)
        (Term.rename Nat.succ leftCode)
        (Term.rename Nat.succ rightCode))
      (ordinalCodeGraphTermAt
        (Term.rename Nat.succ (Term.add leftRaw rightRaw))
        (Term.var 0)))

theorem subst_ordinalCodeAddOutputTermAt
    (sigma : Nat → Term)
    (leftRaw leftCode rightRaw rightCode : Term) :
    subst sigma
        (ordinalCodeAddOutputTermAt
          leftRaw leftCode rightRaw rightCode) =
      ordinalCodeAddOutputTermAt
        (Term.subst sigma leftRaw)
        (Term.subst sigma leftCode)
        (Term.subst sigma rightRaw)
        (Term.subst sigma rightCode) := by
  simp only [ordinalCodeAddOutputTermAt, iffForm, subst]
  rw [subst_hfAddGraphTermAt,
    subst_ordinalCodeGraphTermAt]
  simp only [Term.subst, Term.upSubst,
    Term.subst_rename_succ_up]

theorem rename_ordinalCodeAddOutputTermAt
    (r : Nat → Nat)
    (leftRaw leftCode rightRaw rightCode : Term) :
    rename r
        (ordinalCodeAddOutputTermAt
          leftRaw leftCode rightRaw rightCode) =
      ordinalCodeAddOutputTermAt
        (Term.rename r leftRaw)
        (Term.rename r leftCode)
        (Term.rename r rightRaw)
        (Term.rename r rightCode) := by
  rw [← subst_var_rename]
  simp only [subst_ordinalCodeAddOutputTermAt,
    term_subst_var_rename]

def ordinalCodeAddPointTermAt
    (leftRaw leftCode rightRaw : Term) : Formula :=
  all
    (imp
      (ordinalCodeGraphTermAt
        (Term.rename Nat.succ rightRaw) (Term.var 0))
      (ordinalCodeAddOutputTermAt
        (Term.rename Nat.succ leftRaw)
        (Term.rename Nat.succ leftCode)
        (Term.rename Nat.succ rightRaw)
        (Term.var 0)))

theorem subst_ordinalCodeAddPointTermAt
    (sigma : Nat → Term)
    (leftRaw leftCode rightRaw : Term) :
    subst sigma
        (ordinalCodeAddPointTermAt
          leftRaw leftCode rightRaw) =
      ordinalCodeAddPointTermAt
        (Term.subst sigma leftRaw)
        (Term.subst sigma leftCode)
        (Term.subst sigma rightRaw) := by
  simp [ordinalCodeAddPointTermAt,
    subst_ordinalCodeGraphTermAt,
    subst_ordinalCodeAddOutputTermAt,
    subst, Term.subst, Term.upSubst,
    Term.subst_rename_succ_up]

theorem rename_ordinalCodeAddPointTermAt
    (r : Nat → Nat)
    (leftRaw leftCode rightRaw : Term) :
    rename r
        (ordinalCodeAddPointTermAt
          leftRaw leftCode rightRaw) =
      ordinalCodeAddPointTermAt
        (Term.rename r leftRaw)
        (Term.rename r leftCode)
        (Term.rename r rightRaw) := by
  rw [← subst_var_rename]
  simp only [subst_ordinalCodeAddPointTermAt,
    term_subst_var_rename]

theorem BProv_Ax_s_ordinalCodeAddPointTermAt_zero
    {G : List Formula} {leftRaw leftCode : Term}
    (hleft : BProv Ax_s G
      (ordinalCodeGraphTermAt leftRaw leftCode)) :
    BProv Ax_s G
      (ordinalCodeAddPointTermAt
        leftRaw leftCode Term.zero) := by
  let rightGraph : Formula :=
    ordinalCodeGraphTermAt Term.zero (Term.var 0)
  let Q : List Formula := G.map (rename Nat.succ)
  have hbody : BProv Ax_s Q
      (imp rightGraph
        (ordinalCodeAddOutputTermAt
          (Term.rename Nat.succ leftRaw)
          (Term.rename Nat.succ leftCode)
          Term.zero (Term.var 0))) := by
    apply BProv_impI
    let C : List Formula := rightGraph :: Q
    have hright : BProv Ax_s C rightGraph :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    let D : List Formula := C.map (rename Nat.succ)
    have hleftD : BProv Ax_s D
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+2) leftRaw)
          (Term.rename (fun n ↦ n+2) leftCode)) := by
      have h₂ := BProv_iterRenameSucc_of_sentences
        (B := Ax_s) Ax_s_sentences
        2 hleft
      have hctx := BProv_context_cons
        (B := Ax_s) (a := rename Nat.succ rightGraph) h₂
      simpa [D, C, Q, iterRenameContextSucc, iterRenameSucc,
        rename_ordinalCodeGraphTermAt,
        Term.rename_comp, Function.comp_def, Nat.add_assoc] using hctx
    have hrightD : BProv Ax_s D
        (ordinalCodeGraphTermAt Term.zero (Term.var 1)) := by
      have hren := BProv_rename_of_sentences
        (B := Ax_s) Ax_s_sentences
        hright Nat.succ
      simpa [D, rightGraph,
        rename_ordinalCodeGraphTermAt, Term.rename] using hren
    have hiff := BProv_Ax_s_ordinalCodeAddCore_zero
      (out := Term.var 0) hleftD hrightD
    have hall := BProv_allI_of_sentences
      (B := Ax_s) (G := C)
      Ax_s_sentences hiff
    simpa [ordinalCodeAddOutputTermAt,
      D, Term.rename, Term.rename_comp,
      Function.comp_def, Nat.add_assoc] using hall
  have hall := BProv_allI_of_sentences
    (B := Ax_s) (G := G)
    Ax_s_sentences hbody
  simpa [ordinalCodeAddPointTermAt,
    rightGraph, Q, Term.rename] using hall

theorem BProv_Ax_s_ordinalCodeAddCore_succ_of_pred
    {G : List Formula}
    {leftRaw leftCode rightRaw rightCode rightSuccCode predOut out : Term}
    (hright : BProv Ax_s G
      (ordinalCodeGraphTermAt rightRaw rightCode))
    (hrightSucc : BProv Ax_s G
      (ordinalCodeGraphTermAt (Term.succ rightRaw) rightSuccCode))
    (hsumPred : BProv Ax_s G
      (ordinalCodeGraphTermAt
        (Term.add leftRaw rightRaw) predOut))
    (haddPred : BProv Ax_s G
      (hfAddGraphTermAt predOut leftCode rightCode)) :
    BProv Ax_s G
      (iffForm
        (hfAddGraphTermAt out leftCode rightSuccCode)
        (ordinalCodeGraphTermAt
          (Term.add leftRaw (Term.succ rightRaw)) out)) := by
  have hrightDomain :=
    BProv_Ax_s_codedOrdinalDomain_of_graph hright
  have hrightSuccDomain :=
    BProv_Ax_s_codedOrdinalDomain_of_graph hrightSucc
  have hrightStep :=
    BProv_Ax_s_hfAdjoinGraphTermAt_iff_ordinalCodeGraphTermAt_succ
      ordinalCodeGraphSuccClosure ordinalCodeGraphFunctional
      (codedOut := rightSuccCode) hright
  have hrightStepReverse : BProv Ax_s G
      (imp
        (ordinalCodeGraphTermAt
          (Term.succ rightRaw) rightSuccCode)
        (hfAdjoinGraphTermAt
          rightSuccCode rightCode rightCode)) := by
    simpa [iffForm] using BProv_andE2 hrightStep
  have hrightAdjoin : BProv Ax_s G
      (hfAdjoinGraphTermAt rightSuccCode rightCode rightCode) :=
    BProv_mp Ax_s G _ _ hrightStepReverse hrightSucc
  have haddSucc : BProv Ax_s G
      (eq
        (Term.add leftRaw (Term.succ rightRaw))
        (Term.succ (Term.add leftRaw rightRaw))) :=
    (BProv_Ax_s_addSucc_terms leftRaw rightRaw)
  have hforward : BProv Ax_s G
      (imp
        (hfAddGraphTermAt out leftCode rightSuccCode)
        (ordinalCodeGraphTermAt
          (Term.add leftRaw (Term.succ rightRaw)) out)) := by
    apply BProv_impI
    let C : List Formula :=
      hfAddGraphTermAt out leftCode rightSuccCode :: G
    have haddOut : BProv Ax_s C
        (hfAddGraphTermAt out leftCode rightSuccCode) :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hex : BProv Ax_s C
        (hfAdjoinExistsTermAt predOut predOut) :=
      BProv_Ax_s_hfAdjoinExistsTermAt predOut predOut
    let body : Formula :=
      hfAdjoinGraphTermAt
        (Term.var 0)
        (Term.rename Nat.succ predOut)
        (Term.rename Nat.succ predOut)
    let D : List Formula := body :: C.map (rename Nat.succ)
    have hinner : BProv Ax_s D
        (rename Nat.succ
          (ordinalCodeGraphTermAt
            (Term.add leftRaw (Term.succ rightRaw)) out)) := by
      have hadjoin : BProv Ax_s D body :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D])
      have lift : ∀ {phi : Formula}, BProv Ax_s C phi →
          BProv Ax_s D (rename Nat.succ phi) := by
        intro phi hphi
        simpa [D] using
          (BProv_rename_succ_context_cons_of_sentences
            (B := Ax_s) Ax_s_sentences
            (a := body) hphi)
      have hrightDomainD : BProv Ax_s D
          (subst
            (instTerm (Term.rename Nat.succ rightCode))
            codedOrdinalDomain) := by
        have hraw := lift (BProv_context_cons hrightDomain)
        simpa [rename_subst_instTerm_codedOrdinalDomain] using hraw
      have hrightSuccDomainD : BProv Ax_s D
          (subst
            (instTerm (Term.rename Nat.succ rightSuccCode))
            codedOrdinalDomain) := by
        have hraw := lift (BProv_context_cons hrightSuccDomain)
        simpa [rename_subst_instTerm_codedOrdinalDomain] using hraw
      have hrightAdjoinD : BProv Ax_s D
          (hfAdjoinGraphTermAt
            (Term.rename Nat.succ rightSuccCode)
            (Term.rename Nat.succ rightCode)
            (Term.rename Nat.succ rightCode)) := by
        simpa [rename_hfAdjoinGraphTermAt] using
          (lift (BProv_context_cons hrightAdjoin))
      have haddPredD : BProv Ax_s D
          (hfAddGraphTermAt
            (Term.rename Nat.succ predOut)
            (Term.rename Nat.succ leftCode)
            (Term.rename Nat.succ rightCode)) := by
        simpa [rename_hfAddGraphTermAt] using
          (lift (BProv_context_cons haddPred))
      have haddOutD : BProv Ax_s D
          (hfAddGraphTermAt
            (Term.rename Nat.succ out)
            (Term.rename Nat.succ leftCode)
            (Term.rename Nat.succ rightSuccCode)) := by
        simpa [rename_hfAddGraphTermAt] using (lift haddOut)
      have hsumPredD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.rename Nat.succ
              (Term.add leftRaw rightRaw))
            (Term.rename Nat.succ predOut)) := by
        simpa [rename_ordinalCodeGraphTermAt] using
          (lift (BProv_context_cons hsumPred))
      have haddKnown : BProv Ax_s D
          (hfAddGraphTermAt
            (Term.var 0)
            (Term.rename Nat.succ leftCode)
            (Term.rename Nat.succ rightSuccCode)) :=
        BProv_Ax_s_hfAddGraphTermAt_succ_right
          hrightDomainD hrightAdjoinD
          (by simpa [body] using hadjoin) haddPredD
      have houtEq : BProv Ax_s D
          (eq (Term.rename Nat.succ out) (Term.var 0)) :=
        BProv_Ax_s_hfAddGraphTermAt_functional
          hrightSuccDomainD haddOutD haddKnown
      have hsumSuccD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.succ
              (Term.rename Nat.succ
                (Term.add leftRaw rightRaw)))
            (Term.var 0)) :=
        ordinalCodeGraphSuccClosure hsumPredD
          (by simpa [body] using hadjoin)
      have haddSuccD : BProv Ax_s D
          (eq
            (Term.rename Nat.succ
              (Term.add leftRaw (Term.succ rightRaw)))
            (Term.succ
              (Term.rename Nat.succ
                (Term.add leftRaw rightRaw)))) := by
        simpa [rename, Term.rename] using
          (lift (BProv_context_cons haddSucc))
      have hresult := BProv_ordinalCodeGraphTermAt_congr
        (BProv_eqSym haddSuccD) (BProv_eqSym houtEq) hsumSuccD
      simpa [rename_ordinalCodeGraphTermAt] using hresult
    exact BProv_exE_of_sentences
      (B := Ax_s) Ax_s_sentences
      (G := C) (a := body)
      (c := ordinalCodeGraphTermAt
        (Term.add leftRaw (Term.succ rightRaw)) out)
      (by simpa [hfAdjoinExistsTermAt, body] using hex)
      (by simpa [D] using hinner)
  have hreverse : BProv Ax_s G
      (imp
        (ordinalCodeGraphTermAt
          (Term.add leftRaw (Term.succ rightRaw)) out)
        (hfAddGraphTermAt out leftCode rightSuccCode)) := by
    apply BProv_impI
    let C : List Formula :=
      ordinalCodeGraphTermAt
        (Term.add leftRaw (Term.succ rightRaw)) out :: G
    have htarget : BProv Ax_s C
        (ordinalCodeGraphTermAt
          (Term.add leftRaw (Term.succ rightRaw)) out) :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hsumSucc : BProv Ax_s C
        (ordinalCodeGraphTermAt
          (Term.succ (Term.add leftRaw rightRaw)) out) :=
      BProv_ordinalCodeGraphTermAt_congr_raw
        (BProv_context_cons haddSucc) htarget
    have hstep :=
      BProv_Ax_s_hfAdjoinGraphTermAt_iff_ordinalCodeGraphTermAt_succ
        ordinalCodeGraphSuccClosure ordinalCodeGraphFunctional
        (G := C) (codedOut := out)
        (BProv_context_cons
          (a := ordinalCodeGraphTermAt
            (Term.add leftRaw (Term.succ rightRaw)) out)
          hsumPred)
    have hstepReverse : BProv Ax_s C
        (imp
          (ordinalCodeGraphTermAt
            (Term.succ (Term.add leftRaw rightRaw)) out)
          (hfAdjoinGraphTermAt out predOut predOut)) := by
      simpa [iffForm] using BProv_andE2 hstep
    have houtAdjoin : BProv Ax_s C
        (hfAdjoinGraphTermAt out predOut predOut) :=
      BProv_mp Ax_s C _ _ hstepReverse hsumSucc
    exact BProv_Ax_s_hfAddGraphTermAt_succ_right
      (BProv_context_cons hrightDomain)
      (BProv_context_cons hrightAdjoin)
      houtAdjoin (BProv_context_cons haddPred)
  exact BProv_iffForm_intro hforward hreverse

set_option maxHeartbeats 600000 in
theorem BProv_Ax_s_ordinalCodeAddOutputTermAt_succ
    {G : List Formula}
    {leftRaw leftCode rightRaw rightCode rightSuccCode : Term}
    (hright : BProv Ax_s G
      (ordinalCodeGraphTermAt rightRaw rightCode))
    (hrightSucc : BProv Ax_s G
      (ordinalCodeGraphTermAt (Term.succ rightRaw) rightSuccCode))
    (hih : BProv Ax_s G
      (ordinalCodeAddOutputTermAt
        leftRaw leftCode rightRaw rightCode)) :
    BProv Ax_s G
      (ordinalCodeAddOutputTermAt
        leftRaw leftCode (Term.succ rightRaw) rightSuccCode) := by
  let graphBody : Formula :=
    ordinalCodeGraphTermAt
      (Term.add
        (Term.rename Nat.succ leftRaw)
        (Term.rename Nat.succ rightRaw))
      (Term.var 0)
  have htotal : BProv Ax_s G (ex graphBody) := by
    simpa [graphBody, Term.rename] using
      (OrdinalCodeGraphProofs_total G
        (Term.add leftRaw rightRaw))
  let C : List Formula := graphBody :: G.map (rename Nat.succ)
  have hinner : BProv Ax_s C
      (rename Nat.succ
        (ordinalCodeAddOutputTermAt
          leftRaw leftCode (Term.succ rightRaw) rightSuccCode)) := by
    have hsumPred : BProv Ax_s C graphBody :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have lift : ∀ {phi : Formula}, BProv Ax_s G phi →
        BProv Ax_s C (rename Nat.succ phi) := by
      intro phi hphi
      simpa [C] using
        (BProv_rename_succ_context_cons_of_sentences
          (B := Ax_s) Ax_s_sentences
          (a := graphBody) hphi)
    have hrightC : BProv Ax_s C
        (ordinalCodeGraphTermAt
          (Term.rename Nat.succ rightRaw)
          (Term.rename Nat.succ rightCode)) := by
      simpa [rename_ordinalCodeGraphTermAt] using (lift hright)
    have hrightSuccC : BProv Ax_s C
        (ordinalCodeGraphTermAt
          (Term.succ (Term.rename Nat.succ rightRaw))
          (Term.rename Nat.succ rightSuccCode)) := by
      simpa [rename_ordinalCodeGraphTermAt, Term.rename] using
        (lift hrightSucc)
    have hihC : BProv Ax_s C
        (ordinalCodeAddOutputTermAt
          (Term.rename Nat.succ leftRaw)
          (Term.rename Nat.succ leftCode)
          (Term.rename Nat.succ rightRaw)
          (Term.rename Nat.succ rightCode)) := by
      simpa only [rename_ordinalCodeAddOutputTermAt] using
        (lift hih)
    have hpointRaw := BProv_allE
      (B := Ax_s) (G := C) (t := Term.var 0) hihC
    have hpoint : BProv Ax_s C
        (iffForm
          (hfAddGraphTermAt
            (Term.var 0)
            (Term.rename Nat.succ leftCode)
            (Term.rename Nat.succ rightCode))
          graphBody) := by
      simpa only [ordinalCodeAddOutputTermAt, iffForm,
        graphBody, subst_hfAddGraphTermAt,
        subst_ordinalCodeGraphTermAt,
        subst, instTerm, Term.subst,
        Term.upSubst,
        term_subst_instTerm_rename_succ] using hpointRaw
    have hpointReverse : BProv Ax_s C
        (imp graphBody
          (hfAddGraphTermAt
            (Term.var 0)
            (Term.rename Nat.succ leftCode)
            (Term.rename Nat.succ rightCode))) := by
      simpa [iffForm] using BProv_andE2 hpoint
    have haddPred : BProv Ax_s C
        (hfAddGraphTermAt
          (Term.var 0)
          (Term.rename Nat.succ leftCode)
          (Term.rename Nat.succ rightCode)) :=
      BProv_mp Ax_s C _ _ hpointReverse hsumPred
    let D : List Formula := C.map (rename Nat.succ)
    have hbody : BProv Ax_s D
        (iffForm
          (hfAddGraphTermAt
            (Term.var 0)
            (Term.rename (fun n ↦ n+2) leftCode)
            (Term.rename (fun n ↦ n+2) rightSuccCode))
          (ordinalCodeGraphTermAt
            (Term.add
              (Term.rename (fun n ↦ n+2) leftRaw)
              (Term.succ
                (Term.rename (fun n ↦ n+2) rightRaw)))
            (Term.var 0))) := by
      have liftC : ∀ {phi : Formula}, BProv Ax_s C phi →
          BProv Ax_s D (rename Nat.succ phi) := by
        intro phi hphi
        simpa [D] using
          (BProv_rename_of_sentences
            (B := Ax_s) Ax_s_sentences
            hphi Nat.succ)
      have hrightD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.rename (fun n ↦ n+2) rightRaw)
            (Term.rename (fun n ↦ n+2) rightCode)) := by
        simpa [rename_ordinalCodeGraphTermAt,
          Term.rename_comp, Function.comp_def,
          Nat.add_assoc] using (liftC hrightC)
      have hrightSuccD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.succ
              (Term.rename (fun n ↦ n+2) rightRaw))
            (Term.rename (fun n ↦ n+2) rightSuccCode)) := by
        simpa [rename_ordinalCodeGraphTermAt, Term.rename,
          Term.rename_comp, Function.comp_def,
          Nat.add_assoc] using (liftC hrightSuccC)
      have hsumPredD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.add
              (Term.rename (fun n ↦ n+2) leftRaw)
              (Term.rename (fun n ↦ n+2) rightRaw))
            (Term.var 1)) := by
        simpa [graphBody, rename_ordinalCodeGraphTermAt,
          Term.rename,
          Term.rename_comp, Function.comp_def,
          Nat.add_assoc] using (liftC hsumPred)
      have haddPredD : BProv Ax_s D
          (hfAddGraphTermAt
            (Term.var 1)
            (Term.rename (fun n ↦ n+2) leftCode)
            (Term.rename (fun n ↦ n+2) rightCode)) := by
        simpa [rename_hfAddGraphTermAt,
          Term.rename,
          Term.rename_comp, Function.comp_def,
          Nat.add_assoc] using (liftC haddPred)
      exact BProv_Ax_s_ordinalCodeAddCore_succ_of_pred
        hrightD hrightSuccD hsumPredD haddPredD
    have hall := BProv_allI_of_sentences
      (B := Ax_s) (G := C)
      Ax_s_sentences hbody
    have hall' : BProv Ax_s C
        (ordinalCodeAddOutputTermAt
          (Term.rename Nat.succ leftRaw)
          (Term.rename Nat.succ leftCode)
          (Term.succ (Term.rename Nat.succ rightRaw))
          (Term.rename Nat.succ rightSuccCode)) := by
      simpa [ordinalCodeAddOutputTermAt, D,
        Term.rename, Term.rename_comp, Function.comp_def,
        Nat.add_assoc] using hall
    simpa only [rename_ordinalCodeAddOutputTermAt,
      Term.rename] using hall'
  exact BProv_exE_of_sentences
    (B := Ax_s) Ax_s_sentences
    (G := G) (a := graphBody)
    (c := ordinalCodeAddOutputTermAt
      leftRaw leftCode (Term.succ rightRaw) rightSuccCode)
    htotal (by simpa [C] using hinner)

theorem BProv_Ax_s_ordinalCodeAddPointTermAt_of_graph
    {G : List Formula}
    {leftRaw leftCode rightRaw rightCode : Term}
    (hpoint : BProv Ax_s G
      (ordinalCodeAddPointTermAt
        leftRaw leftCode rightRaw))
    (hgraph : BProv Ax_s G
      (ordinalCodeGraphTermAt rightRaw rightCode)) :
    BProv Ax_s G
      (ordinalCodeAddOutputTermAt
        leftRaw leftCode rightRaw rightCode) := by
  have himpRaw := BProv_allE
    (B := Ax_s) (G := G) (t := rightCode) hpoint
  have himp : BProv Ax_s G
      (imp
        (ordinalCodeGraphTermAt rightRaw rightCode)
        (ordinalCodeAddOutputTermAt
          leftRaw leftCode rightRaw rightCode)) := by
    simpa [ordinalCodeAddPointTermAt,
      subst_ordinalCodeGraphTermAt,
      subst_ordinalCodeAddOutputTermAt,
      subst, instTerm, Term.subst,
      term_subst_instTerm_rename_succ] using himpRaw
  exact BProv_mp Ax_s G _ _ himp hgraph

set_option maxHeartbeats 600000 in
theorem BProv_Ax_s_ordinalCodeAddPointTermAt_succ
    {G : List Formula} {leftRaw leftCode rightRaw : Term}
    (hih : BProv Ax_s G
      (ordinalCodeAddPointTermAt
        leftRaw leftCode rightRaw)) :
    BProv Ax_s G
      (ordinalCodeAddPointTermAt
        leftRaw leftCode (Term.succ rightRaw)) := by
  let rightSuccGraph : Formula :=
    ordinalCodeGraphTermAt
      (Term.succ (Term.rename Nat.succ rightRaw))
      (Term.var 0)
  let Q : List Formula := G.map (rename Nat.succ)
  have hbody : BProv Ax_s Q
      (imp rightSuccGraph
        (ordinalCodeAddOutputTermAt
          (Term.rename Nat.succ leftRaw)
          (Term.rename Nat.succ leftCode)
          (Term.succ (Term.rename Nat.succ rightRaw))
          (Term.var 0))) := by
    apply BProv_impI
    let C : List Formula := rightSuccGraph :: Q
    have hrightSucc : BProv Ax_s C rightSuccGraph :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    let predBody : Formula :=
      ordinalCodeGraphTermAt
        (Term.rename (fun n ↦ n+2) rightRaw)
        (Term.var 0)
    have htotal : BProv Ax_s C (ex predBody) := by
      simpa [predBody, Term.rename_comp,
        Function.comp_def, Nat.add_assoc] using
        (OrdinalCodeGraphProofs_total C
          (Term.rename Nat.succ rightRaw))
    let D : List Formula := predBody :: C.map (rename Nat.succ)
    have hinner : BProv Ax_s D
        (rename Nat.succ
          (ordinalCodeAddOutputTermAt
            (Term.rename Nat.succ leftRaw)
            (Term.rename Nat.succ leftCode)
            (Term.succ (Term.rename Nat.succ rightRaw))
            (Term.var 0))) := by
      have hpred : BProv Ax_s D predBody :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D])
      have hrightSuccD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.succ
              (Term.rename (fun n ↦ n+2) rightRaw))
            (Term.var 1)) := by
        have hren := BProv_rename_of_sentences
          (B := Ax_s) Ax_s_sentences
          hrightSucc Nat.succ
        simpa [D, rightSuccGraph,
          rename_ordinalCodeGraphTermAt, Term.rename,
          Term.rename_comp, Function.comp_def,
          Nat.add_assoc] using
            (BProv_context_cons (a := predBody) hren)
      have hihQ : BProv Ax_s Q
          (ordinalCodeAddPointTermAt
            (Term.rename Nat.succ leftRaw)
            (Term.rename Nat.succ leftCode)
            (Term.rename Nat.succ rightRaw)) := by
        have hren := BProv_rename_of_sentences
          (B := Ax_s) Ax_s_sentences
          hih Nat.succ
        simpa [Q, rename_ordinalCodeAddPointTermAt] using hren
      have hihC : BProv Ax_s C
          (ordinalCodeAddPointTermAt
            (Term.rename Nat.succ leftRaw)
            (Term.rename Nat.succ leftCode)
            (Term.rename Nat.succ rightRaw)) :=
        BProv_context_cons (a := rightSuccGraph) hihQ
      have hihD : BProv Ax_s D
          (ordinalCodeAddPointTermAt
            (Term.rename (fun n ↦ n+2) leftRaw)
            (Term.rename (fun n ↦ n+2) leftCode)
            (Term.rename (fun n ↦ n+2) rightRaw)) := by
        have hren := BProv_rename_succ_context_cons_of_sentences
          (B := Ax_s) Ax_s_sentences
          (a := predBody) hihC
        simpa [D, C, Q,
          rename_ordinalCodeAddPointTermAt,
          Term.rename_comp, Function.comp_def,
          Nat.add_assoc] using hren
      have houtputPred :=
        BProv_Ax_s_ordinalCodeAddPointTermAt_of_graph
          hihD (by simpa [predBody] using hpred)
      have houtputSucc :=
        BProv_Ax_s_ordinalCodeAddOutputTermAt_succ
          (by simpa [predBody] using hpred)
          hrightSuccD houtputPred
      simpa only [rename_ordinalCodeAddOutputTermAt,
        Term.rename, Term.rename_comp, Function.comp_def,
        Nat.add_assoc] using houtputSucc
    exact BProv_exE_of_sentences
      (B := Ax_s) Ax_s_sentences
      (G := C) (a := predBody)
      (c := ordinalCodeAddOutputTermAt
        (Term.rename Nat.succ leftRaw)
        (Term.rename Nat.succ leftCode)
        (Term.succ (Term.rename Nat.succ rightRaw))
        (Term.var 0))
      htotal (by simpa [D] using hinner)
  have hall := BProv_allI_of_sentences
    (B := Ax_s) (G := G)
    Ax_s_sentences hbody
  simpa [ordinalCodeAddPointTermAt,
    rightSuccGraph, Q, Term.rename] using hall

attribute [local irreducible]
  hfAddGraphTermAt
  ordinalCodeAddOutputTermAt
  ordinalCodeAddPointTermAt

set_option maxHeartbeats 400000 in
theorem BProv_Ax_s_all_ordinalCodeAddPoint
    {G : List Formula} {leftRaw leftCode : Term}
    (hleft : BProv Ax_s G
      (ordinalCodeGraphTermAt leftRaw leftCode)) :
    BProv Ax_s G
      (all
        (ordinalCodeAddPointTermAt
          (Term.rename Nat.succ leftRaw)
          (Term.rename Nat.succ leftCode)
          (Term.var 0))) := by
  let phi : Formula :=
    ordinalCodeAddPointTermAt
      (Term.rename Nat.succ leftRaw)
      (Term.rename Nat.succ leftCode)
      (Term.var 0)
  have hzero : BProv Ax_s G (subst substZero phi) := by
    have hbase :=
      BProv_Ax_s_ordinalCodeAddPointTermAt_zero
        (G := G) (leftRaw := leftRaw) (leftCode := leftCode) hleft
    change BProv Ax_s G
      (subst substZero
        (ordinalCodeAddPointTermAt
          (Term.rename Nat.succ leftRaw)
          (Term.rename Nat.succ leftCode)
          (Term.var 0)))
    rw [subst_ordinalCodeAddPointTermAt]
    simpa only [substZero, Term.subst,
      term_substZero_rename_succ] using hbase
  let Q : List Formula := G.map (rename Nat.succ)
  have hsuccImp : BProv Ax_s Q
      (imp phi (subst substSuccVar phi)) := by
    let C : List Formula := phi :: Q
    have hihRaw : BProv Ax_s C phi :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hih : BProv Ax_s C
        (ordinalCodeAddPointTermAt
          (Term.rename Nat.succ leftRaw)
          (Term.rename Nat.succ leftCode)
          (Term.var 0)) := by
      simpa only [phi] using hihRaw
    have hnext :=
      BProv_Ax_s_ordinalCodeAddPointTermAt_succ
        (G := C)
        (leftRaw := Term.rename Nat.succ leftRaw)
        (leftCode := Term.rename Nat.succ leftCode)
        (rightRaw := Term.var 0) hih
    have hnextSub : BProv Ax_s C (subst substSuccVar phi) := by
      change BProv Ax_s C
        (subst substSuccVar
          (ordinalCodeAddPointTermAt
            (Term.rename Nat.succ leftRaw)
            (Term.rename Nat.succ leftCode)
            (Term.var 0)))
      rw [subst_ordinalCodeAddPointTermAt]
      simpa only [substSuccVar, Term.subst,
        term_substSuccVar_rename_succ] using hnext
    exact BProv_impI (B := Ax_s) (G := Q)
      (a := phi) (b := subst substSuccVar phi)
      (by simpa only [C] using hnextSub)
  have hsucc : BProv Ax_s G
      (all (imp phi (subst substSuccVar phi))) :=
    BProv_allI_of_sentences
      (B := Ax_s) (G := G)
      Ax_s_sentences hsuccImp
  simpa only [phi] using
    (BProv_Ax_s_induction_rule (G := G) (phi := phi) hzero hsucc)

theorem BProv_Ax_s_ordinalCodeAddPointTermAt
    {G : List Formula} {leftRaw leftCode rightRaw : Term}
    (hleft : BProv Ax_s G
      (ordinalCodeGraphTermAt leftRaw leftCode)) :
    BProv Ax_s G
      (ordinalCodeAddPointTermAt
        leftRaw leftCode rightRaw) := by
  have hall := BProv_Ax_s_all_ordinalCodeAddPoint hleft
  have hraw := BProv_allE
    (B := Ax_s) (G := G) (t := rightRaw) hall
  rw [subst_ordinalCodeAddPointTermAt] at hraw
  simpa only [instTerm, Term.subst,
    term_subst_instTerm_rename_succ] using hraw

theorem BProv_Ax_s_ordinalCodeAddTermAt
    {G : List Formula}
    {leftRaw leftCode rightRaw rightCode out : Term}
    (hleft : BProv Ax_s G
      (ordinalCodeGraphTermAt leftRaw leftCode))
    (hright : BProv Ax_s G
      (ordinalCodeGraphTermAt rightRaw rightCode)) :
    BProv Ax_s G
      (iffForm
        (hfAddGraphTermAt out leftCode rightCode)
        (ordinalCodeGraphTermAt
          (Term.add leftRaw rightRaw) out)) := by
  have hpoint :=
    BProv_Ax_s_ordinalCodeAddPointTermAt
      (rightRaw := rightRaw) hleft
  have houtput :=
    BProv_Ax_s_ordinalCodeAddPointTermAt_of_graph
      hpoint hright
  have houtput' : BProv Ax_s G
      (all
        (iffForm
          (hfAddGraphTermAt
            (Term.var 0)
            (Term.rename Nat.succ leftCode)
            (Term.rename Nat.succ rightCode))
          (ordinalCodeGraphTermAt
            (Term.rename Nat.succ
              (Term.add leftRaw rightRaw))
            (Term.var 0)))) := by
    simpa only [ordinalCodeAddOutputTermAt] using houtput
  have hraw := BProv_allE
    (B := Ax_s) (G := G) (t := out) houtput'
  simpa only [iffForm, subst,
    subst_hfAddGraphTermAt,
    subst_ordinalCodeGraphTermAt,
    instTerm, Term.subst, Term.upSubst,
    term_subst_instTerm_rename_succ] using hraw

theorem ordinalCodeAddCoreCompatibility :
    OrdinalCodeAddCoreCompatibility := by
  intro G leftRaw rightRaw codedOut hleft hright
  have hiff := BProv_Ax_s_ordinalCodeAddTermAt
    (out := Term.var (codedOut+2)) hleft hright
  simpa only [compositeAddCoreAt_eq_termAt] using hiff

theorem BProv_Ax_s_term_graph_add_forward_of_shifted_operands
    (G : List Formula) (a b leftRaw rightRaw : Term)
    (codedMap : Nat → Nat) (codedOut : Nat)
    (hleft : BProv Ax_s
      ((G.map (rename Nat.succ)).map (rename Nat.succ))
      (iffForm
        (compositeTermGraphAt 1 (fun n ↦ codedMap n + 2) a)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+2) leftRaw) (Term.var 1))))
    (hright : BProv Ax_s
      ((G.map (rename Nat.succ)).map (rename Nat.succ))
      (iffForm
        (compositeTermGraphAt 0 (fun n ↦ codedMap n + 2) b)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+2) rightRaw) (Term.var 0)))) :
    BProv Ax_s G
      (imp
        (compositeTermGraphAt codedOut codedMap (Term.add a b))
        (ordinalCodeGraphTermAt
          (Term.add leftRaw rightRaw) (Term.var codedOut))) := by
  let composite : Formula :=
    compositeTermGraphAt codedOut codedMap (Term.add a b)
  let target : Formula :=
    ordinalCodeGraphTermAt
      (Term.add leftRaw rightRaw) (Term.var codedOut)
  let leftComposite : Formula :=
    compositeTermGraphAt 1 (fun n ↦ codedMap n + 2) a
  let rightComposite : Formula :=
    compositeTermGraphAt 0 (fun n ↦ codedMap n + 2) b
  let core : Formula := compositeAddCoreAt codedOut
  let body : Formula :=
    and leftComposite (and rightComposite core)
  apply BProv_impI
  let C : List Formula := composite :: G
  have hcomposite : BProv Ax_s C composite :=
    BProv_ass (B := Ax_s) (G := C) (by simp [C])
  have hex : BProv Ax_s C (ex (ex body)) := by
    simpa [composite, body, leftComposite, rightComposite, core,
      compositeTermGraphAt_add_normalForm] using hcomposite
  let inner : Formula := ex body
  let D : List Formula :=
    body :: (inner :: C.map (rename Nat.succ)).map (rename Nat.succ)
  have hopened : BProv Ax_s D
      (rename Nat.succ (rename Nat.succ target)) := by
    have hbody : BProv Ax_s D body :=
      BProv_ass (B := Ax_s) (G := D) (by simp [D])
    have hleftComposite : BProv Ax_s D leftComposite :=
      BProv_andE1 hbody
    have htail := BProv_andE2 hbody
    have hrightComposite : BProv Ax_s D rightComposite :=
      BProv_andE1 htail
    have hcore : BProv Ax_s D core :=
      BProv_andE2 htail
    -- `hleft` and `hright` are already shifted through both witnesses.  The
    -- opened context differs only by this explicit local prefix.
    have liftShifted : ∀ {phi : Formula},
        BProv Ax_s
          ((G.map (rename Nat.succ)).map (rename Nat.succ)) phi →
        BProv Ax_s D phi := by
      intro phi hphi
      simpa [D, C, List.map_map] using
        (BProv_context_prefix (B := Ax_s)
          [body, rename Nat.succ inner,
            rename Nat.succ (rename Nat.succ composite)] hphi)
    have hleftD := liftShifted hleft
    have hleftForward : BProv Ax_s D
        (imp leftComposite
          (ordinalCodeGraphTermAt
            (Term.rename (fun n ↦ n+2) leftRaw)
            (Term.var 1))) := by
      simpa [iffForm, leftComposite] using BProv_andE1 hleftD
    have hleftGraph := BProv_mp Ax_s D _ _
      hleftForward hleftComposite
    have hrightD := liftShifted hright
    have hrightForward : BProv Ax_s D
        (imp rightComposite
          (ordinalCodeGraphTermAt
            (Term.rename (fun n ↦ n+2) rightRaw)
            (Term.var 0))) := by
      simpa [iffForm, rightComposite] using BProv_andE1 hrightD
    have hrightGraph := BProv_mp Ax_s D _ _
      hrightForward hrightComposite
    have hcoreIff := ordinalCodeAddCoreCompatibility
      (G := D)
      (leftRaw := Term.rename (fun n ↦ n+2) leftRaw)
      (rightRaw := Term.rename (fun n ↦ n+2) rightRaw)
      (codedOut := codedOut) hleftGraph hrightGraph
    have hcoreForward : BProv Ax_s D
        (imp core
          (ordinalCodeGraphTermAt
            (Term.add
              (Term.rename (fun n ↦ n+2) leftRaw)
              (Term.rename (fun n ↦ n+2) rightRaw))
            (Term.var (codedOut+2)))) := by
      simpa [iffForm, core] using BProv_andE1 hcoreIff
    have htarget := BProv_mp Ax_s D _ _ hcoreForward hcore
    simpa [target, rename_ordinalCodeGraphTermAt,
      Term.rename, Term.rename_comp,
      Function.comp_def, Nat.add_assoc] using htarget
  exact BProv_two_exE_of_sentences
    (B := Ax_s) Ax_s_sentences
    (G := C) (body := body) (target := target)
    hex (by simpa [D, inner] using hopened)

theorem BProv_Ax_s_term_graph_add_reverse_of_shifted_operands
    (G : List Formula) (a b leftRaw rightRaw : Term)
    (codedMap : Nat → Nat) (codedOut : Nat)
    (hleft : BProv Ax_s
      ((G.map (rename Nat.succ)).map (rename Nat.succ))
      (iffForm
        (compositeTermGraphAt 1 (fun n ↦ codedMap n + 2) a)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+2) leftRaw) (Term.var 1))))
    (hright : BProv Ax_s
      ((G.map (rename Nat.succ)).map (rename Nat.succ))
      (iffForm
        (compositeTermGraphAt 0 (fun n ↦ codedMap n + 2) b)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+2) rightRaw) (Term.var 0)))) :
    BProv Ax_s G
      (imp
        (ordinalCodeGraphTermAt
          (Term.add leftRaw rightRaw) (Term.var codedOut))
        (compositeTermGraphAt codedOut codedMap (Term.add a b))) := by
  let composite : Formula :=
    compositeTermGraphAt codedOut codedMap (Term.add a b)
  let target : Formula :=
    ordinalCodeGraphTermAt
      (Term.add leftRaw rightRaw) (Term.var codedOut)
  let leftComposite : Formula :=
    compositeTermGraphAt 1 (fun n ↦ codedMap n + 2) a
  let rightComposite : Formula :=
    compositeTermGraphAt 0 (fun n ↦ codedMap n + 2) b
  let core : Formula := compositeAddCoreAt codedOut
  let body : Formula :=
    and leftComposite (and rightComposite core)
  apply BProv_impI
  let C : List Formula := target :: G
  have htarget : BProv Ax_s C target :=
    BProv_ass (B := Ax_s) (G := C) (by simp [C])
  let leftGraphBody : Formula :=
    ordinalCodeGraphTermAt
      (Term.rename Nat.succ leftRaw) (Term.var 0)
  have hleftTotal : BProv Ax_s C (ex leftGraphBody) := by
    simpa [leftGraphBody] using
      (OrdinalCodeGraphProofs_total C leftRaw)
  let L : List Formula := leftGraphBody :: C.map (rename Nat.succ)
  let rightGraphBody : Formula :=
    ordinalCodeGraphTermAt
      (Term.rename (fun n ↦ n+2) rightRaw) (Term.var 0)
  have hrightTotal : BProv Ax_s L (ex rightGraphBody) := by
    simpa [rightGraphBody, Term.rename_comp,
      Function.comp_def, Nat.add_assoc] using
      (OrdinalCodeGraphProofs_total L
        (Term.rename Nat.succ rightRaw))
  let R : List Formula := rightGraphBody :: L.map (rename Nat.succ)
  have hrenamedComposite : BProv Ax_s R
      (rename Nat.succ (rename Nat.succ composite)) := by
    have hrightGraph : BProv Ax_s R rightGraphBody :=
      BProv_ass (B := Ax_s) (G := R) (by simp [R])
    have hleftGraphL : BProv Ax_s L leftGraphBody :=
      BProv_ass (B := Ax_s) (G := L) (by simp [L])
    have hleftGraph : BProv Ax_s R
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+2) leftRaw)
          (Term.var 1)) := by
      have hren := BProv_rename_succ_context_cons_of_sentences
        (B := Ax_s) Ax_s_sentences
        (a := rightGraphBody) hleftGraphL
      simpa [R, leftGraphBody,
        rename_ordinalCodeGraphTermAt,
        Term.rename,
        Term.rename_comp, Function.comp_def,
        Nat.add_assoc] using hren
    have htargetR : BProv Ax_s R
        (ordinalCodeGraphTermAt
          (Term.add
            (Term.rename (fun n ↦ n+2) leftRaw)
            (Term.rename (fun n ↦ n+2) rightRaw))
          (Term.var (codedOut+2))) := by
      have htargetLift := BProv_lift_two_contexts_of_sentences
        (B := Ax_s) Ax_s_sentences
        (outer := leftGraphBody) (inner := rightGraphBody) htarget
      simpa [R, L, C, target,
        rename_ordinalCodeGraphTermAt, Term.rename,
        Term.rename_comp, Function.comp_def,
        Nat.add_assoc] using htargetLift
    have liftShifted : ∀ {phi : Formula},
        BProv Ax_s
          ((G.map (rename Nat.succ)).map (rename Nat.succ)) phi →
        BProv Ax_s R phi := by
      intro phi hphi
      simpa [R, L, C, List.map_map] using
        (BProv_context_prefix (B := Ax_s)
          [rightGraphBody, rename Nat.succ leftGraphBody,
            rename Nat.succ (rename Nat.succ target)] hphi)
    have hleftR := liftShifted hleft
    have hleftReverse : BProv Ax_s R
        (imp
          (ordinalCodeGraphTermAt
            (Term.rename (fun n ↦ n+2) leftRaw) (Term.var 1))
          leftComposite) := by
      simpa [iffForm, leftComposite] using BProv_andE2 hleftR
    have hleftComposite : BProv Ax_s R leftComposite :=
      BProv_mp Ax_s R _ _ hleftReverse hleftGraph
    have hrightR := liftShifted hright
    have hrightReverse : BProv Ax_s R
        (imp
          (ordinalCodeGraphTermAt
            (Term.rename (fun n ↦ n+2) rightRaw) (Term.var 0))
          rightComposite) := by
      simpa [iffForm, rightComposite] using BProv_andE2 hrightR
    have hrightComposite : BProv Ax_s R rightComposite :=
      BProv_mp Ax_s R _ _ hrightReverse hrightGraph
    have hcoreIff := ordinalCodeAddCoreCompatibility
      (G := R)
      (leftRaw := Term.rename (fun n ↦ n+2) leftRaw)
      (rightRaw := Term.rename (fun n ↦ n+2) rightRaw)
      (codedOut := codedOut) hleftGraph hrightGraph
    have hcoreReverse : BProv Ax_s R
        (imp
          (ordinalCodeGraphTermAt
            (Term.add
              (Term.rename (fun n ↦ n+2) leftRaw)
              (Term.rename (fun n ↦ n+2) rightRaw))
            (Term.var (codedOut+2)))
          core) := by
      simpa [iffForm, core] using BProv_andE2 hcoreIff
    have hcore : BProv Ax_s R core :=
      BProv_mp Ax_s R _ _ hcoreReverse htargetR
    have hbody : BProv Ax_s R body :=
      BProv_andI hleftComposite
        (BProv_andI hrightComposite hcore)
    change BProv Ax_s R
      (rename Nat.succ (rename Nat.succ
        (compositeTermGraphAt codedOut codedMap (Term.add a b))))
    rw [compositeTermGraphAt_add_normalForm]
    apply BProv_exI (t := Term.var 1)
    apply BProv_exI (t := Term.var 0)
    rw [subst_instTerm_var_zero_up_var_one_rename_up_up_succ_twice]
    exact hbody
  have hcompositeL : BProv Ax_s L (rename Nat.succ composite) :=
    BProv_exE_of_sentences
      (B := Ax_s) Ax_s_sentences
      (G := L) (a := rightGraphBody)
      (c := rename Nat.succ composite)
      hrightTotal (by simpa [R] using hrenamedComposite)
  have hcompositeC : BProv Ax_s C composite :=
    BProv_exE_of_sentences
      (B := Ax_s) Ax_s_sentences
      (G := C) (a := leftGraphBody) (c := composite)
      hleftTotal (by simpa [L] using hcompositeL)
  exact hcompositeC

theorem BProv_Ax_s_term_graph_add_of_shifted_operands
    (G : List Formula) (a b leftRaw rightRaw : Term)
    (codedMap : Nat → Nat) (codedOut : Nat)
    (hleft : BProv Ax_s
      ((G.map (rename Nat.succ)).map (rename Nat.succ))
      (iffForm
        (compositeTermGraphAt 1 (fun n ↦ codedMap n + 2) a)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+2) leftRaw) (Term.var 1))))
    (hright : BProv Ax_s
      ((G.map (rename Nat.succ)).map (rename Nat.succ))
      (iffForm
        (compositeTermGraphAt 0 (fun n ↦ codedMap n + 2) b)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+2) rightRaw) (Term.var 0)))) :
    BProv Ax_s G
      (iffForm
        (compositeTermGraphAt codedOut codedMap (Term.add a b))
        (ordinalCodeGraphTermAt
          (Term.add leftRaw rightRaw) (Term.var codedOut))) := by
  have hforward :=
    BProv_Ax_s_term_graph_add_forward_of_shifted_operands
      G a b leftRaw rightRaw codedMap codedOut hleft hright
  have hreverse :=
    BProv_Ax_s_term_graph_add_reverse_of_shifted_operands
      G a b leftRaw rightRaw codedMap codedOut hleft hright
  exact BProv_iffForm_intro hforward hreverse

/-- Addition preserves the complete ordinal-code term-graph property. -/
theorem ordinalCodeTermGraphProof_add
    (a b : Term)
    (iha : OrdinalCodeTermGraphProof a)
    (ihb : OrdinalCodeTermGraphProof b) :
    OrdinalCodeTermGraphProof (Term.add a b) := by
  intro G rawMap codedMap codedOut hcode
  let G₂ : List Formula :=
    (G.map (rename Nat.succ)).map (rename Nat.succ)
  let rawMap₂ : Nat → Nat := fun n ↦ rawMap n + 2
  let codedMap₂ : Nat → Nat := fun n ↦ codedMap n + 2
  have hcode₂ : ∀ n, Term.Free n (Term.add a b) →
      BProv Ax_s G₂
        (ordinalCodeGraphAt (rawMap₂ n) (codedMap₂ n)) := by
    intro n hn
    have h₀ := hcode n hn
    have h₂ := BProv_iterRenameSucc_of_sentences
      (B := Ax_s) Ax_s_sentences
      2 h₀
    simpa [G₂, rawMap₂, codedMap₂, iterRenameContextSucc, iterRenameSucc,
      ordinalCodeGraphAt,
      rename_ordinalCodeGraphTermAt, Term.rename,
      List.map_map, Function.comp_def, Nat.add_assoc] using h₂
  have hleftCode : ∀ n, Term.Free n a →
      BProv Ax_s G₂
        (ordinalCodeGraphAt (rawMap₂ n) (codedMap₂ n)) :=
    fun n hn ↦ hcode₂ n (Or.inl hn)
  have hrightCode : ∀ n, Term.Free n b →
      BProv Ax_s G₂
        (ordinalCodeGraphAt (rawMap₂ n) (codedMap₂ n)) :=
    fun n hn ↦ hcode₂ n (Or.inr hn)
  have hleft₀ := iha G₂ rawMap₂ codedMap₂ 1 hleftCode
  have hleft : BProv Ax_s G₂
      (iffForm
        (compositeTermGraphAt 1 (fun n ↦ codedMap n + 2) a)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+2) (Term.rename rawMap a))
          (Term.var 1))) := by
    simpa [rawMap₂, codedMap₂,
      Term.rename_comp, Function.comp_def,
      Nat.add_assoc] using hleft₀
  have hright₀ := ihb G₂ rawMap₂ codedMap₂ 0 hrightCode
  have hright : BProv Ax_s G₂
      (iffForm
        (compositeTermGraphAt 0 (fun n ↦ codedMap n + 2) b)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+2) (Term.rename rawMap b))
          (Term.var 0))) := by
    simpa [rawMap₂, codedMap₂,
      Term.rename_comp, Function.comp_def,
      Nat.add_assoc] using hright₀
  have hadd := BProv_Ax_s_term_graph_add_of_shifted_operands
    G a b (Term.rename rawMap a) (Term.rename rawMap b)
    codedMap codedOut
    (by simpa [G₂] using hleft)
    (by simpa [G₂] using hright)
  simpa [Term.rename] using hadd

theorem ordinalCodeTermAddCompatibility :
    OrdinalCodeTermAddCompatibility := by
  intro a b iha ihb
  exact ordinalCodeTermGraphProof_add a b iha ihb

/-- Multiplication-constructor interface for the complete term-graph
induction. -/
def OrdinalCodeTermMulCompatibility : Prop :=
  ∀ a b,
    OrdinalCodeTermGraphProof a →
    OrdinalCodeTermGraphProof b →
    OrdinalCodeTermGraphProof (Term.mul a b)

/-! ## Multiplication compatibility for ordinal-code term graphs -/
private def mulLeftShift : Nat → Nat
  | 0 => 1
  | n+1 => n+4

private def mulRightShift : Nat → Nat
  | 0 => 2
  | n+1 => n+4

theorem hfFormulaAt_mul_left_termGraph_eq_composite
    (codedOut : Nat) (codedMap : Nat → Nat) (t : Term) :
    hfFormulaAt
        (hfUpVarMap (hfUpVarMap (hfUpVarMap
          (codedTermSlotMap codedOut codedMap))))
        (AckermannHF.PAInHF.termGraphAt (fun n ↦ n+4) 1 t) =
      compositeTermGraphAt 1 (fun n ↦ codedMap n + 3) t := by
  let graph : Form :=
    AckermannHF.PAInHF.termGraphAt (fun n ↦ n+1) 0 t
  have hgraph : SetTheory.rename mulLeftShift graph =
      AckermannHF.PAInHF.termGraphAt (fun n ↦ n+4) 1 t := by
    simpa [graph, mulLeftShift] using
      (AckermannHF.PAInHF.termGraphAt_rename t
        (ρ := fun n ↦ n+1) (out := 0) (r := mulLeftShift))
  rw [← hgraph, hfFormulaAt_source_rename]
  apply hfFormulaAt_ext
  intro n
  cases n <;> rfl

theorem hfFormulaAt_mul_right_termGraph_eq_composite
    (codedOut : Nat) (codedMap : Nat → Nat) (t : Term) :
    hfFormulaAt
        (hfUpVarMap (hfUpVarMap (hfUpVarMap
          (codedTermSlotMap codedOut codedMap))))
        (AckermannHF.PAInHF.termGraphAt (fun n ↦ n+4) 2 t) =
      compositeTermGraphAt 2 (fun n ↦ codedMap n + 3) t := by
  let graph : Form :=
    AckermannHF.PAInHF.termGraphAt (fun n ↦ n+1) 0 t
  have hgraph : SetTheory.rename mulRightShift graph =
      AckermannHF.PAInHF.termGraphAt (fun n ↦ n+4) 2 t := by
    simpa [graph, mulRightShift] using
      (AckermannHF.PAInHF.termGraphAt_rename t
        (ρ := fun n ↦ n+1) (out := 0) (r := mulRightShift))
  rw [← hgraph, hfFormulaAt_source_rename]
  apply hfFormulaAt_ext
  intro n
  cases n <;> rfl

def compositeMulGraphAt
    (codedOut : Nat) (codedMap : Nat → Nat) : Formula :=
  hfFormulaAt
    (hfUpVarMap (hfUpVarMap (hfUpVarMap
      (codedTermSlotMap codedOut codedMap))))
    (SetTheory.Form.fAnd (SetTheory.Form.fEq 0 3)
      AckermannHF.PAInHF.mulGraph)

private def compositeMulCoreSlotMap (codedOut : Nat) : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n+3 => codedOut + n + 3

def compositeMulCoreAt (codedOut : Nat) : Formula :=
  hfFormulaAt (compositeMulCoreSlotMap codedOut)
    (SetTheory.Form.fAnd (SetTheory.Form.fEq 0 3)
      AckermannHF.PAInHF.mulGraph)

theorem compositeMulGraphAt_eq_core
    (codedOut : Nat) (codedMap : Nat → Nat) :
    compositeMulGraphAt codedOut codedMap =
      compositeMulCoreAt codedOut := by
  apply hfFormulaAt_ext_free
  intro n hn
  rcases hn with heq | hmul
  · rcases heq with rfl | rfl <;> rfl
  · rcases AckermannHF.PAInHF.mulGraph_free hmul with
      rfl | rfl | rfl <;> rfl

theorem compositeTermGraphAt_mul_normalForm
    (codedOut : Nat) (codedMap : Nat → Nat) (a b : Term) :
    compositeTermGraphAt codedOut codedMap (Term.mul a b) =
      ex (ex (ex
        (and
          (compositeTermGraphAt 1 (fun n ↦ codedMap n + 3) a)
          (and
            (compositeTermGraphAt 2 (fun n ↦ codedMap n + 3) b)
            (compositeMulCoreAt codedOut))))) := by
  rw [← compositeMulGraphAt_eq_core codedOut codedMap]
  simp [compositeTermGraphAt,
    AckermannHF.PAInHF.termGraphAt, hfFormulaAt,
    compositeMulGraphAt,
    hfFormulaAt_mul_left_termGraph_eq_composite,
    hfFormulaAt_mul_right_termGraph_eq_composite]

/-! ### Reverse-translated multiplication recursion laws -/

def hfMulGraphAt (out left right : Nat) : Formula :=
  hfFormulaAt (fun n : Nat ↦ n)
    (AckermannHF.PAInHF.mulGraphAt out left right)

def HF_mulZeroRightSentence : SetTheory.Form :=
  SetTheory.Form.fAll (SetTheory.Form.fAll (SetTheory.Form.fAll
    (SetTheory.Form.fImp
      (AckermannHF.HF_emptyAt 1)
      (SetTheory.Form.fImp
        (AckermannHF.HF_emptyAt 0)
        (AckermannHF.PAInHF.mulGraphAt 0 2 1)))))

theorem HF_mulZeroRightSentence_sentence :
    SetTheory.Sentence HF_mulZeroRightSentence := by
  intro i hi
  simp only [HF_mulZeroRightSentence, SetTheory.Free] at hi
  rcases hi with hright | hout | hmul
  · have := AckermannHF.HF_emptyAt_free hright
    omega
  · have := AckermannHF.HF_emptyAt_free hout
    omega
  · rcases AckermannHF.PAInHF.mulGraphAt_free hmul with
      h | h | h <;> omega

theorem BProv_HFFin_mulZeroRightSentence :
    SetTheory.BProv AckermannHF.HFFinAx_s []
      HF_mulZeroRightSentence := by
  apply SetTheory.completeness_inf AckermannHF.HFFinAx_s
  · exact AckermannHF.Sentences_HFFin
  · exact HF_mulZeroRightSentence_sentence
  · intro Dom mem v hHF
    let M := AckermannHF.firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
    intro left right out hright hout
    let e : Nat → Dom :=
      SetTheory.scons out (SetTheory.scons right (SetTheory.scons left v))
    have hrightM : SetTheory.Sat M.mem e
        (AckermannHF.HF_emptyAt 1) := by
      change SetTheory.Sat mem e (AckermannHF.HF_emptyAt 1)
      simpa [e, SetTheory.scons] using hright
    have houtM : SetTheory.Sat M.mem e
        (AckermannHF.HF_emptyAt 0) := by
      change SetTheory.Sat mem e (AckermannHF.HF_emptyAt 0)
      simpa [e, SetTheory.scons] using hout
    apply AckermannHF.PAInHF.mulGraphAt_zero_right_model
      M.toFirstOrderAdjunctionModel e 0 2 1
    · exact (AckermannHF.FirstOrderAdjunctionModel.HF_emptyAt_empty
        M.toFirstOrderAdjunctionModel e 0).mp houtM
    · exact (AckermannHF.FirstOrderAdjunctionModel.HF_emptyAt_empty
        M.toFirstOrderAdjunctionModel e 1).mp hrightM

theorem translateHFFormula_mulZeroRightSentence :
    translateHFFormula HF_mulZeroRightSentence =
      all (all (all
        (imp
          (hfEmptyAt 1)
          (imp
            (hfEmptyAt 0)
            (hfMulGraphAt 0 2 1))))) := by
  let ρ : Nat → Nat :=
    hfUpVarMap (hfUpVarMap
      (hfUpVarMap (fun n : Nat ↦ n)))
  change all (all (all
    (imp
      (hfFormulaAt ρ (AckermannHF.HF_emptyAt 1))
      (imp
        (hfFormulaAt ρ (AckermannHF.HF_emptyAt 0))
        (hfFormulaAt ρ
          (AckermannHF.PAInHF.mulGraphAt 0 2 1)))))) = _
  have hρ : ∀ n, ρ n = n := by
    intro n
    simp only [ρ, hfUpVarMap_id]
  rw [hfFormulaAt_ext _ hρ, hfFormulaAt_ext _ hρ,
    hfFormulaAt_ext _ hρ]
  rfl

theorem BProv_Ax_s_mulZeroRightSentence :
    BProv Ax_s []
      (all (all (all
        (imp
          (hfEmptyAt 1)
          (imp
            (hfEmptyAt 0)
            (hfMulGraphAt 0 2 1)))))) := by
  have htranslated : BProv translatedHFFinAx []
      (translateHFFormula HF_mulZeroRightSentence) :=
    BProv_translateHFFormula_of_BProv_HFFin
      BProv_HFFin_mulZeroRightSentence
  have hpa : BProv Ax_s []
      (translateHFFormula HF_mulZeroRightSentence) :=
    BProv_lift_translatedHFFinAx_to_PA
      (fun f hf ↦ BProv_Ax_s_of_translatedHFFinAx hf)
      htranslated
  rwa [translateHFFormula_mulZeroRightSentence] at hpa

def HF_mulSuccRightSentence : SetTheory.Form :=
  SetTheory.Form.fAll (SetTheory.Form.fAll (SetTheory.Form.fAll
    (SetTheory.Form.fAll (SetTheory.Form.fAll
      (SetTheory.Form.fImp
        (AckermannHF.HF_ordinalLikeAt 3)
        (SetTheory.Form.fImp
          (AckermannHF.HF_succAt 2 3)
          (SetTheory.Form.fImp
            (AckermannHF.PAInHF.mulGraphAt 1 4 3)
            (SetTheory.Form.fImp
              (AckermannHF.PAInHF.addGraphAt 0 1 4)
              (AckermannHF.PAInHF.mulGraphAt 0 4 2)))))))))

theorem HF_mulSuccRightSentence_sentence :
    SetTheory.Sentence HF_mulSuccRightSentence := by
  intro i hi
  simp only [HF_mulSuccRightSentence, SetTheory.Free] at hi
  rcases hi with hord | hright | hmul | hadd | hnext
  · have := AckermannHF.HF_ordinalLikeAt_free hord
    omega
  · rcases AckermannHF.HF_succAt_free hright with h | h <;> omega
  · rcases AckermannHF.PAInHF.mulGraphAt_free hmul with
      h | h | h <;> omega
  · rcases AckermannHF.PAInHF.addGraphAt_free hadd with
      h | h | h <;> omega
  · rcases AckermannHF.PAInHF.mulGraphAt_free hnext with
      h | h | h <;> omega

theorem BProv_HFFin_mulSuccRightSentence :
    SetTheory.BProv AckermannHF.HFFinAx_s []
      HF_mulSuccRightSentence := by
  apply SetTheory.completeness_inf AckermannHF.HFFinAx_s
  · exact AckermannHF.Sentences_HFFin
  · exact HF_mulSuccRightSentence_sentence
  · intro Dom mem v hHF
    let M := AckermannHF.firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
    intro left right rightSucc previous out
      hrightOrd hrightSucc hmul hadd
    let e : Nat → Dom :=
      SetTheory.scons out
        (SetTheory.scons previous
          (SetTheory.scons rightSucc
            (SetTheory.scons right (SetTheory.scons left v))))
    have hrightOrdM : SetTheory.Sat M.mem e
        (AckermannHF.HF_ordinalLikeAt 3) := by
      change SetTheory.Sat mem e (AckermannHF.HF_ordinalLikeAt 3)
      simpa [e, SetTheory.scons] using hrightOrd
    have hrightSuccM : SetTheory.Sat M.mem e
        (AckermannHF.HF_succAt 2 3) := by
      change SetTheory.Sat mem e (AckermannHF.HF_succAt 2 3)
      simpa [e, SetTheory.scons] using hrightSucc
    have hmulM : SetTheory.Sat M.mem e
        (AckermannHF.PAInHF.mulGraphAt 1 4 3) := by
      change SetTheory.Sat mem e
        (AckermannHF.PAInHF.mulGraphAt 1 4 3)
      simpa [e, SetTheory.scons] using hmul
    have haddM : SetTheory.Sat M.mem e
        (AckermannHF.PAInHF.addGraphAt 0 1 4) := by
      change SetTheory.Sat mem e
        (AckermannHF.PAInHF.addGraphAt 0 1 4)
      simpa [e, SetTheory.scons] using hadd
    let N := M.toFirstOrderAdjunctionModel
    rcases hmulM with ⟨f, hfSat, hpreviousSat⟩
    have hf : AckermannHF.PAInHF.MulRecApprox
        N (e 4) f (e 3) := by
      simpa [N, SetTheory.scons] using
        (AckermannHF.PAInHF.mulRecApproxAt_spec N
          (SetTheory.scons f e) 0 5 4).mp hfSat
    have hprevious : N.mem
        (AckermannHF.FirstOrderAdjunctionModel.kpair N (e 3) (e 1)) f := by
      simpa [N, SetTheory.scons] using
        (AckermannHF.FirstOrderAdjunctionModel.HF_pairMemAt_spec N
          (SetTheory.scons f e) 4 2 0).mp hpreviousSat
    rcases haddM with ⟨g, hgSat, houtSat⟩
    have hg : AckermannHF.FirstOrderAdjunctionModel.SuccRecApprox
        N (e 1) g (e 4) := by
      simpa [N, SetTheory.scons] using
        (AckermannHF.FirstOrderAdjunctionModel.HF_succRecApproxAt_spec N
          (SetTheory.scons g e) 0 2 5).mp hgSat
    have hout : N.mem
        (AckermannHF.FirstOrderAdjunctionModel.kpair N (e 4) (e 0)) g := by
      simpa [N, SetTheory.scons] using
        (AckermannHF.FirstOrderAdjunctionModel.HF_pairMemAt_spec N
          (SetTheory.scons g e) 5 1 0).mp houtSat
    apply AckermannHF.PAInHF.mulGraphAt_succ_right_of_mulRecApprox_model
      N e 0 4 2 3
      (f := f) (z := e 1) (g := g) (y := e 0)
    · exact (AckermannHF.HF_ordinalLikeAt_spec e 3).mp hrightOrdM
    · exact (AckermannHF.FirstOrderAdjunctionModel.HF_succAt_spec
        N e 2 3).mp hrightSuccM
    · rfl
    · exact hf
    · exact hprevious
    · exact hg
    · exact hout

theorem translateHFFormula_mulSuccRightSentence :
    translateHFFormula HF_mulSuccRightSentence =
      all (all (all (all (all
        (imp
          (addHFOrdinalLikeAt 3)
          (imp
            (hfAdjoinGraphAt 2 3 3)
            (imp
              (hfMulGraphAt 1 4 3)
              (imp
                (hfAddGraphAt 0 1 4)
                (hfMulGraphAt 0 4 2))))))))) := by
  let ρ : Nat → Nat :=
    hfUpVarMap (hfUpVarMap (hfUpVarMap
      (hfUpVarMap (hfUpVarMap (fun n : Nat ↦ n)))))
  change all (all (all (all (all
    (imp
      (hfFormulaAt ρ (AckermannHF.HF_ordinalLikeAt 3))
      (imp
        (hfFormulaAt ρ (AckermannHF.HF_succAt 2 3))
        (imp
          (hfFormulaAt ρ
            (AckermannHF.PAInHF.mulGraphAt 1 4 3))
          (imp
            (hfFormulaAt ρ
              (AckermannHF.PAInHF.addGraphAt 0 1 4))
            (hfFormulaAt ρ
              (AckermannHF.PAInHF.mulGraphAt 0 4 2)))))))))) = _
  have hρ : ∀ n, ρ n = n := by
    intro n
    simp only [ρ, hfUpVarMap_id]
  rw [hfFormulaAt_ext _ hρ, hfFormulaAt_ext _ hρ,
    hfFormulaAt_ext _ hρ, hfFormulaAt_ext _ hρ,
    hfFormulaAt_ext _ hρ]
  rfl

theorem BProv_Ax_s_mulSuccRightSentence :
    BProv Ax_s []
      (all (all (all (all (all
        (imp
          (addHFOrdinalLikeAt 3)
          (imp
            (hfAdjoinGraphAt 2 3 3)
            (imp
              (hfMulGraphAt 1 4 3)
              (imp
                (hfAddGraphAt 0 1 4)
                (hfMulGraphAt 0 4 2)))))))))) := by
  have htranslated : BProv translatedHFFinAx []
      (translateHFFormula HF_mulSuccRightSentence) :=
    BProv_translateHFFormula_of_BProv_HFFin
      BProv_HFFin_mulSuccRightSentence
  have hpa : BProv Ax_s []
      (translateHFFormula HF_mulSuccRightSentence) :=
    BProv_lift_translatedHFFinAx_to_PA
      (fun f hf ↦ BProv_Ax_s_of_translatedHFFinAx hf)
      htranslated
  rwa [translateHFFormula_mulSuccRightSentence] at hpa

def HF_mulFunctionalSentence : SetTheory.Form :=
  SetTheory.Form.fAll (SetTheory.Form.fAll (SetTheory.Form.fAll
    (SetTheory.Form.fAll
      (SetTheory.Form.fImp
        (AckermannHF.HF_ordinalLikeAt 3)
        (SetTheory.Form.fImp
          (AckermannHF.HF_ordinalLikeAt 2)
          (SetTheory.Form.fImp
            (AckermannHF.PAInHF.mulGraphAt 1 3 2)
            (SetTheory.Form.fImp
              (AckermannHF.PAInHF.mulGraphAt 0 3 2)
              (SetTheory.Form.fEq 1 0))))))))

theorem HF_mulFunctionalSentence_sentence :
    SetTheory.Sentence HF_mulFunctionalSentence := by
  intro i hi
  simp only [HF_mulFunctionalSentence, SetTheory.Free] at hi
  rcases hi with hleft | hright | hmul₁ | hmul₂ | heq
  · have := AckermannHF.HF_ordinalLikeAt_free hleft
    omega
  · have := AckermannHF.HF_ordinalLikeAt_free hright
    omega
  · rcases AckermannHF.PAInHF.mulGraphAt_free hmul₁ with
      h | h | h <;> omega
  · rcases AckermannHF.PAInHF.mulGraphAt_free hmul₂ with
      h | h | h <;> omega
  · rcases heq with h | h <;> omega

theorem BProv_HFFin_mulFunctionalSentence :
    SetTheory.BProv AckermannHF.HFFinAx_s []
      HF_mulFunctionalSentence := by
  apply SetTheory.completeness_inf AckermannHF.HFFinAx_s
  · exact AckermannHF.Sentences_HFFin
  · exact HF_mulFunctionalSentence_sentence
  · intro Dom mem v hHF
    let M := AckermannHF.firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
    intro left right out₁ out₂ hleftOrd hrightOrd hmul₁ hmul₂
    let e : Nat → Dom :=
      SetTheory.scons out₂
        (SetTheory.scons out₁
          (SetTheory.scons right (SetTheory.scons left v)))
    have hleftOrdM : SetTheory.Sat M.mem e
        (AckermannHF.HF_ordinalLikeAt 3) := by
      change SetTheory.Sat mem e (AckermannHF.HF_ordinalLikeAt 3)
      simpa [e, SetTheory.scons] using hleftOrd
    have hrightOrdM : SetTheory.Sat M.mem e
        (AckermannHF.HF_ordinalLikeAt 2) := by
      change SetTheory.Sat mem e (AckermannHF.HF_ordinalLikeAt 2)
      simpa [e, SetTheory.scons] using hrightOrd
    have hmul₁M : SetTheory.Sat M.mem e
        (AckermannHF.PAInHF.mulGraphAt 1 3 2) := by
      change SetTheory.Sat mem e
        (AckermannHF.PAInHF.mulGraphAt 1 3 2)
      simpa [e, SetTheory.scons] using hmul₁
    have hmul₂M : SetTheory.Sat M.mem e
        (AckermannHF.PAInHF.mulGraphAt 0 3 2) := by
      change SetTheory.Sat mem e
        (AckermannHF.PAInHF.mulGraphAt 0 3 2)
      simpa [e, SetTheory.scons] using hmul₂
    exact AckermannHF.PAInHF.mulGraphAt_value_unique_finite_model
      M e 1 0 3 2
      ((AckermannHF.HF_ordinalLikeAt_spec e 3).mp hleftOrdM)
      ((AckermannHF.HF_ordinalLikeAt_spec e 2).mp hrightOrdM)
      hmul₁M hmul₂M

theorem translateHFFormula_mulFunctionalSentence :
    translateHFFormula HF_mulFunctionalSentence =
      all (all (all (all
        (imp
          (addHFOrdinalLikeAt 3)
          (imp
            (addHFOrdinalLikeAt 2)
            (imp
              (hfMulGraphAt 1 3 2)
              (imp
                (hfMulGraphAt 0 3 2)
                (eq (Term.var 1) (Term.var 0))))))))) := by
  let ρ : Nat → Nat :=
    hfUpVarMap (hfUpVarMap
      (hfUpVarMap (hfUpVarMap (fun n : Nat ↦ n))))
  change all (all (all (all
    (imp
      (hfFormulaAt ρ (AckermannHF.HF_ordinalLikeAt 3))
      (imp
        (hfFormulaAt ρ (AckermannHF.HF_ordinalLikeAt 2))
        (imp
          (hfFormulaAt ρ
            (AckermannHF.PAInHF.mulGraphAt 1 3 2))
          (imp
            (hfFormulaAt ρ
              (AckermannHF.PAInHF.mulGraphAt 0 3 2))
            (eq (Term.var (ρ 1)) (Term.var (ρ 0)))))))))) = _
  have hρ : ∀ n, ρ n = n := by
    intro n
    simp only [ρ, hfUpVarMap_id]
  rw [hfFormulaAt_ext _ hρ, hfFormulaAt_ext _ hρ,
    hfFormulaAt_ext _ hρ, hfFormulaAt_ext _ hρ,
    hρ 1, hρ 0]
  rfl

theorem BProv_Ax_s_mulFunctionalSentence :
    BProv Ax_s []
      (all (all (all (all
        (imp
          (addHFOrdinalLikeAt 3)
          (imp
            (addHFOrdinalLikeAt 2)
            (imp
              (hfMulGraphAt 1 3 2)
              (imp
                (hfMulGraphAt 0 3 2)
                (eq (Term.var 1) (Term.var 0)))))))))) := by
  have htranslated : BProv translatedHFFinAx []
      (translateHFFormula HF_mulFunctionalSentence) :=
    BProv_translateHFFormula_of_BProv_HFFin
      BProv_HFFin_mulFunctionalSentence
  have hpa : BProv Ax_s []
      (translateHFFormula HF_mulFunctionalSentence) :=
    BProv_lift_translatedHFFinAx_to_PA
      (fun f hf ↦ BProv_Ax_s_of_translatedHFFinAx hf)
      htranslated
  rwa [translateHFFormula_mulFunctionalSentence] at hpa

private def mulTermSubst
    (out left right : Term) : Nat → Term
  | 0 => right
  | 1 => left
  | 2 => out
  | n+3 => Term.var (n+3)

/-- Term-parametric reverse translation of the HF multiplication graph. -/
def hfMulGraphTermAt
    (out left right : Term) : Formula :=
  subst (mulTermSubst out left right)
    (hfMulGraphAt 2 1 0)

theorem hfMulGraphAt_eq_termAt
    (out left right : Nat) :
    hfMulGraphAt out left right =
      hfMulGraphTermAt
        (Term.var out) (Term.var left) (Term.var right) := by
  let r : Nat → Nat
    | 0 => right
    | 1 => left
    | 2 => out
    | n+3 => n+3
  have hsubst :
      mulTermSubst
          (Term.var out) (Term.var left) (Term.var right) =
        fun n ↦ Term.var (r n) := by
    funext n
    rcases n with _ | _ | _ | n <;> rfl
  have hsource :
      SetTheory.rename r
          (AckermannHF.PAInHF.mulGraphAt 2 1 0) =
        AckermannHF.PAInHF.mulGraphAt out left right := by
    simpa [r] using
      (AckermannHF.PAInHF.rename_mulGraphAt r 2 1 0)
  simp only [hfMulGraphTermAt, hsubst, subst_var_rename,
    hfMulGraphAt]
  rw [← hsource]
  exact hfFormulaAt_id_rename _ _

theorem subst_hfMulGraphTermAt
    (sigma : Nat → Term) (out left right : Term) :
    subst sigma (hfMulGraphTermAt out left right) =
      hfMulGraphTermAt
        (Term.subst sigma out)
        (Term.subst sigma left)
        (Term.subst sigma right) := by
  simp only [hfMulGraphTermAt, subst_comp]
  apply subst_ext_free
  intro n hn
  rcases hfFormulaAt_free _ hn with ⟨m, hm, rfl⟩
  rcases AckermannHF.PAInHF.mulGraphAt_free hm with rfl | rfl | rfl
  · rfl
  · rfl
  · rfl

theorem rename_hfMulGraphTermAt
    (r : Nat → Nat) (out left right : Term) :
    rename r (hfMulGraphTermAt out left right) =
      hfMulGraphTermAt
        (Term.rename r out)
        (Term.rename r left)
        (Term.rename r right) := by
  rw [← subst_var_rename]
  simp only [subst_hfMulGraphTermAt,
    term_subst_var_rename]

theorem compositeMulCoreAt_normalForm
    (codedOut : Nat) :
    compositeMulCoreAt codedOut =
      and
        (eq (Term.var 0) (Term.var (codedOut+3)))
        (hfMulGraphTermAt
          (Term.var 0) (Term.var 1) (Term.var 2)) := by
  rw [← hfMulGraphAt_eq_termAt]
  simp only [compositeMulCoreAt, hfMulGraphAt,
    hfFormulaAt]
  let r : Nat → Nat := compositeMulCoreSlotMap codedOut
  have hmul : hfFormulaAt r AckermannHF.PAInHF.mulGraph =
      hfFormulaAt (fun n : Nat ↦ n) AckermannHF.PAInHF.mulGraph := by
    apply hfFormulaAt_ext_free
    intro n hn
    rcases AckermannHF.PAInHF.mulGraph_free hn with
      rfl | rfl | rfl <;> rfl
  rw [hmul]
  rfl

theorem BProv_Ax_s_hfMulGraphTermAt_zero_right
    {G : List Formula} {out left right : Term}
    (hright : BProv Ax_s G (hfEmptyTermAt right))
    (hout : BProv Ax_s G (hfEmptyTermAt out)) :
    BProv Ax_s G (hfMulGraphTermAt out left right) := by
  have hall : BProv Ax_s G
      (all (all (all
        (imp
          (hfEmptyTermAt (Term.var 1))
          (imp
            (hfEmptyTermAt (Term.var 0))
            (hfMulGraphTermAt
              (Term.var 0) (Term.var 2) (Term.var 1))))))) := by
    simpa only [hfEmptyAt, hfMulGraphAt_eq_termAt] using
      (BProv_weaken_nil
        (G := G) BProv_Ax_s_mulZeroRightSentence)
  have hleft := BProv_allE (B := Ax_s) (G := G) (t := left) hall
  have hright₀ := BProv_allE (B := Ax_s) (G := G) (t := right) hleft
  have hout₀ := BProv_allE (B := Ax_s) (G := G) (t := out) hright₀
  have himp : BProv Ax_s G
      (imp
        (hfEmptyTermAt right)
        (imp (hfEmptyTermAt out)
          (hfMulGraphTermAt out left right))) := by
    simpa [subst_hfEmptyTermAt,
      subst_hfMulGraphTermAt,
      subst, instTerm, Term.subst, Term.upSubst,
      Term.subst_rename_succ_up,
      term_subst_instTerm_rename_succ] using hout₀
  have hstep := BProv_mp Ax_s G _ _ himp hright
  exact BProv_mp Ax_s G _ _ hstep hout

theorem BProv_Ax_s_hfMulGraphTermAt_succ_right
    {G : List Formula}
    {out previous left rightSucc right : Term}
    (hrightDomain : BProv Ax_s G
      (subst (instTerm right) codedOrdinalDomain))
    (hrightSucc : BProv Ax_s G
      (hfAdjoinGraphTermAt rightSucc right right))
    (hmul : BProv Ax_s G
      (hfMulGraphTermAt previous left right))
    (hadd : BProv Ax_s G
      (hfAddGraphTermAt out previous left)) :
    BProv Ax_s G
      (hfMulGraphTermAt out left rightSucc) := by
  have hall : BProv Ax_s G
      (all (all (all (all (all
        (imp
          (subst (instTerm (Term.var 3)) codedOrdinalDomain)
          (imp
            (hfAdjoinGraphTermAt
              (Term.var 2) (Term.var 3) (Term.var 3))
            (imp
              (hfMulGraphTermAt
                (Term.var 1) (Term.var 4) (Term.var 3))
              (imp
                (hfAddGraphTermAt
                  (Term.var 0) (Term.var 1) (Term.var 4))
                (hfMulGraphTermAt
                  (Term.var 0) (Term.var 4) (Term.var 2))))))))))) := by
    simpa only [addHFOrdinalLikeAt_eq_domainTermAt,
      hfAdjoinGraphAt, hfMulGraphAt_eq_termAt,
      hfAddGraphAt_eq_termAt] using
      (BProv_weaken_nil
        (G := G) BProv_Ax_s_mulSuccRightSentence)
  have hleft := BProv_allE (B := Ax_s) (G := G) (t := left) hall
  have hright₀ := BProv_allE (B := Ax_s) (G := G) (t := right) hleft
  have hrightSucc₀ :=
    BProv_allE (B := Ax_s) (G := G) (t := rightSucc) hright₀
  have hprevious₀ :=
    BProv_allE (B := Ax_s) (G := G) (t := previous) hrightSucc₀
  have hout₀ := BProv_allE (B := Ax_s) (G := G) (t := out) hprevious₀
  have himp : BProv Ax_s G
      (imp
        (subst (instTerm right) codedOrdinalDomain)
        (imp
          (hfAdjoinGraphTermAt rightSucc right right)
          (imp
            (hfMulGraphTermAt previous left right)
            (imp
              (hfAddGraphTermAt out previous left)
              (hfMulGraphTermAt out left rightSucc))))) := by
    simpa [subst_domainTermAt,
      subst_hfAdjoinGraphTermAt,
      subst_hfMulGraphTermAt,
      subst_hfAddGraphTermAt,
      subst, instTerm, Term.subst, Term.upSubst,
      Term.subst_rename_succ_up,
      term_subst_instTerm_rename_succ] using hout₀
  have h₁ := BProv_mp Ax_s G _ _ himp hrightDomain
  have h₂ := BProv_mp Ax_s G _ _ h₁ hrightSucc
  have h₃ := BProv_mp Ax_s G _ _ h₂ hmul
  exact BProv_mp Ax_s G _ _ h₃ hadd

theorem BProv_Ax_s_hfMulGraphTermAt_functional
    {G : List Formula} {out₁ out₂ left right : Term}
    (hleftDomain : BProv Ax_s G
      (subst (instTerm left) codedOrdinalDomain))
    (hrightDomain : BProv Ax_s G
      (subst (instTerm right) codedOrdinalDomain))
    (hmul₁ : BProv Ax_s G
      (hfMulGraphTermAt out₁ left right))
    (hmul₂ : BProv Ax_s G
      (hfMulGraphTermAt out₂ left right)) :
    BProv Ax_s G (eq out₁ out₂) := by
  have hall : BProv Ax_s G
      (all (all (all (all
        (imp
          (subst (instTerm (Term.var 3)) codedOrdinalDomain)
          (imp
            (subst (instTerm (Term.var 2)) codedOrdinalDomain)
            (imp
              (hfMulGraphTermAt
                (Term.var 1) (Term.var 3) (Term.var 2))
              (imp
                (hfMulGraphTermAt
                  (Term.var 0) (Term.var 3) (Term.var 2))
                (eq (Term.var 1) (Term.var 0)))))))))) := by
    simpa only [addHFOrdinalLikeAt_eq_domainTermAt,
      hfMulGraphAt_eq_termAt] using
      (BProv_weaken_nil
        (G := G) BProv_Ax_s_mulFunctionalSentence)
  have hleft := BProv_allE (B := Ax_s) (G := G) (t := left) hall
  have hright₀ := BProv_allE (B := Ax_s) (G := G) (t := right) hleft
  have hout₁₀ := BProv_allE (B := Ax_s) (G := G) (t := out₁) hright₀
  have hout₂₀ := BProv_allE (B := Ax_s) (G := G) (t := out₂) hout₁₀
  have himp : BProv Ax_s G
      (imp
        (subst (instTerm left) codedOrdinalDomain)
        (imp
          (subst (instTerm right) codedOrdinalDomain)
          (imp
            (hfMulGraphTermAt out₁ left right)
            (imp
              (hfMulGraphTermAt out₂ left right)
              (eq out₁ out₂))))) := by
    simpa [subst_domainTermAt,
      subst_hfMulGraphTermAt,
      subst, instTerm, Term.subst, Term.upSubst,
      Term.subst_rename_succ_up,
      term_subst_instTerm_rename_succ] using hout₂₀
  have h₁ := BProv_mp Ax_s G _ _ himp hleftDomain
  have h₂ := BProv_mp Ax_s G _ _ h₁ hrightDomain
  have h₃ := BProv_mp Ax_s G _ _ h₂ hmul₁
  exact BProv_mp Ax_s G _ _ h₃ hmul₂

theorem BProv_Ax_s_ordinalCodeMulCore_zero
    {G : List Formula} {leftRaw leftCode rightCode out : Term}
    (hleft : BProv Ax_s G
      (ordinalCodeGraphTermAt leftRaw leftCode))
    (hright : BProv Ax_s G
      (ordinalCodeGraphTermAt Term.zero rightCode)) :
    BProv Ax_s G
      (iffForm
        (hfMulGraphTermAt out leftCode rightCode)
        (ordinalCodeGraphTermAt
          (Term.mul leftRaw Term.zero) out)) := by
  have hleftDomain :=
    BProv_Ax_s_codedOrdinalDomain_of_graph hleft
  have hrightDomain :=
    BProv_Ax_s_codedOrdinalDomain_of_graph hright
  have hrightEq : BProv Ax_s G (eq rightCode Term.zero) :=
    BProv_Ax_s_eq_zero_of_ordinalCodeGraphTermAt_zero hright
  have hrightEmpty : BProv Ax_s G (hfEmptyTermAt rightCode) :=
    BProv_Ax_s_hfEmptyTermAt_of_eq_zero hrightEq
  have hzeroEmpty : BProv Ax_s G (hfEmptyTermAt Term.zero) :=
    BProv_Ax_s_hfEmptyTermAt_zero
  have hbase : BProv Ax_s G
      (hfMulGraphTermAt Term.zero leftCode rightCode) :=
    BProv_Ax_s_hfMulGraphTermAt_zero_right
      hrightEmpty hzeroEmpty
  have hmulZero : BProv Ax_s G
      (eq (Term.mul leftRaw Term.zero) Term.zero) :=
    (BProv_Ax_s_mulZero_term leftRaw)
  have hzeroGraph : BProv Ax_s G
      (ordinalCodeGraphTermAt Term.zero Term.zero) :=
    BProv_Ax_s_ordinalCodeGraphTermAt_zero
  have hforward : BProv Ax_s G
      (imp
        (hfMulGraphTermAt out leftCode rightCode)
        (ordinalCodeGraphTermAt
          (Term.mul leftRaw Term.zero) out)) := by
    apply BProv_impI
    let C : List Formula :=
      hfMulGraphTermAt out leftCode rightCode :: G
    have hmul : BProv Ax_s C
        (hfMulGraphTermAt out leftCode rightCode) :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have houtEq : BProv Ax_s C (eq out Term.zero) :=
      BProv_Ax_s_hfMulGraphTermAt_functional
        (BProv_context_cons hleftDomain)
        (BProv_context_cons hrightDomain)
        hmul (BProv_context_cons hbase)
    exact BProv_ordinalCodeGraphTermAt_congr
      (BProv_eqSym (BProv_context_cons hmulZero))
      (BProv_eqSym houtEq) (BProv_context_cons hzeroGraph)
  have hreverse : BProv Ax_s G
      (imp
        (ordinalCodeGraphTermAt
          (Term.mul leftRaw Term.zero) out)
        (hfMulGraphTermAt out leftCode rightCode)) := by
    apply BProv_impI
    let C : List Formula :=
      ordinalCodeGraphTermAt
        (Term.mul leftRaw Term.zero) out :: G
    have htarget : BProv Ax_s C
        (ordinalCodeGraphTermAt
          (Term.mul leftRaw Term.zero) out) :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have houtGraph : BProv Ax_s C
        (ordinalCodeGraphTermAt Term.zero out) :=
      BProv_ordinalCodeGraphTermAt_congr_raw
        (BProv_context_cons hmulZero) htarget
    have houtEq : BProv Ax_s C (eq out Term.zero) :=
      BProv_Ax_s_ordinalCodeGraphTermAt_functional
        houtGraph (BProv_context_cons hzeroGraph)
    have houtEmpty : BProv Ax_s C (hfEmptyTermAt out) :=
      BProv_Ax_s_hfEmptyTermAt_of_eq_zero houtEq
    exact BProv_Ax_s_hfMulGraphTermAt_zero_right
      (BProv_context_cons hrightEmpty) houtEmpty
  exact BProv_iffForm_intro hforward hreverse

/- The fixed-predecessor multiplication successor step consumes the concrete
term-parametric addition bridge above. -/
set_option maxHeartbeats 600000 in
theorem BProv_Ax_s_ordinalCodeMulCore_succ_of_pred
    {G : List Formula}
    {leftRaw leftCode rightRaw rightCode rightSuccCode predOut out : Term}
    (hleft : BProv Ax_s G
      (ordinalCodeGraphTermAt leftRaw leftCode))
    (hright : BProv Ax_s G
      (ordinalCodeGraphTermAt rightRaw rightCode))
    (hrightSucc : BProv Ax_s G
      (ordinalCodeGraphTermAt (Term.succ rightRaw) rightSuccCode))
    (hprodPred : BProv Ax_s G
      (ordinalCodeGraphTermAt
        (Term.mul leftRaw rightRaw) predOut))
    (hmulPred : BProv Ax_s G
      (hfMulGraphTermAt predOut leftCode rightCode)) :
    BProv Ax_s G
      (iffForm
        (hfMulGraphTermAt out leftCode rightSuccCode)
        (ordinalCodeGraphTermAt
          (Term.mul leftRaw (Term.succ rightRaw)) out)) := by
  let sumRaw : Term :=
    Term.add (Term.mul leftRaw rightRaw) leftRaw
  let targetRaw : Term := Term.mul leftRaw (Term.succ rightRaw)
  have hleftDomain :=
    BProv_Ax_s_codedOrdinalDomain_of_graph hleft
  have hrightDomain :=
    BProv_Ax_s_codedOrdinalDomain_of_graph hright
  have hrightSuccDomain :=
    BProv_Ax_s_codedOrdinalDomain_of_graph hrightSucc
  have hrightStep :=
    BProv_Ax_s_hfAdjoinGraphTermAt_iff_ordinalCodeGraphTermAt_succ
      ordinalCodeGraphSuccClosure ordinalCodeGraphFunctional
      (codedOut := rightSuccCode) hright
  have hrightStepReverse : BProv Ax_s G
      (imp
        (ordinalCodeGraphTermAt
          (Term.succ rightRaw) rightSuccCode)
        (hfAdjoinGraphTermAt
          rightSuccCode rightCode rightCode)) := by
    simpa [iffForm] using BProv_andE2 hrightStep
  have hrightAdjoin : BProv Ax_s G
      (hfAdjoinGraphTermAt rightSuccCode rightCode rightCode) :=
    BProv_mp Ax_s G _ _ hrightStepReverse hrightSucc
  have hmulSucc : BProv Ax_s G (eq targetRaw sumRaw) := by
    simpa [targetRaw, sumRaw] using
      (BProv_Ax_s_mulSucc_terms leftRaw rightRaw)
  have hforward : BProv Ax_s G
      (imp
        (hfMulGraphTermAt out leftCode rightSuccCode)
        (ordinalCodeGraphTermAt targetRaw out)) := by
    apply BProv_impI
    let C : List Formula :=
      hfMulGraphTermAt out leftCode rightSuccCode :: G
    have hmulOut : BProv Ax_s C
        (hfMulGraphTermAt out leftCode rightSuccCode) :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    let graphBody : Formula :=
      ordinalCodeGraphTermAt
        (Term.rename Nat.succ sumRaw) (Term.var 0)
    have htotal : BProv Ax_s C (ex graphBody) := by
      simpa [graphBody, sumRaw, Term.rename] using
        (OrdinalCodeGraphProofs_total C sumRaw)
    let D : List Formula := graphBody :: C.map (rename Nat.succ)
    have hinner : BProv Ax_s D
        (rename Nat.succ
          (ordinalCodeGraphTermAt targetRaw out)) := by
      have hsum : BProv Ax_s D graphBody :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D])
      have lift : ∀ {phi : Formula}, BProv Ax_s C phi →
          BProv Ax_s D (rename Nat.succ phi) := by
        intro phi hphi
        simpa [D] using
          (BProv_rename_succ_context_cons_of_sentences
            (B := Ax_s) Ax_s_sentences
            (a := graphBody) hphi)
      have hleftD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.rename Nat.succ leftRaw)
            (Term.rename Nat.succ leftCode)) := by
        simpa [rename_ordinalCodeGraphTermAt] using
          (lift (BProv_context_cons hleft))
      have hprodPredD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.rename Nat.succ (Term.mul leftRaw rightRaw))
            (Term.rename Nat.succ predOut)) := by
        simpa [rename_ordinalCodeGraphTermAt] using
          (lift (BProv_context_cons hprodPred))
      have hmulPredD : BProv Ax_s D
          (hfMulGraphTermAt
            (Term.rename Nat.succ predOut)
            (Term.rename Nat.succ leftCode)
            (Term.rename Nat.succ rightCode)) := by
        simpa [rename_hfMulGraphTermAt] using
          (lift (BProv_context_cons hmulPred))
      have hrightAdjoinD : BProv Ax_s D
          (hfAdjoinGraphTermAt
            (Term.rename Nat.succ rightSuccCode)
            (Term.rename Nat.succ rightCode)
            (Term.rename Nat.succ rightCode)) := by
        simpa [rename_hfAdjoinGraphTermAt] using
          (lift (BProv_context_cons hrightAdjoin))
      have hleftDomainD : BProv Ax_s D
          (subst
            (instTerm (Term.rename Nat.succ leftCode))
            codedOrdinalDomain) := by
        have hraw := lift (BProv_context_cons hleftDomain)
        simpa [rename_subst_instTerm_codedOrdinalDomain] using hraw
      have hrightDomainD : BProv Ax_s D
          (subst
            (instTerm (Term.rename Nat.succ rightCode))
            codedOrdinalDomain) := by
        have hraw := lift (BProv_context_cons hrightDomain)
        simpa [rename_subst_instTerm_codedOrdinalDomain] using hraw
      have hrightSuccDomainD : BProv Ax_s D
          (subst
            (instTerm (Term.rename Nat.succ rightSuccCode))
            codedOrdinalDomain) := by
        have hraw := lift (BProv_context_cons hrightSuccDomain)
        simpa [rename_subst_instTerm_codedOrdinalDomain] using hraw
      have hmulOutD : BProv Ax_s D
          (hfMulGraphTermAt
            (Term.rename Nat.succ out)
            (Term.rename Nat.succ leftCode)
            (Term.rename Nat.succ rightSuccCode)) := by
        simpa [rename_hfMulGraphTermAt] using (lift hmulOut)
      have haddIff : BProv Ax_s D
          (iffForm
            (hfAddGraphTermAt
              (Term.var 0)
              (Term.rename Nat.succ predOut)
              (Term.rename Nat.succ leftCode))
            graphBody) := by
        have hraw := BProv_Ax_s_ordinalCodeAddTermAt
          (out := Term.var 0) hprodPredD hleftD
        simpa [graphBody, sumRaw, Term.rename] using hraw
      have haddReverse : BProv Ax_s D
          (imp graphBody
            (hfAddGraphTermAt
              (Term.var 0)
              (Term.rename Nat.succ predOut)
              (Term.rename Nat.succ leftCode))) := by
        simpa [iffForm] using BProv_andE2 haddIff
      have haddOut := BProv_mp Ax_s D _ _ haddReverse hsum
      have hmulKnown : BProv Ax_s D
          (hfMulGraphTermAt
            (Term.var 0)
            (Term.rename Nat.succ leftCode)
            (Term.rename Nat.succ rightSuccCode)) :=
        BProv_Ax_s_hfMulGraphTermAt_succ_right
          hrightDomainD hrightAdjoinD hmulPredD haddOut
      have houtEq : BProv Ax_s D
          (eq (Term.rename Nat.succ out) (Term.var 0)) :=
        BProv_Ax_s_hfMulGraphTermAt_functional
          hleftDomainD hrightSuccDomainD hmulOutD hmulKnown
      have hmulSuccD : BProv Ax_s D
          (eq
            (Term.rename Nat.succ targetRaw)
            (Term.rename Nat.succ sumRaw)) := by
        simpa [rename, Term.rename] using
          (lift (BProv_context_cons hmulSucc))
      have hresult := BProv_ordinalCodeGraphTermAt_congr
        (BProv_eqSym hmulSuccD) (BProv_eqSym houtEq)
        (by simpa [graphBody] using hsum)
      simpa [rename_ordinalCodeGraphTermAt] using hresult
    exact BProv_exE_of_sentences
      (B := Ax_s) Ax_s_sentences
      (G := C) (a := graphBody)
      (c := ordinalCodeGraphTermAt targetRaw out)
      htotal (by simpa [D] using hinner)
  have hreverse : BProv Ax_s G
      (imp
        (ordinalCodeGraphTermAt targetRaw out)
        (hfMulGraphTermAt out leftCode rightSuccCode)) := by
    apply BProv_impI
    let C : List Formula :=
      ordinalCodeGraphTermAt targetRaw out :: G
    have htarget : BProv Ax_s C
        (ordinalCodeGraphTermAt targetRaw out) :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hsum : BProv Ax_s C
        (ordinalCodeGraphTermAt sumRaw out) :=
      BProv_ordinalCodeGraphTermAt_congr_raw
        (BProv_context_cons hmulSucc) htarget
    have haddIff : BProv Ax_s C
        (iffForm
          (hfAddGraphTermAt out predOut leftCode)
          (ordinalCodeGraphTermAt sumRaw out)) := by
      have hprodPredC := BProv_context_cons
        (B := Ax_s) (a := ordinalCodeGraphTermAt targetRaw out)
        hprodPred
      have hleftC := BProv_context_cons
        (B := Ax_s) (a := ordinalCodeGraphTermAt targetRaw out)
        hleft
      have hraw := BProv_Ax_s_ordinalCodeAddTermAt
        (G := C) (out := out)
        hprodPredC hleftC
      simpa [sumRaw] using hraw
    have haddReverse : BProv Ax_s C
        (imp
          (ordinalCodeGraphTermAt sumRaw out)
          (hfAddGraphTermAt out predOut leftCode)) := by
      simpa [iffForm] using BProv_andE2 haddIff
    have haddOut := BProv_mp Ax_s C _ _ haddReverse hsum
    exact BProv_Ax_s_hfMulGraphTermAt_succ_right
      (BProv_context_cons hrightDomain)
      (BProv_context_cons hrightAdjoin)
      (BProv_context_cons hmulPred) haddOut
  simpa [iffForm, targetRaw] using BProv_andI hforward hreverse

def ordinalCodeMulOutputTermAt
    (leftRaw leftCode rightRaw rightCode : Term) : Formula :=
  all
    (iffForm
      (hfMulGraphTermAt
        (Term.var 0)
        (Term.rename Nat.succ leftCode)
        (Term.rename Nat.succ rightCode))
      (ordinalCodeGraphTermAt
        (Term.rename Nat.succ (Term.mul leftRaw rightRaw))
        (Term.var 0)))

theorem subst_ordinalCodeMulOutputTermAt
    (sigma : Nat → Term)
    (leftRaw leftCode rightRaw rightCode : Term) :
    subst sigma
        (ordinalCodeMulOutputTermAt
          leftRaw leftCode rightRaw rightCode) =
      ordinalCodeMulOutputTermAt
        (Term.subst sigma leftRaw)
        (Term.subst sigma leftCode)
        (Term.subst sigma rightRaw)
        (Term.subst sigma rightCode) := by
  simp only [ordinalCodeMulOutputTermAt, iffForm, subst]
  rw [subst_hfMulGraphTermAt,
    subst_ordinalCodeGraphTermAt]
  simp only [Term.subst, Term.upSubst,
    Term.subst_rename_succ_up]

theorem rename_ordinalCodeMulOutputTermAt
    (r : Nat → Nat)
    (leftRaw leftCode rightRaw rightCode : Term) :
    rename r
        (ordinalCodeMulOutputTermAt
          leftRaw leftCode rightRaw rightCode) =
      ordinalCodeMulOutputTermAt
        (Term.rename r leftRaw)
        (Term.rename r leftCode)
        (Term.rename r rightRaw)
        (Term.rename r rightCode) := by
  rw [← subst_var_rename]
  simp only [subst_ordinalCodeMulOutputTermAt,
    term_subst_var_rename]

def ordinalCodeMulPointTermAt
    (leftRaw leftCode rightRaw : Term) : Formula :=
  all
    (imp
      (ordinalCodeGraphTermAt
        (Term.rename Nat.succ rightRaw) (Term.var 0))
      (ordinalCodeMulOutputTermAt
        (Term.rename Nat.succ leftRaw)
        (Term.rename Nat.succ leftCode)
        (Term.rename Nat.succ rightRaw)
        (Term.var 0)))

theorem subst_ordinalCodeMulPointTermAt
    (sigma : Nat → Term)
    (leftRaw leftCode rightRaw : Term) :
    subst sigma
        (ordinalCodeMulPointTermAt
          leftRaw leftCode rightRaw) =
      ordinalCodeMulPointTermAt
        (Term.subst sigma leftRaw)
        (Term.subst sigma leftCode)
        (Term.subst sigma rightRaw) := by
  simp [ordinalCodeMulPointTermAt,
    subst_ordinalCodeGraphTermAt,
    subst_ordinalCodeMulOutputTermAt,
    subst, Term.subst, Term.upSubst,
    Term.subst_rename_succ_up]

theorem rename_ordinalCodeMulPointTermAt
    (r : Nat → Nat)
    (leftRaw leftCode rightRaw : Term) :
    rename r
        (ordinalCodeMulPointTermAt
          leftRaw leftCode rightRaw) =
      ordinalCodeMulPointTermAt
        (Term.rename r leftRaw)
        (Term.rename r leftCode)
        (Term.rename r rightRaw) := by
  rw [← subst_var_rename]
  simp only [subst_ordinalCodeMulPointTermAt,
    term_subst_var_rename]

theorem BProv_Ax_s_ordinalCodeMulPointTermAt_zero
    {G : List Formula} {leftRaw leftCode : Term}
    (hleft : BProv Ax_s G
      (ordinalCodeGraphTermAt leftRaw leftCode)) :
    BProv Ax_s G
      (ordinalCodeMulPointTermAt
        leftRaw leftCode Term.zero) := by
  let rightGraph : Formula :=
    ordinalCodeGraphTermAt Term.zero (Term.var 0)
  let Q : List Formula := G.map (rename Nat.succ)
  have hbody : BProv Ax_s Q
      (imp rightGraph
        (ordinalCodeMulOutputTermAt
          (Term.rename Nat.succ leftRaw)
          (Term.rename Nat.succ leftCode)
          Term.zero (Term.var 0))) := by
    apply BProv_impI
    let C : List Formula := rightGraph :: Q
    have hright : BProv Ax_s C rightGraph :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    let D : List Formula := C.map (rename Nat.succ)
    have hleftD : BProv Ax_s D
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+2) leftRaw)
          (Term.rename (fun n ↦ n+2) leftCode)) := by
      have h₂ := BProv_iterRenameSucc_of_sentences
        (B := Ax_s) Ax_s_sentences
        2 hleft
      have hctx := BProv_context_cons
        (B := Ax_s) (a := rename Nat.succ rightGraph) h₂
      simpa [D, C, Q, iterRenameContextSucc, iterRenameSucc,
        rename_ordinalCodeGraphTermAt,
        Term.rename_comp, Function.comp_def, Nat.add_assoc] using hctx
    have hrightD : BProv Ax_s D
        (ordinalCodeGraphTermAt Term.zero (Term.var 1)) := by
      have hren := BProv_rename_of_sentences
        (B := Ax_s) Ax_s_sentences
        hright Nat.succ
      simpa [D, rightGraph,
        rename_ordinalCodeGraphTermAt, Term.rename] using hren
    have hiff := BProv_Ax_s_ordinalCodeMulCore_zero
      (out := Term.var 0) hleftD hrightD
    have hall := BProv_allI_of_sentences
      (B := Ax_s) (G := C)
      Ax_s_sentences hiff
    simpa [ordinalCodeMulOutputTermAt,
      D, Term.rename, Term.rename_comp,
      Function.comp_def, Nat.add_assoc] using hall
  have hall := BProv_allI_of_sentences
    (B := Ax_s) (G := G)
    Ax_s_sentences hbody
  simpa [ordinalCodeMulPointTermAt,
    rightGraph, Q, Term.rename] using hall

theorem BProv_Ax_s_ordinalCodeMulOutputTermAt_succ
    {G : List Formula}
    {leftRaw leftCode rightRaw rightCode rightSuccCode : Term}
    (hleft : BProv Ax_s G
      (ordinalCodeGraphTermAt leftRaw leftCode))
    (hright : BProv Ax_s G
      (ordinalCodeGraphTermAt rightRaw rightCode))
    (hrightSucc : BProv Ax_s G
      (ordinalCodeGraphTermAt (Term.succ rightRaw) rightSuccCode))
    (hih : BProv Ax_s G
      (ordinalCodeMulOutputTermAt
        leftRaw leftCode rightRaw rightCode)) :
    BProv Ax_s G
      (ordinalCodeMulOutputTermAt
        leftRaw leftCode (Term.succ rightRaw) rightSuccCode) := by
  let graphBody : Formula :=
    ordinalCodeGraphTermAt
      (Term.mul
        (Term.rename Nat.succ leftRaw)
        (Term.rename Nat.succ rightRaw))
      (Term.var 0)
  have htotal : BProv Ax_s G (ex graphBody) := by
    simpa [graphBody, Term.rename] using
      (OrdinalCodeGraphProofs_total G
        (Term.mul leftRaw rightRaw))
  let C : List Formula := graphBody :: G.map (rename Nat.succ)
  have hinner : BProv Ax_s C
      (rename Nat.succ
        (ordinalCodeMulOutputTermAt
          leftRaw leftCode (Term.succ rightRaw) rightSuccCode)) := by
    have hprodPred : BProv Ax_s C graphBody :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have lift : ∀ {phi : Formula}, BProv Ax_s G phi →
        BProv Ax_s C (rename Nat.succ phi) := by
      intro phi hphi
      simpa [C] using
        (BProv_rename_succ_context_cons_of_sentences
          (B := Ax_s) Ax_s_sentences
          (a := graphBody) hphi)
    have hrightC : BProv Ax_s C
        (ordinalCodeGraphTermAt
          (Term.rename Nat.succ rightRaw)
          (Term.rename Nat.succ rightCode)) := by
      simpa [rename_ordinalCodeGraphTermAt] using (lift hright)
    have hleftC : BProv Ax_s C
        (ordinalCodeGraphTermAt
          (Term.rename Nat.succ leftRaw)
          (Term.rename Nat.succ leftCode)) := by
      simpa [rename_ordinalCodeGraphTermAt] using (lift hleft)
    have hrightSuccC : BProv Ax_s C
        (ordinalCodeGraphTermAt
          (Term.succ (Term.rename Nat.succ rightRaw))
          (Term.rename Nat.succ rightSuccCode)) := by
      simpa [rename_ordinalCodeGraphTermAt, Term.rename] using
        (lift hrightSucc)
    have hihC : BProv Ax_s C
        (ordinalCodeMulOutputTermAt
          (Term.rename Nat.succ leftRaw)
          (Term.rename Nat.succ leftCode)
          (Term.rename Nat.succ rightRaw)
          (Term.rename Nat.succ rightCode)) := by
      simpa only [rename_ordinalCodeMulOutputTermAt] using
        (lift hih)
    have hpointRaw := BProv_allE
      (B := Ax_s) (G := C) (t := Term.var 0) hihC
    have hpoint : BProv Ax_s C
        (iffForm
          (hfMulGraphTermAt
            (Term.var 0)
            (Term.rename Nat.succ leftCode)
            (Term.rename Nat.succ rightCode))
          graphBody) := by
      simpa only [ordinalCodeMulOutputTermAt, iffForm,
        graphBody, subst_hfMulGraphTermAt,
        subst_ordinalCodeGraphTermAt,
        subst, instTerm, Term.subst,
        Term.upSubst,
        term_subst_instTerm_rename_succ] using hpointRaw
    have hpointReverse : BProv Ax_s C
        (imp graphBody
          (hfMulGraphTermAt
            (Term.var 0)
            (Term.rename Nat.succ leftCode)
            (Term.rename Nat.succ rightCode))) := by
      simpa [iffForm] using BProv_andE2 hpoint
    have hmulPred : BProv Ax_s C
        (hfMulGraphTermAt
          (Term.var 0)
          (Term.rename Nat.succ leftCode)
          (Term.rename Nat.succ rightCode)) :=
      BProv_mp Ax_s C _ _ hpointReverse hprodPred
    let D : List Formula := C.map (rename Nat.succ)
    have hbody : BProv Ax_s D
        (iffForm
          (hfMulGraphTermAt
            (Term.var 0)
            (Term.rename (fun n ↦ n+2) leftCode)
            (Term.rename (fun n ↦ n+2) rightSuccCode))
          (ordinalCodeGraphTermAt
            (Term.mul
              (Term.rename (fun n ↦ n+2) leftRaw)
              (Term.succ
                (Term.rename (fun n ↦ n+2) rightRaw)))
            (Term.var 0))) := by
      have liftC : ∀ {phi : Formula}, BProv Ax_s C phi →
          BProv Ax_s D (rename Nat.succ phi) := by
        intro phi hphi
        simpa [D] using
          (BProv_rename_of_sentences
            (B := Ax_s) Ax_s_sentences
            hphi Nat.succ)
      have hrightD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.rename (fun n ↦ n+2) rightRaw)
            (Term.rename (fun n ↦ n+2) rightCode)) := by
        simpa [rename_ordinalCodeGraphTermAt,
          Term.rename_comp, Function.comp_def,
          Nat.add_assoc] using (liftC hrightC)
      have hleftD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.rename (fun n ↦ n+2) leftRaw)
            (Term.rename (fun n ↦ n+2) leftCode)) := by
        simpa [rename_ordinalCodeGraphTermAt,
          Term.rename_comp, Function.comp_def,
          Nat.add_assoc] using (liftC hleftC)
      have hrightSuccD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.succ
              (Term.rename (fun n ↦ n+2) rightRaw))
            (Term.rename (fun n ↦ n+2) rightSuccCode)) := by
        simpa [rename_ordinalCodeGraphTermAt, Term.rename,
          Term.rename_comp, Function.comp_def,
          Nat.add_assoc] using (liftC hrightSuccC)
      have hprodPredD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.mul
              (Term.rename (fun n ↦ n+2) leftRaw)
              (Term.rename (fun n ↦ n+2) rightRaw))
            (Term.var 1)) := by
        simpa [graphBody, rename_ordinalCodeGraphTermAt,
          Term.rename,
          Term.rename_comp, Function.comp_def,
          Nat.add_assoc] using (liftC hprodPred)
      have hmulPredD : BProv Ax_s D
          (hfMulGraphTermAt
            (Term.var 1)
            (Term.rename (fun n ↦ n+2) leftCode)
            (Term.rename (fun n ↦ n+2) rightCode)) := by
        simpa [rename_hfMulGraphTermAt,
          Term.rename,
          Term.rename_comp, Function.comp_def,
          Nat.add_assoc] using (liftC hmulPred)
      exact BProv_Ax_s_ordinalCodeMulCore_succ_of_pred
        hleftD hrightD hrightSuccD hprodPredD hmulPredD
    have hall := BProv_allI_of_sentences
      (B := Ax_s) (G := C)
      Ax_s_sentences hbody
    have hall' : BProv Ax_s C
        (ordinalCodeMulOutputTermAt
          (Term.rename Nat.succ leftRaw)
          (Term.rename Nat.succ leftCode)
          (Term.succ (Term.rename Nat.succ rightRaw))
          (Term.rename Nat.succ rightSuccCode)) := by
      simpa [ordinalCodeMulOutputTermAt, D,
        Term.rename, Term.rename_comp, Function.comp_def,
        Nat.add_assoc] using hall
    simpa only [rename_ordinalCodeMulOutputTermAt,
      Term.rename] using hall'
  exact BProv_exE_of_sentences
    (B := Ax_s) Ax_s_sentences
    (G := G) (a := graphBody)
    (c := ordinalCodeMulOutputTermAt
      leftRaw leftCode (Term.succ rightRaw) rightSuccCode)
    htotal (by simpa [C] using hinner)

theorem BProv_Ax_s_ordinalCodeMulPointTermAt_of_graph
    {G : List Formula}
    {leftRaw leftCode rightRaw rightCode : Term}
    (hpoint : BProv Ax_s G
      (ordinalCodeMulPointTermAt
        leftRaw leftCode rightRaw))
    (hgraph : BProv Ax_s G
      (ordinalCodeGraphTermAt rightRaw rightCode)) :
    BProv Ax_s G
      (ordinalCodeMulOutputTermAt
        leftRaw leftCode rightRaw rightCode) := by
  have himpRaw := BProv_allE
    (B := Ax_s) (G := G) (t := rightCode) hpoint
  have himp : BProv Ax_s G
      (imp
        (ordinalCodeGraphTermAt rightRaw rightCode)
        (ordinalCodeMulOutputTermAt
          leftRaw leftCode rightRaw rightCode)) := by
    simpa [ordinalCodeMulPointTermAt,
      subst_ordinalCodeGraphTermAt,
      subst_ordinalCodeMulOutputTermAt,
      subst, instTerm, Term.subst,
      term_subst_instTerm_rename_succ] using himpRaw
  exact BProv_mp Ax_s G _ _ himp hgraph

set_option maxHeartbeats 600000 in
theorem BProv_Ax_s_ordinalCodeMulPointTermAt_succ
    {G : List Formula} {leftRaw leftCode rightRaw : Term}
    (hleft : BProv Ax_s G
      (ordinalCodeGraphTermAt leftRaw leftCode))
    (hih : BProv Ax_s G
      (ordinalCodeMulPointTermAt
        leftRaw leftCode rightRaw)) :
    BProv Ax_s G
      (ordinalCodeMulPointTermAt
        leftRaw leftCode (Term.succ rightRaw)) := by
  let rightSuccGraph : Formula :=
    ordinalCodeGraphTermAt
      (Term.succ (Term.rename Nat.succ rightRaw))
      (Term.var 0)
  let Q : List Formula := G.map (rename Nat.succ)
  have hbody : BProv Ax_s Q
      (imp rightSuccGraph
        (ordinalCodeMulOutputTermAt
          (Term.rename Nat.succ leftRaw)
          (Term.rename Nat.succ leftCode)
          (Term.succ (Term.rename Nat.succ rightRaw))
          (Term.var 0))) := by
    apply BProv_impI
    let C : List Formula := rightSuccGraph :: Q
    have hrightSucc : BProv Ax_s C rightSuccGraph :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    let predBody : Formula :=
      ordinalCodeGraphTermAt
        (Term.rename (fun n ↦ n+2) rightRaw)
        (Term.var 0)
    have htotal : BProv Ax_s C (ex predBody) := by
      simpa [predBody, Term.rename_comp,
        Function.comp_def, Nat.add_assoc] using
        (OrdinalCodeGraphProofs_total C
          (Term.rename Nat.succ rightRaw))
    let D : List Formula := predBody :: C.map (rename Nat.succ)
    have hinner : BProv Ax_s D
        (rename Nat.succ
          (ordinalCodeMulOutputTermAt
            (Term.rename Nat.succ leftRaw)
            (Term.rename Nat.succ leftCode)
            (Term.succ (Term.rename Nat.succ rightRaw))
            (Term.var 0))) := by
      have hpred : BProv Ax_s D predBody :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D])
      have hrightSuccD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.succ
              (Term.rename (fun n ↦ n+2) rightRaw))
            (Term.var 1)) := by
        have hren := BProv_rename_of_sentences
          (B := Ax_s) Ax_s_sentences
          hrightSucc Nat.succ
        simpa [D, rightSuccGraph,
          rename_ordinalCodeGraphTermAt, Term.rename,
          Term.rename_comp, Function.comp_def,
          Nat.add_assoc] using
            (BProv_context_cons (a := predBody) hren)
      have hihQ : BProv Ax_s Q
          (ordinalCodeMulPointTermAt
            (Term.rename Nat.succ leftRaw)
            (Term.rename Nat.succ leftCode)
            (Term.rename Nat.succ rightRaw)) := by
        have hren := BProv_rename_of_sentences
          (B := Ax_s) Ax_s_sentences
          hih Nat.succ
        simpa [Q, rename_ordinalCodeMulPointTermAt] using hren
      have hleftQ : BProv Ax_s Q
          (ordinalCodeGraphTermAt
            (Term.rename Nat.succ leftRaw)
            (Term.rename Nat.succ leftCode)) := by
        have hren := BProv_rename_of_sentences
          (B := Ax_s) Ax_s_sentences
          hleft Nat.succ
        simpa [Q, rename_ordinalCodeGraphTermAt] using hren
      have hihC : BProv Ax_s C
          (ordinalCodeMulPointTermAt
            (Term.rename Nat.succ leftRaw)
            (Term.rename Nat.succ leftCode)
            (Term.rename Nat.succ rightRaw)) :=
        BProv_context_cons (a := rightSuccGraph) hihQ
      have hihD : BProv Ax_s D
          (ordinalCodeMulPointTermAt
            (Term.rename (fun n ↦ n+2) leftRaw)
            (Term.rename (fun n ↦ n+2) leftCode)
            (Term.rename (fun n ↦ n+2) rightRaw)) := by
        have hren := BProv_rename_succ_context_cons_of_sentences
          (B := Ax_s) Ax_s_sentences
          (a := predBody) hihC
        simpa [D, C, Q,
          rename_ordinalCodeMulPointTermAt,
          Term.rename_comp, Function.comp_def,
          Nat.add_assoc] using hren
      have hleftC : BProv Ax_s C
          (ordinalCodeGraphTermAt
            (Term.rename Nat.succ leftRaw)
            (Term.rename Nat.succ leftCode)) :=
        BProv_context_cons (a := rightSuccGraph) hleftQ
      have hleftD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.rename (fun n ↦ n+2) leftRaw)
            (Term.rename (fun n ↦ n+2) leftCode)) := by
        have hren := BProv_rename_succ_context_cons_of_sentences
          (B := Ax_s) Ax_s_sentences
          (a := predBody) hleftC
        simpa [D, C, Q,
          rename_ordinalCodeGraphTermAt,
          Term.rename_comp, Function.comp_def,
          Nat.add_assoc] using hren
      have houtputPred :=
        BProv_Ax_s_ordinalCodeMulPointTermAt_of_graph
          hihD (by simpa [predBody] using hpred)
      have houtputSucc :=
        BProv_Ax_s_ordinalCodeMulOutputTermAt_succ
          hleftD
          (by simpa [predBody] using hpred)
          hrightSuccD houtputPred
      simpa only [rename_ordinalCodeMulOutputTermAt,
        Term.rename, Term.rename_comp, Function.comp_def,
        Nat.add_assoc] using houtputSucc
    exact BProv_exE_of_sentences
      (B := Ax_s) Ax_s_sentences
      (G := C) (a := predBody)
      (c := ordinalCodeMulOutputTermAt
        (Term.rename Nat.succ leftRaw)
        (Term.rename Nat.succ leftCode)
        (Term.succ (Term.rename Nat.succ rightRaw))
        (Term.var 0))
      htotal (by simpa [D] using hinner)
  have hall := BProv_allI_of_sentences
    (B := Ax_s) (G := G)
    Ax_s_sentences hbody
  simpa [ordinalCodeMulPointTermAt,
    rightSuccGraph, Q, Term.rename] using hall

attribute [local irreducible]
  hfMulGraphTermAt
  ordinalCodeMulOutputTermAt
  ordinalCodeMulPointTermAt

set_option maxHeartbeats 400000 in
theorem BProv_Ax_s_all_ordinalCodeMulPoint
    {G : List Formula} {leftRaw leftCode : Term}
    (hleft : BProv Ax_s G
      (ordinalCodeGraphTermAt leftRaw leftCode)) :
    BProv Ax_s G
      (all
        (ordinalCodeMulPointTermAt
          (Term.rename Nat.succ leftRaw)
          (Term.rename Nat.succ leftCode)
          (Term.var 0))) := by
  let phi : Formula :=
    ordinalCodeMulPointTermAt
      (Term.rename Nat.succ leftRaw)
      (Term.rename Nat.succ leftCode)
      (Term.var 0)
  have hzero : BProv Ax_s G (subst substZero phi) := by
    have hbase :=
      BProv_Ax_s_ordinalCodeMulPointTermAt_zero hleft
    change BProv Ax_s G
      (subst substZero
        (ordinalCodeMulPointTermAt
          (Term.rename Nat.succ leftRaw)
          (Term.rename Nat.succ leftCode)
          (Term.var 0)))
    rw [subst_ordinalCodeMulPointTermAt]
    simpa only [substZero, Term.subst,
      term_substZero_rename_succ] using hbase
  let Q : List Formula := G.map (rename Nat.succ)
  have hsuccImp : BProv Ax_s Q
      (imp phi (subst substSuccVar phi)) := by
    let C : List Formula := phi :: Q
    have hihRaw : BProv Ax_s C phi :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hih : BProv Ax_s C
        (ordinalCodeMulPointTermAt
          (Term.rename Nat.succ leftRaw)
          (Term.rename Nat.succ leftCode)
          (Term.var 0)) := by
      simpa only [phi] using hihRaw
    have hleftQ : BProv Ax_s Q
        (ordinalCodeGraphTermAt
          (Term.rename Nat.succ leftRaw)
          (Term.rename Nat.succ leftCode)) := by
      have hren := BProv_rename_of_sentences
        (B := Ax_s) Ax_s_sentences
        hleft Nat.succ
      simpa [Q, rename_ordinalCodeGraphTermAt] using hren
    have hleftC : BProv Ax_s C
        (ordinalCodeGraphTermAt
          (Term.rename Nat.succ leftRaw)
          (Term.rename Nat.succ leftCode)) :=
      BProv_context_cons (a := phi) hleftQ
    have hnext :=
      BProv_Ax_s_ordinalCodeMulPointTermAt_succ
        hleftC hih
    have hnextSub : BProv Ax_s C (subst substSuccVar phi) := by
      change BProv Ax_s C
        (subst substSuccVar
          (ordinalCodeMulPointTermAt
            (Term.rename Nat.succ leftRaw)
            (Term.rename Nat.succ leftCode)
            (Term.var 0)))
      rw [subst_ordinalCodeMulPointTermAt]
      simpa only [substSuccVar, Term.subst,
        term_substSuccVar_rename_succ] using hnext
    exact BProv_impI (B := Ax_s) (G := Q)
      (a := phi) (b := subst substSuccVar phi)
      (by simpa only [C] using hnextSub)
  have hsucc : BProv Ax_s G
      (all (imp phi (subst substSuccVar phi))) :=
    BProv_allI_of_sentences
      (B := Ax_s) (G := G)
      Ax_s_sentences hsuccImp
  simpa only [phi] using
    (BProv_Ax_s_induction_rule (G := G) (phi := phi) hzero hsucc)

theorem BProv_Ax_s_ordinalCodeMulPointTermAt
    {G : List Formula} {leftRaw leftCode rightRaw : Term}
    (hleft : BProv Ax_s G
      (ordinalCodeGraphTermAt leftRaw leftCode)) :
    BProv Ax_s G
      (ordinalCodeMulPointTermAt
        leftRaw leftCode rightRaw) := by
  have hall := BProv_Ax_s_all_ordinalCodeMulPoint hleft
  have hraw := BProv_allE
    (B := Ax_s) (G := G) (t := rightRaw) hall
  rw [subst_ordinalCodeMulPointTermAt] at hraw
  simpa only [instTerm, Term.subst,
    term_subst_instTerm_rename_succ] using hraw

/-- Sound arithmetic multiplication kernel: for any explicit left/right code
and output term, the reverse-translated HF multiplication graph agrees with
the ordinal-code graph of raw multiplication. -/
theorem BProv_Ax_s_ordinalCodeMulTermAt
    {G : List Formula}
    {leftRaw leftCode rightRaw rightCode out : Term}
    (hleft : BProv Ax_s G
      (ordinalCodeGraphTermAt leftRaw leftCode))
    (hright : BProv Ax_s G
      (ordinalCodeGraphTermAt rightRaw rightCode)) :
    BProv Ax_s G
      (iffForm
        (hfMulGraphTermAt out leftCode rightCode)
        (ordinalCodeGraphTermAt
          (Term.mul leftRaw rightRaw) out)) := by
  have hpoint :=
    BProv_Ax_s_ordinalCodeMulPointTermAt
      (rightRaw := rightRaw) hleft
  have houtput :=
    BProv_Ax_s_ordinalCodeMulPointTermAt_of_graph
      hpoint hright
  have houtput' : BProv Ax_s G
      (all
        (iffForm
          (hfMulGraphTermAt
            (Term.var 0)
            (Term.rename Nat.succ leftCode)
            (Term.rename Nat.succ rightCode))
          (ordinalCodeGraphTermAt
            (Term.rename Nat.succ
              (Term.mul leftRaw rightRaw))
            (Term.var 0)))) := by
    simpa only [ordinalCodeMulOutputTermAt] using houtput
  have hraw := BProv_allE
    (B := Ax_s) (G := G)
    (t := out) houtput'
  simpa only [iffForm,
    subst_hfMulGraphTermAt,
    subst_ordinalCodeGraphTermAt,
    subst, instTerm, Term.subst,
    Term.upSubst,
    term_subst_instTerm_rename_succ] using hraw

/-- The multiplication core becomes sound once its local output slot is
existentially bound.  Before that binder, the left and right operand codes are
`var 0` and `var 1`; the external result slot is `var (codedOut + 2)`.
Opening the output binder shifts those three slots to `var 1`, `var 2`, and
`var (codedOut + 3)`, while the local result itself is `var 0`. -/
private def OrdinalCodeMulCoreCompatibility : Prop :=
  ∀ {G : List Formula} {leftRaw rightRaw : Term} {codedOut : Nat},
    BProv Ax_s G
      (ordinalCodeGraphTermAt leftRaw (Term.var 0)) →
    BProv Ax_s G
      (ordinalCodeGraphTermAt rightRaw (Term.var 1)) →
    BProv Ax_s G
      (iffForm
        (ex (compositeMulCoreAt codedOut))
        (ordinalCodeGraphTermAt
          (Term.mul leftRaw rightRaw) (Term.var (codedOut+2))))

theorem ordinalCodeMulCoreCompatibility :
    OrdinalCodeMulCoreCompatibility := by
  intro G leftRaw rightRaw codedOut hleft hright
  let core : Formula := compositeMulCoreAt codedOut
  let coreEx : Formula := ex core
  let target : Formula :=
    ordinalCodeGraphTermAt
      (Term.mul leftRaw rightRaw) (Term.var (codedOut+2))
  have hforward : BProv Ax_s G (imp coreEx target) := by
    apply BProv_impI
    let C : List Formula := coreEx :: G
    have hcoreEx : BProv Ax_s C coreEx :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    let D : List Formula := core :: C.map (rename Nat.succ)
    have hopened : BProv Ax_s D (rename Nat.succ target) := by
      have hcore : BProv Ax_s D core :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D])
      have hcore' : BProv Ax_s D
          (and
            (eq (Term.var 0) (Term.var (codedOut+3)))
            (hfMulGraphTermAt
              (Term.var 0) (Term.var 1) (Term.var 2))) := by
        simpa only [core, compositeMulCoreAt_normalForm] using hcore
      have houtEq : BProv Ax_s D
          (eq (Term.var 0) (Term.var (codedOut+3))) :=
        BProv_andE1 hcore'
      have hmul : BProv Ax_s D
          (hfMulGraphTermAt
            (Term.var 0) (Term.var 1) (Term.var 2)) :=
        BProv_andE2 hcore'
      have lift : ∀ {phi : Formula}, BProv Ax_s G phi →
          BProv Ax_s D (rename Nat.succ phi) := by
        intro phi hphi
        have hC := BProv_context_cons (B := Ax_s) (a := coreEx) hphi
        have hD := BProv_rename_succ_context_cons_of_sentences
          (B := Ax_s) Ax_s_sentences
          (a := core) hC
        simpa [D, C] using hD
      have hleftD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.rename Nat.succ leftRaw) (Term.var 1)) := by
        simpa [rename_ordinalCodeGraphTermAt, Term.rename] using (lift hleft)
      have hrightD : BProv Ax_s D
          (ordinalCodeGraphTermAt
            (Term.rename Nat.succ rightRaw) (Term.var 2)) := by
        simpa [rename_ordinalCodeGraphTermAt, Term.rename] using (lift hright)
      have hcompat := BProv_Ax_s_ordinalCodeMulTermAt
        (G := D)
        (leftRaw := Term.rename Nat.succ leftRaw)
        (leftCode := Term.var 1)
        (rightRaw := Term.rename Nat.succ rightRaw)
        (rightCode := Term.var 2)
        (out := Term.var 0) hleftD hrightD
      have hmulForward : BProv Ax_s D
          (imp
            (hfMulGraphTermAt
              (Term.var 0) (Term.var 1) (Term.var 2))
            (ordinalCodeGraphTermAt
              (Term.mul
                (Term.rename Nat.succ leftRaw)
                (Term.rename Nat.succ rightRaw))
              (Term.var 0))) := by
        simpa [iffForm] using BProv_andE1 hcompat
      have hlocal := BProv_mp Ax_s D _ _ hmulForward hmul
      have hresult :=
        BProv_ordinalCodeGraphTermAt_congr_coded houtEq hlocal
      simpa [target, rename_ordinalCodeGraphTermAt,
        Term.rename, Nat.add_assoc] using hresult
    have htargetC := BProv_exE_of_sentences
      (B := Ax_s) Ax_s_sentences
      (G := C) (a := core) (c := target)
      hcoreEx (by simpa [D] using hopened)
    exact htargetC
  have hreverse : BProv Ax_s G (imp target coreEx) := by
    apply BProv_impI
    let C : List Formula := target :: G
    have htarget : BProv Ax_s C target :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hleftC : BProv Ax_s C
        (ordinalCodeGraphTermAt leftRaw (Term.var 0)) :=
      BProv_context_cons (a := target) hleft
    have hrightC : BProv Ax_s C
        (ordinalCodeGraphTermAt rightRaw (Term.var 1)) :=
      BProv_context_cons (a := target) hright
    let out : Term := Term.var (codedOut+2)
    have hcompat := BProv_Ax_s_ordinalCodeMulTermAt
      (G := C) (leftRaw := leftRaw) (leftCode := Term.var 0)
      (rightRaw := rightRaw) (rightCode := Term.var 1)
      (out := out) hleftC hrightC
    have hmulReverse : BProv Ax_s C
        (imp target
          (hfMulGraphTermAt out (Term.var 0) (Term.var 1))) := by
      simpa [iffForm, target, out] using BProv_andE2 hcompat
    have hmul := BProv_mp Ax_s C _ _ hmulReverse htarget
    have heq : BProv Ax_s C (eq out out) :=
      BProv_eqRefl (B := Ax_s) (G := C) out
    have hcoreEx : BProv Ax_s C coreEx := by
      apply BProv_exI (t := out)
      simpa [coreEx, core, compositeMulCoreAt_normalForm,
        subst_hfMulGraphTermAt,
        subst, instTerm, Term.subst, out] using
        (BProv_andI heq hmul)
    exact hcoreEx
  simpa [iffForm, coreEx, target] using BProv_andI hforward hreverse

theorem BProv_Ax_s_term_graph_mul_forward_of_shifted_operands
    (G : List Formula) (a b leftRaw rightRaw : Term)
    (codedMap : Nat → Nat) (codedOut : Nat)
    (hleft : BProv Ax_s
      (((G.map (rename Nat.succ)).map (rename Nat.succ)).map
        (rename Nat.succ))
      (iffForm
        (compositeTermGraphAt 1 (fun n ↦ codedMap n + 3) a)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+3) leftRaw) (Term.var 1))))
    (hright : BProv Ax_s
      (((G.map (rename Nat.succ)).map (rename Nat.succ)).map
        (rename Nat.succ))
      (iffForm
        (compositeTermGraphAt 2 (fun n ↦ codedMap n + 3) b)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+3) rightRaw) (Term.var 2)))) :
    BProv Ax_s G
      (imp
        (compositeTermGraphAt codedOut codedMap (Term.mul a b))
        (ordinalCodeGraphTermAt
          (Term.mul leftRaw rightRaw) (Term.var codedOut))) := by
  let composite : Formula :=
    compositeTermGraphAt codedOut codedMap (Term.mul a b)
  let target : Formula :=
    ordinalCodeGraphTermAt
      (Term.mul leftRaw rightRaw) (Term.var codedOut)
  let leftComposite : Formula :=
    compositeTermGraphAt 1 (fun n ↦ codedMap n + 3) a
  let rightComposite : Formula :=
    compositeTermGraphAt 2 (fun n ↦ codedMap n + 3) b
  let core : Formula := compositeMulCoreAt codedOut
  let body : Formula :=
    and leftComposite (and rightComposite core)
  apply BProv_impI
  let C : List Formula := composite :: G
  have hcomposite : BProv Ax_s C composite :=
    BProv_ass (B := Ax_s) (G := C) (by simp [C])
  have hex : BProv Ax_s C (ex (ex (ex body))) := by
    simpa [composite, body, leftComposite, rightComposite, core,
      compositeTermGraphAt_mul_normalForm] using hcomposite
  let inner₁ : Formula := ex body
  let inner₂ : Formula := ex (ex body)
  let D : List Formula :=
    body ::
      (inner₁ ::
        (inner₂ :: C.map (rename Nat.succ)).map
          (rename Nat.succ)).map (rename Nat.succ)
  have hopened : BProv Ax_s D
      (rename Nat.succ (rename Nat.succ (rename Nat.succ target))) := by
    have hbody : BProv Ax_s D body :=
      BProv_ass (B := Ax_s) (G := D) (by simp [D])
    have hleftComposite : BProv Ax_s D leftComposite :=
      BProv_andE1 hbody
    have htail := BProv_andE2 hbody
    have hrightComposite : BProv Ax_s D rightComposite :=
      BProv_andE1 htail
    have hcore : BProv Ax_s D core :=
      BProv_andE2 htail
    -- The three existential outputs account for the triple renaming; after
    -- that, moving into `D` is ordinary prefix weakening.
    have liftShifted : ∀ {phi : Formula},
        BProv Ax_s
          (((G.map (rename Nat.succ)).map (rename Nat.succ)).map
            (rename Nat.succ)) phi →
        BProv Ax_s D phi := by
      intro phi hphi
      simpa [D, C, inner₁, inner₂, List.map_map] using
        (BProv_context_prefix (B := Ax_s)
          [body, rename Nat.succ inner₁,
            rename Nat.succ (rename Nat.succ inner₂),
            rename Nat.succ (rename Nat.succ
              (rename Nat.succ composite))] hphi)
    have hleftD := liftShifted hleft
    have hleftForward : BProv Ax_s D
        (imp leftComposite
          (ordinalCodeGraphTermAt
            (Term.rename (fun n ↦ n+3) leftRaw)
            (Term.var 1))) := by
      simpa [iffForm, leftComposite] using BProv_andE1 hleftD
    have hleftGraph := BProv_mp Ax_s D _ _
      hleftForward hleftComposite
    have hrightD := liftShifted hright
    have hrightForward : BProv Ax_s D
        (imp rightComposite
          (ordinalCodeGraphTermAt
            (Term.rename (fun n ↦ n+3) rightRaw)
            (Term.var 2))) := by
      simpa [iffForm, rightComposite] using BProv_andE1 hrightD
    have hrightGraph := BProv_mp Ax_s D _ _
      hrightForward hrightComposite
    have hcore' : BProv Ax_s D
        (and
          (eq (Term.var 0) (Term.var (codedOut+3)))
          (hfMulGraphTermAt
            (Term.var 0) (Term.var 1) (Term.var 2))) := by
      simpa only [core, compositeMulCoreAt_normalForm] using hcore
    have houtEq : BProv Ax_s D
        (eq (Term.var 0) (Term.var (codedOut+3))) :=
      BProv_andE1 hcore'
    have hmul : BProv Ax_s D
        (hfMulGraphTermAt
          (Term.var 0) (Term.var 1) (Term.var 2)) :=
      BProv_andE2 hcore'
    have hcompat := BProv_Ax_s_ordinalCodeMulTermAt
      (G := D)
      (leftRaw := Term.rename (fun n ↦ n+3) leftRaw)
      (leftCode := Term.var 1)
      (rightRaw := Term.rename (fun n ↦ n+3) rightRaw)
      (rightCode := Term.var 2)
      (out := Term.var 0) hleftGraph hrightGraph
    have hmulForward : BProv Ax_s D
        (imp
          (hfMulGraphTermAt
            (Term.var 0) (Term.var 1) (Term.var 2))
          (ordinalCodeGraphTermAt
            (Term.mul
              (Term.rename (fun n ↦ n+3) leftRaw)
              (Term.rename (fun n ↦ n+3) rightRaw))
            (Term.var 0))) := by
      simpa [iffForm] using BProv_andE1 hcompat
    have hlocal := BProv_mp Ax_s D _ _ hmulForward hmul
    have hresult :=
      BProv_ordinalCodeGraphTermAt_congr_coded houtEq hlocal
    simpa [target, rename_ordinalCodeGraphTermAt,
      Term.rename, Term.rename_comp,
      Function.comp_def, Nat.add_assoc] using hresult
  have htargetC := BProv_three_exE_of_sentences
    (B := Ax_s) Ax_s_sentences
    (G := C) (body := body) (target := target)
    hex (by simpa [D, inner₁, inner₂] using hopened)
  simpa [C] using htargetC

theorem BProv_Ax_s_term_graph_mul_reverse_of_shifted_operands
    (G : List Formula) (a b leftRaw rightRaw : Term)
    (codedMap : Nat → Nat) (codedOut : Nat)
    (hleft : BProv Ax_s
      (((G.map (rename Nat.succ)).map (rename Nat.succ)).map
        (rename Nat.succ))
      (iffForm
        (compositeTermGraphAt 1 (fun n ↦ codedMap n + 3) a)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+3) leftRaw) (Term.var 1))))
    (hright : BProv Ax_s
      (((G.map (rename Nat.succ)).map (rename Nat.succ)).map
        (rename Nat.succ))
      (iffForm
        (compositeTermGraphAt 2 (fun n ↦ codedMap n + 3) b)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+3) rightRaw) (Term.var 2)))) :
    BProv Ax_s G
      (imp
        (ordinalCodeGraphTermAt
          (Term.mul leftRaw rightRaw) (Term.var codedOut))
        (compositeTermGraphAt codedOut codedMap (Term.mul a b))) := by
  let composite : Formula :=
    compositeTermGraphAt codedOut codedMap (Term.mul a b)
  let target : Formula :=
    ordinalCodeGraphTermAt
      (Term.mul leftRaw rightRaw) (Term.var codedOut)
  let leftComposite : Formula :=
    compositeTermGraphAt 1 (fun n ↦ codedMap n + 3) a
  let rightComposite : Formula :=
    compositeTermGraphAt 2 (fun n ↦ codedMap n + 3) b
  let core : Formula := compositeMulCoreAt codedOut
  let body : Formula :=
    and leftComposite (and rightComposite core)
  apply BProv_impI
  let C : List Formula := target :: G
  have htarget : BProv Ax_s C target :=
    BProv_ass (B := Ax_s) (G := C) (by simp [C])
  let rightGraphBody : Formula :=
    ordinalCodeGraphTermAt
      (Term.rename Nat.succ rightRaw) (Term.var 0)
  have hrightTotal : BProv Ax_s C (ex rightGraphBody) := by
    simpa [rightGraphBody] using
      (OrdinalCodeGraphProofs_total C rightRaw)
  let R : List Formula := rightGraphBody :: C.map (rename Nat.succ)
  let leftGraphBody : Formula :=
    ordinalCodeGraphTermAt
      (Term.rename (fun n ↦ n+2) leftRaw) (Term.var 0)
  have hleftTotal : BProv Ax_s R (ex leftGraphBody) := by
    simpa [leftGraphBody, Term.rename_comp,
      Function.comp_def, Nat.add_assoc] using
      (OrdinalCodeGraphProofs_total R
        (Term.rename Nat.succ leftRaw))
  let L : List Formula := leftGraphBody :: R.map (rename Nat.succ)
  have hleftGraph : BProv Ax_s L leftGraphBody :=
    BProv_ass (B := Ax_s) (G := L) (by simp [L])
  have hrightGraphR : BProv Ax_s R rightGraphBody :=
    BProv_ass (B := Ax_s) (G := R) (by simp [R])
  have hrightGraph : BProv Ax_s L
      (ordinalCodeGraphTermAt
        (Term.rename (fun n ↦ n+2) rightRaw) (Term.var 1)) := by
    have hren := BProv_rename_succ_context_cons_of_sentences
      (B := Ax_s) Ax_s_sentences
      (a := leftGraphBody) hrightGraphR
    simpa [L, rightGraphBody,
      rename_ordinalCodeGraphTermAt,
      Term.rename, Term.rename_comp,
      Function.comp_def, Nat.add_assoc] using hren
  let targetL : Formula :=
    ordinalCodeGraphTermAt
      (Term.mul
        (Term.rename (fun n ↦ n+2) leftRaw)
        (Term.rename (fun n ↦ n+2) rightRaw))
      (Term.var (codedOut+2))
  have htargetL : BProv Ax_s L targetL := by
    have htargetLift := BProv_lift_two_contexts_of_sentences
      (B := Ax_s) Ax_s_sentences
      (outer := rightGraphBody) (inner := leftGraphBody) htarget
    simpa [L, R, C, target, targetL,
      rename_ordinalCodeGraphTermAt, Term.rename,
      Term.rename_comp, Function.comp_def,
      Nat.add_assoc] using htargetLift
  have hcoreIff := ordinalCodeMulCoreCompatibility
    (G := L)
    (leftRaw := Term.rename (fun n ↦ n+2) leftRaw)
    (rightRaw := Term.rename (fun n ↦ n+2) rightRaw)
    (codedOut := codedOut)
    (by simpa [leftGraphBody] using hleftGraph)
    hrightGraph
  have hcoreReverse : BProv Ax_s L
      (imp targetL (ex core)) := by
    simpa [iffForm, targetL, core] using BProv_andE2 hcoreIff
  have hcoreEx : BProv Ax_s L (ex core) :=
    BProv_mp Ax_s L _ _ hcoreReverse htargetL
  let D : List Formula := core :: L.map (rename Nat.succ)
  have hrenamedComposite : BProv Ax_s D
      (rename Nat.succ (rename Nat.succ
        (rename Nat.succ composite))) := by
    have hcore : BProv Ax_s D core :=
      BProv_ass (B := Ax_s) (G := D) (by simp [D])
    have liftShifted : ∀ {phi : Formula},
        BProv Ax_s
          (((G.map (rename Nat.succ)).map (rename Nat.succ)).map
            (rename Nat.succ)) phi →
        BProv Ax_s D phi := by
      intro phi hphi
      simpa [D, L, R, C, List.map_map] using
        (BProv_context_prefix (B := Ax_s)
          [core, rename Nat.succ leftGraphBody,
            rename Nat.succ (rename Nat.succ rightGraphBody),
            rename Nat.succ (rename Nat.succ
              (rename Nat.succ target))] hphi)
    have hleftD := liftShifted hleft
    have hleftReverse : BProv Ax_s D
        (imp
          (ordinalCodeGraphTermAt
            (Term.rename (fun n ↦ n+3) leftRaw) (Term.var 1))
          leftComposite) := by
      simpa [iffForm, leftComposite] using BProv_andE2 hleftD
    have hleftGraphD : BProv Ax_s D
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+3) leftRaw) (Term.var 1)) := by
      have hren := BProv_rename_succ_context_cons_of_sentences
        (B := Ax_s) Ax_s_sentences
        (a := core) hleftGraph
      simpa [D, leftGraphBody,
        rename_ordinalCodeGraphTermAt,
        Term.rename, Term.rename_comp,
        Function.comp_def, Nat.add_assoc] using hren
    have hleftComposite : BProv Ax_s D leftComposite :=
      BProv_mp Ax_s D _ _ hleftReverse hleftGraphD
    have hrightD := liftShifted hright
    have hrightReverse : BProv Ax_s D
        (imp
          (ordinalCodeGraphTermAt
            (Term.rename (fun n ↦ n+3) rightRaw) (Term.var 2))
          rightComposite) := by
      simpa [iffForm, rightComposite] using BProv_andE2 hrightD
    have hrightGraphD : BProv Ax_s D
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+3) rightRaw) (Term.var 2)) := by
      have hren := BProv_rename_succ_context_cons_of_sentences
        (B := Ax_s) Ax_s_sentences
        (a := core) hrightGraph
      simpa [D, L, rightGraphBody,
        rename_ordinalCodeGraphTermAt,
        Term.rename, Term.rename_comp,
        Function.comp_def, Nat.add_assoc] using hren
    have hrightComposite : BProv Ax_s D rightComposite :=
      BProv_mp Ax_s D _ _ hrightReverse hrightGraphD
    have hbody : BProv Ax_s D body :=
      BProv_andI hleftComposite
        (BProv_andI hrightComposite hcore)
    change BProv Ax_s D
      (rename Nat.succ (rename Nat.succ (rename Nat.succ
        (compositeTermGraphAt codedOut codedMap (Term.mul a b)))))
    rw [compositeTermGraphAt_mul_normalForm]
    apply BProv_exI (t := Term.var 2)
    apply BProv_exI (t := Term.var 1)
    apply BProv_exI (t := Term.var 0)
    rw [subst_three_witnesses_rename_three_succ]
    exact hbody
  have hcompositeL : BProv Ax_s L
      (rename Nat.succ (rename Nat.succ composite)) :=
    BProv_exE_of_sentences
      (B := Ax_s) Ax_s_sentences
      (G := L) (a := core)
      (c := rename Nat.succ (rename Nat.succ composite))
      hcoreEx (by simpa [D] using hrenamedComposite)
  have hcompositeR : BProv Ax_s R (rename Nat.succ composite) :=
    BProv_exE_of_sentences
      (B := Ax_s) Ax_s_sentences
      (G := R) (a := leftGraphBody)
      (c := rename Nat.succ composite)
      hleftTotal (by simpa [L] using hcompositeL)
  have hcompositeC : BProv Ax_s C composite :=
    BProv_exE_of_sentences
      (B := Ax_s) Ax_s_sentences
      (G := C) (a := rightGraphBody) (c := composite)
      hrightTotal (by simpa [R] using hcompositeR)
  simpa [C] using hcompositeC

theorem BProv_Ax_s_term_graph_mul_of_shifted_operands
    (G : List Formula) (a b leftRaw rightRaw : Term)
    (codedMap : Nat → Nat) (codedOut : Nat)
    (hleft : BProv Ax_s
      (((G.map (rename Nat.succ)).map (rename Nat.succ)).map
        (rename Nat.succ))
      (iffForm
        (compositeTermGraphAt 1 (fun n ↦ codedMap n + 3) a)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+3) leftRaw) (Term.var 1))))
    (hright : BProv Ax_s
      (((G.map (rename Nat.succ)).map (rename Nat.succ)).map
        (rename Nat.succ))
      (iffForm
        (compositeTermGraphAt 2 (fun n ↦ codedMap n + 3) b)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+3) rightRaw) (Term.var 2)))) :
    BProv Ax_s G
      (iffForm
        (compositeTermGraphAt codedOut codedMap (Term.mul a b))
        (ordinalCodeGraphTermAt
          (Term.mul leftRaw rightRaw) (Term.var codedOut))) := by
  have hforward :=
    BProv_Ax_s_term_graph_mul_forward_of_shifted_operands
      G a b leftRaw rightRaw codedMap codedOut hleft hright
  have hreverse :=
    BProv_Ax_s_term_graph_mul_reverse_of_shifted_operands
      G a b leftRaw rightRaw codedMap codedOut hleft hright
  exact BProv_iffForm_intro hforward hreverse

/-- Multiplication preserves the complete ordinal-code term-graph property. -/
theorem ordinalCodeTermGraphProof_mul
    (a b : Term)
    (iha : OrdinalCodeTermGraphProof a)
    (ihb : OrdinalCodeTermGraphProof b) :
    OrdinalCodeTermGraphProof (Term.mul a b) := by
  intro G rawMap codedMap codedOut hcode
  let G₃ : List Formula :=
    (((G.map (rename Nat.succ)).map (rename Nat.succ)).map
      (rename Nat.succ))
  let rawMap₃ : Nat → Nat := fun n ↦ rawMap n + 3
  let codedMap₃ : Nat → Nat := fun n ↦ codedMap n + 3
  have hcode₃ : ∀ n, Term.Free n (Term.mul a b) →
      BProv Ax_s G₃
        (ordinalCodeGraphAt (rawMap₃ n) (codedMap₃ n)) := by
    intro n hn
    have h₀ := hcode n hn
    have h₃ := BProv_iterRenameSucc_of_sentences
      (B := Ax_s) Ax_s_sentences
      3 h₀
    simpa [G₃, rawMap₃, codedMap₃, iterRenameContextSucc, iterRenameSucc,
      ordinalCodeGraphAt,
      rename_ordinalCodeGraphTermAt, Term.rename,
      List.map_map, Function.comp_def, Nat.add_assoc] using h₃
  have hleftCode : ∀ n, Term.Free n a →
      BProv Ax_s G₃
        (ordinalCodeGraphAt (rawMap₃ n) (codedMap₃ n)) :=
    fun n hn ↦ hcode₃ n (Or.inl hn)
  have hrightCode : ∀ n, Term.Free n b →
      BProv Ax_s G₃
        (ordinalCodeGraphAt (rawMap₃ n) (codedMap₃ n)) :=
    fun n hn ↦ hcode₃ n (Or.inr hn)
  have hleft₀ := iha G₃ rawMap₃ codedMap₃ 1 hleftCode
  have hleft : BProv Ax_s G₃
      (iffForm
        (compositeTermGraphAt 1 (fun n ↦ codedMap n + 3) a)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+3) (Term.rename rawMap a))
          (Term.var 1))) := by
    simpa [rawMap₃, codedMap₃,
      Term.rename_comp, Function.comp_def,
      Nat.add_assoc] using hleft₀
  have hright₀ := ihb G₃ rawMap₃ codedMap₃ 2 hrightCode
  have hright : BProv Ax_s G₃
      (iffForm
        (compositeTermGraphAt 2 (fun n ↦ codedMap n + 3) b)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+3) (Term.rename rawMap b))
          (Term.var 2))) := by
    simpa [rawMap₃, codedMap₃,
      Term.rename_comp, Function.comp_def,
      Nat.add_assoc] using hright₀
  have hmul := BProv_Ax_s_term_graph_mul_of_shifted_operands
    G a b (Term.rename rawMap a) (Term.rename rawMap b)
    codedMap codedOut hleft hright
  simpa [Term.rename] using hmul

theorem ordinalCodeTermMulCompatibility :
    OrdinalCodeTermMulCompatibility := by
  intro a b iha ihb
  exact ordinalCodeTermGraphProof_mul a b iha ihb

/-- Modular compatibility constructor retaining explicit addition and
multiplication arguments. -/
theorem OrdinalCodeTermCompatibilityProofs_of_add_mul
    (hadd : OrdinalCodeTermAddCompatibility)
    (hmul : OrdinalCodeTermMulCompatibility) :
    OrdinalCodeTermCompatibilityProofs where
  graph_functional := ordinalCodeGraphFunctional
  zero_compatible := OrdinalCodeTermGraphProof_zero
  succ_compatible := ordinalCodeTermGraphProof_succ
  add_compatible := hadd
  mul_compatible := hmul

/-- Functionality, zero, successor, and addition are concrete;
multiplication alone now constructs the full operation interface. -/
theorem OrdinalCodeTermCompatibilityProofs_of_mul
    (hmul : OrdinalCodeTermMulCompatibility) :
    OrdinalCodeTermCompatibilityProofs where
  graph_functional := ordinalCodeGraphFunctional
  zero_compatible := OrdinalCodeTermGraphProof_zero
  succ_compatible := ordinalCodeTermGraphProof_succ
  add_compatible := ordinalCodeTermAddCompatibility
  mul_compatible := hmul

/-- The operation interface closes the full `term_graph` field by ordinary
structural induction on PA terms. -/
theorem BProv_Ax_s_term_graph_of_compatibility
    (C : OrdinalCodeTermCompatibilityProofs) :
    ∀ t, OrdinalCodeTermGraphProof t := by
  intro t
  induction t with
  | var n =>
      intro G rawMap codedMap codedOut hcode
      exact BProv_Ax_s_term_graph_var
        C.graph_functional G n rawMap codedMap codedOut hcode
  | zero =>
      exact C.zero_compatible
  | succ t ih =>
      exact C.succ_compatible t ih
  | add a b iha ihb =>
      exact C.add_compatible a b iha ihb
  | mul a b iha ihb =>
      exact C.mul_compatible a b iha ihb

/-- The graph-level proof obligations remaining after totality. -/
structure OrdinalCodeGraphRemainingProofs where
  range : ∀ (G : List Formula) (coded : Term),
    BProv Ax_s G
      (iffForm
        (subst (instTerm coded) codedOrdinalDomain)
        (ex (ordinalCodeGraphTermAt
          (Term.var 0) (Term.rename Nat.succ coded))))
  injective : ∀ {G : List Formula} {raw₁ raw₂ coded : Term},
    BProv Ax_s G (ordinalCodeGraphTermAt raw₁ coded) →
    BProv Ax_s G (ordinalCodeGraphTermAt raw₂ coded) →
    BProv Ax_s G (eq raw₁ raw₂)

/-- Sole remaining graph-level law after totality, range, and coded-output
functionality have been proved. -/
def OrdinalCodeGraphInjective : Prop :=
  ∀ {G : List Formula} {raw₁ raw₂ coded : Term},
    BProv Ax_s G (ordinalCodeGraphTermAt raw₁ coded) →
    BProv Ax_s G (ordinalCodeGraphTermAt raw₂ coded) →
    BProv Ax_s G (eq raw₁ raw₂)

/-! ## Raw-side injectivity of `ordinalCodeGraphTermAt` -/

/-- On ordinal-like HF objects, two self-successors with a common output
have equal inputs. -/
def HF_selfSuccInjectiveSentence : SetTheory.Form :=
  SetTheory.Form.fAll (SetTheory.Form.fAll (SetTheory.Form.fAll
    (SetTheory.Form.fImp
      (AckermannHF.HF_ordinalLikeAt 2)
      (SetTheory.Form.fImp
        (AckermannHF.HF_ordinalLikeAt 1)
        (SetTheory.Form.fImp
          (AckermannHF.HF_succAt 0 2)
          (SetTheory.Form.fImp
            (AckermannHF.HF_succAt 0 1)
            (SetTheory.Form.fEq 2 1)))))))

theorem HF_selfSuccInjectiveSentence_sentence :
    SetTheory.Sentence HF_selfSuccInjectiveSentence := by
  intro i hi
  simp [HF_selfSuccInjectiveSentence,
    AckermannHF.HF_ordinalLikeAt,
    AckermannHF.HF_transitiveAt,
    AckermannHF.HF_memTotalOnAt,
    AckermannHF.HF_succAt,
    AckermannHF.HF_adjoinAt,
    SetTheory.fIff, SetTheory.Free] at hi

theorem BProv_HFFin_selfSuccInjectiveSentence :
    SetTheory.BProv AckermannHF.HFFinAx_s []
      HF_selfSuccInjectiveSentence := by
  apply SetTheory.completeness_inf AckermannHF.HFFinAx_s
  · exact AckermannHF.Sentences_HFFin
  · exact HF_selfSuccInjectiveSentence_sentence
  · intro Dom mem v hHF
    let M := AckermannHF.firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
    intro a b out ha hb hsuccA hsuccB
    have ha' : AckermannHF.OrdinalLike M.mem a :=
      (AckermannHF.HF_ordinalLikeAt_spec
        (SetTheory.scons out (SetTheory.scons b (SetTheory.scons a v))) 2).mp ha
    have hb' : AckermannHF.OrdinalLike M.mem b :=
      (AckermannHF.HF_ordinalLikeAt_spec
        (SetTheory.scons out (SetTheory.scons b (SetTheory.scons a v))) 1).mp hb
    have hsuccA' : out = M.adjoin a a :=
      (AckermannHF.FirstOrderAdjunctionModel.HF_succAt_spec
        M.toFirstOrderAdjunctionModel
        (SetTheory.scons out (SetTheory.scons b (SetTheory.scons a v)))
        0 2).mp hsuccA
    have hsuccB' : out = M.adjoin b b :=
      (AckermannHF.FirstOrderAdjunctionModel.HF_succAt_spec
        M.toFirstOrderAdjunctionModel
        (SetTheory.scons out (SetTheory.scons b (SetTheory.scons a v)))
        0 1).mp hsuccB
    apply AckermannHF.FirstOrderAdjunctionModel.adjoin_self_injective_on_ordinalLike
      M.toFirstOrderAdjunctionModel ha' hb'
    rw [← hsuccA', ← hsuccB']

def selfSuccInjectivePAFormula : Formula :=
  all <| all <| all <|
    imp (rename (fun n : Nat ↦ n + 2) codedOrdinalDomain) <|
    imp (rename Nat.succ codedOrdinalDomain) <|
    imp (hfAdjoinGraphAt 0 2 2) <|
    imp (hfAdjoinGraphAt 0 1 1) <|
    eq (Term.var 2) (Term.var 1)

theorem translateHFFormula_selfSuccInjectiveSentence :
    translateHFFormula HF_selfSuccInjectiveSentence =
      selfSuccInjectivePAFormula := by
  rfl

theorem BProv_Ax_s_selfSuccInjectiveSentence {G : List Formula} :
    BProv Ax_s G selfSuccInjectivePAFormula := by
  apply BProv_weaken_nil
  have htranslated : BProv translatedHFFinAx []
      (translateHFFormula HF_selfSuccInjectiveSentence) :=
    BProv_translateHFFormula_of_BProv_HFFin
      BProv_HFFin_selfSuccInjectiveSentence
  have hpa : BProv Ax_s []
      (translateHFFormula HF_selfSuccInjectiveSentence) :=
    BProv_lift_translatedHFFinAx_to_PA
      (fun f hf => BProv_Ax_s_of_translatedHFFinAx hf)
      htranslated
  rwa [translateHFFormula_selfSuccInjectiveSentence] at hpa

/-- Term-parametric form of self-successor injectivity on the translated
ordinal domain. -/
theorem BProv_Ax_s_hfAdjoinGraphTermAt_injective_self
    {G : List Formula} {a b out : Term}
    (ha : BProv Ax_s G
      (subst (instTerm a) codedOrdinalDomain))
    (hb : BProv Ax_s G
      (subst (instTerm b) codedOrdinalDomain))
    (hsuccA : BProv Ax_s G (hfAdjoinGraphTermAt out a a))
    (hsuccB : BProv Ax_s G (hfAdjoinGraphTermAt out b b)) :
    BProv Ax_s G (eq a b) := by
  have hall : BProv Ax_s G selfSuccInjectivePAFormula :=
    BProv_Ax_s_selfSuccInjectiveSentence
  have haRaw := BProv_allE (B := Ax_s) (G := G) (t := a) hall
  have hbRaw := BProv_allE (B := Ax_s) (G := G) (t := b) haRaw
  have houtRaw := BProv_allE (B := Ax_s) (G := G) (t := out) hbRaw
  have hrename :
      rename (fun n : Nat ↦ n + 2) codedOrdinalDomain =
        rename Nat.succ (rename Nat.succ codedOrdinalDomain) := by
    rw [rename_comp]
  have haNorm :
      subst (instTerm out)
          (subst (Term.upSubst (instTerm b))
            (subst (Term.upSubst (Term.upSubst (instTerm a)))
              (rename (fun n : Nat ↦ n + 2) codedOrdinalDomain))) =
        subst (instTerm a) codedOrdinalDomain := by
    rw [hrename]
    rw [subst_rename_succ_up]
    rw [subst_rename_succ_up]
    rw [subst_rename_succ_up]
    rw [subst_instTerm_rename_succ]
    rw [subst_instTerm_rename_succ]
  have hbNorm :
      subst (instTerm b)
          (subst (Term.upSubst (instTerm a)) codedOrdinalDomain) =
        subst (instTerm b) codedOrdinalDomain := by
    rw [subst_up_inst_codedOrdinalDomain]
  have houtExpanded : BProv Ax_s G
      (imp
        (subst (instTerm out)
          (subst (Term.upSubst (instTerm b))
            (subst (Term.upSubst (Term.upSubst (instTerm a)))
              (rename (fun n : Nat ↦ n + 2) codedOrdinalDomain))))
        (imp
          (subst (instTerm b)
            (subst (Term.upSubst (instTerm a)) codedOrdinalDomain))
          (imp
            (hfAdjoinGraphTermAt out a a)
            (imp
              (hfAdjoinGraphTermAt out b b)
              (eq a b))))) := by
    simpa [hfAdjoinGraphAt, subst_hfAdjoinGraphTermAt,
      subst, instTerm, Term.subst, Term.upSubst,
      Term.subst_rename_succ_up,
      term_subst_instTerm_rename_succ,
      subst_rename_succ_up,
      subst_instTerm_rename_succ] using houtRaw
  rw [haNorm, hbNorm] at houtExpanded
  exact BProv_mp Ax_s G _ _
    (BProv_mp Ax_s G _ _
      (BProv_mp Ax_s G _ _
        (BProv_mp Ax_s G _ _ houtExpanded ha) hb) hsuccA) hsuccB

/-- No HF self-successor can be empty. -/
def HF_selfSuccNonemptySentence : SetTheory.Form :=
  SetTheory.Form.fAll (SetTheory.Form.fAll
    (SetTheory.Form.fImp
      (AckermannHF.HF_succAt 0 1)
      (SetTheory.Form.fImp
        (AckermannHF.HF_emptyAt 0)
        SetTheory.Form.fBot)))

theorem HF_selfSuccNonemptySentence_sentence :
    SetTheory.Sentence HF_selfSuccNonemptySentence := by
  intro i hi
  simp [HF_selfSuccNonemptySentence,
    AckermannHF.HF_succAt,
    AckermannHF.HF_adjoinAt,
    AckermannHF.HF_emptyAt,
    SetTheory.fIff, SetTheory.Free] at hi

theorem BProv_HFFin_selfSuccNonemptySentence :
    SetTheory.BProv AckermannHF.HFFinAx_s []
      HF_selfSuccNonemptySentence := by
  apply SetTheory.completeness_inf AckermannHF.HFFinAx_s
  · exact AckermannHF.Sentences_HFFin
  · exact HF_selfSuccNonemptySentence_sentence
  · intro Dom mem v hHF
    let M := AckermannHF.firstOrderFiniteAdjunctionModel_of_HFFinAx_s v hHF
    intro a out hsucc hempty
    have hsucc' : out = M.adjoin a a :=
      (AckermannHF.FirstOrderAdjunctionModel.HF_succAt_spec
        M.toFirstOrderAdjunctionModel
        (SetTheory.scons out (SetTheory.scons a v)) 0 1).mp hsucc
    have hempty' : out = M.empty :=
      (AckermannHF.FirstOrderAdjunctionModel.HF_emptyAt_empty
        M.toFirstOrderAdjunctionModel
        (SetTheory.scons out (SetTheory.scons a v)) 0).mp hempty
    have hEq : M.adjoin a a = M.empty := hsucc'.symm.trans hempty'
    have haMem : M.mem a (M.adjoin a a) :=
      (M.adjoin_spec a a a).mpr (Or.inr rfl)
    rw [hEq] at haMem
    exact M.empty_spec a haMem

theorem translateHFFormula_selfSuccNonemptySentence :
    translateHFFormula HF_selfSuccNonemptySentence =
      all (all
        (imp
          (hfAdjoinGraphAt 0 1 1)
          (imp (hfEmptyAt 0) bot))) := by
  rfl

theorem BProv_Ax_s_selfSuccNonemptySentence {G : List Formula} :
    BProv Ax_s G
      (all (all
        (imp
          (hfAdjoinGraphAt 0 1 1)
          (imp (hfEmptyAt 0) bot)))) := by
  apply BProv_weaken_nil
  have htranslated : BProv translatedHFFinAx []
      (translateHFFormula HF_selfSuccNonemptySentence) :=
    BProv_translateHFFormula_of_BProv_HFFin
      BProv_HFFin_selfSuccNonemptySentence
  have hpa : BProv Ax_s []
      (translateHFFormula HF_selfSuccNonemptySentence) :=
    BProv_lift_translatedHFFinAx_to_PA
      (fun f hf => BProv_Ax_s_of_translatedHFFinAx hf)
      htranslated
  rwa [translateHFFormula_selfSuccNonemptySentence] at hpa

theorem BProv_Ax_s_bot_of_hfAdjoinGraphTermAt_hfEmptyTermAt
    {G : List Formula} {a out : Term}
    (hsucc : BProv Ax_s G (hfAdjoinGraphTermAt out a a))
    (hempty : BProv Ax_s G (hfEmptyTermAt out)) :
    BProv Ax_s G bot := by
  have hall : BProv Ax_s G
      (all (all
        (imp
          (hfAdjoinGraphAt 0 1 1)
          (imp (hfEmptyAt 0) bot)))) :=
    BProv_Ax_s_selfSuccNonemptySentence
  have haRaw := BProv_allE (B := Ax_s) (G := G) (t := a) hall
  have houtRaw := BProv_allE (B := Ax_s) (G := G) (t := out) haRaw
  have himp : BProv Ax_s G
      (imp
        (hfAdjoinGraphTermAt out a a)
        (imp (hfEmptyTermAt out) bot)) := by
    simpa [hfAdjoinGraphAt, hfEmptyAt,
      subst_hfAdjoinGraphTermAt, subst_hfEmptyTermAt,
      subst, instTerm, Term.subst, Term.upSubst,
      Term.subst_rename_succ_up,
      term_subst_instTerm_rename_succ] using houtRaw
  exact BProv_mp Ax_s G _ _
    (BProv_mp Ax_s G _ _ himp hsucc) hempty

/-- Direct term-level use of the already proved graph-codomain induction. -/
theorem BProv_Ax_s_codedOrdinalDomain_of_ordinalCodeGraphTermAt
    {G : List Formula} {raw coded : Term}
    (hgraph : BProv Ax_s G (ordinalCodeGraphTermAt raw coded)) :
    BProv Ax_s G (subst (instTerm coded) codedOrdinalDomain) := by
  have hall : BProv Ax_s G
      (all (ordinalCodeCodomainTermAt (Term.var 0))) :=
    BProv_Ax_s_all_ordinalCodeCodomain
  have hrawRaw := BProv_allE
    (B := Ax_s) (G := G) (t := raw) hall
  have hraw : BProv Ax_s G (ordinalCodeCodomainTermAt raw) := by
    simpa [subst_ordinalCodeCodomainTermAt,
      instTerm, Term.subst] using hrawRaw
  have hcodedRaw := BProv_allE
    (B := Ax_s) (G := G) (t := coded) hraw
  have himp : BProv Ax_s G
      (imp
        (ordinalCodeGraphTermAt raw coded)
        (subst (instTerm coded) codedOrdinalDomain)) := by
    simpa [ordinalCodeCodomainTermAt,
      subst_ordinalCodeGraphTermAt,
      subst, instTerm, Term.subst,
      term_subst_instTerm_rename_succ] using hcodedRaw
  exact BProv_mp Ax_s G _ _ himp hgraph

/-- A zero-stage trace and a successor-stage trace cannot have the same
endpoint. -/
theorem BProv_Ax_s_bot_of_ordinalCodeGraphTermAt_zero_succ
    {G : List Formula} {raw coded : Term}
    (hzero : BProv Ax_s G
      (ordinalCodeGraphTermAt Term.zero coded))
    (hsucc : BProv Ax_s G
      (ordinalCodeGraphTermAt (Term.succ raw) coded)) :
    BProv Ax_s G bot := by
  have hcodedZero : BProv Ax_s G (eq coded Term.zero) :=
    BProv_Ax_s_eq_zero_of_ordinalCodeGraphTermAt_zero hzero
  have hedge : BProv Ax_s G
      (ordinalCodePredEdgeTermAt raw coded) :=
    BProv_Ax_s_ordinalCodePredEdgeTermAt_of_succ_graph hsucc
  let edgeBody : Formula :=
    and
      (ordinalCodeGraphTermAt
        (Term.rename Nat.succ raw) (Term.var 0))
      (hfAdjoinGraphTermAt
        (Term.rename Nat.succ coded) (Term.var 0) (Term.var 0))
  let C : List Formula := edgeBody :: G.map (rename Nat.succ)
  have hopened : BProv Ax_s C (rename Nat.succ bot) := by
    have hedgeBody : BProv Ax_s C edgeBody :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hadjoin : BProv Ax_s C
        (hfAdjoinGraphTermAt
          (Term.rename Nat.succ coded) (Term.var 0) (Term.var 0)) := by
      simpa [edgeBody] using BProv_andE2 hedgeBody
    have hcodedZeroRen := BProv_rename_of_sentences
      (B := Ax_s) Ax_s_sentences
      hcodedZero Nat.succ
    have hcodedZeroC : BProv Ax_s C
        (eq (Term.rename Nat.succ coded) Term.zero) := by
      have hctx := BProv_context_cons
        (B := Ax_s) (a := edgeBody) hcodedZeroRen
      simpa [C, rename, Term.rename] using hctx
    have hadjoinZero : BProv Ax_s C
        (hfAdjoinGraphTermAt
          Term.zero (Term.var 0) (Term.var 0)) :=
      BProv_hfAdjoinGraphTermAt_of_new_eq_term
        hadjoin hcodedZeroC
    have hempty : BProv Ax_s C (hfEmptyTermAt Term.zero) :=
      BProv_Ax_s_hfEmptyTermAt_zero
    simpa [rename] using
      (BProv_Ax_s_bot_of_hfAdjoinGraphTermAt_hfEmptyTermAt
        hadjoinZero hempty)
  exact BProv_exE_of_sentences
    (B := Ax_s) Ax_s_sentences
    (G := G) (a := edgeBody) (c := bot)
    (by simpa [ordinalCodePredEdgeTermAt, edgeBody] using hedge)
    (by simpa [C, rename] using hopened)

/-- The zero-stage trace has no raw preimage other than zero. -/
theorem BProv_Ax_s_eq_zero_of_ordinalCodeGraphTermAt_common
    {G : List Formula} {raw coded : Term}
    (hzero : BProv Ax_s G
      (ordinalCodeGraphTermAt Term.zero coded))
    (hraw : BProv Ax_s G
      (ordinalCodeGraphTermAt raw coded)) :
    BProv Ax_s G (eq Term.zero raw) := by
  let target : Formula := eq Term.zero raw
  let succBody : Formula :=
    eq (Term.rename Nat.succ raw) (Term.succ (Term.var 0))
  have hcases : BProv Ax_s G
      (or
        (eq raw Term.zero)
        (ex succBody)) := by
    simpa [succBody] using
      (BProv_Ax_s_zeroOrSuccPred_term (G := G) raw)
  have hzeroBranch : BProv Ax_s
      (eq raw Term.zero :: G) target := by
    have heq : BProv Ax_s (eq raw Term.zero :: G)
        (eq raw Term.zero) :=
      BProv_ass (B := Ax_s) (G := eq raw Term.zero :: G) (by simp)
    simpa [target] using BProv_eqSym heq
  have hsuccBranch : BProv Ax_s (ex succBody :: G) target := by
    let H : List Formula := ex succBody :: G
    let C : List Formula := succBody :: H.map (rename Nat.succ)
    have hopened : BProv Ax_s C (rename Nat.succ target) := by
      have hsuccEq : BProv Ax_s C succBody :=
        BProv_ass (B := Ax_s) (G := C) (by simp [C])
      have lift : ∀ {phi : Formula}, BProv Ax_s G phi →
          BProv Ax_s C (rename Nat.succ phi) := by
        intro phi hphi
        have hren := BProv_rename_of_sentences
          (B := Ax_s) Ax_s_sentences
          hphi Nat.succ
        have hinnerCtx := BProv_context_cons
          (B := Ax_s) (a := rename Nat.succ (ex succBody)) hren
        have hbodyCtx := BProv_context_cons
          (B := Ax_s) (a := succBody) hinnerCtx
        simpa [C, H] using hbodyCtx
      have hzeroC : BProv Ax_s C
          (ordinalCodeGraphTermAt
            Term.zero (Term.rename Nat.succ coded)) := by
        have h := lift hzero
        simpa [rename_ordinalCodeGraphTermAt,
          rename, Term.rename] using h
      have hrawC : BProv Ax_s C
          (ordinalCodeGraphTermAt
            (Term.rename Nat.succ raw)
            (Term.rename Nat.succ coded)) := by
        have h := lift hraw
        simpa [rename_ordinalCodeGraphTermAt] using h
      have hsuccC : BProv Ax_s C
          (ordinalCodeGraphTermAt
            (Term.succ (Term.var 0))
            (Term.rename Nat.succ coded)) :=
        BProv_ordinalCodeGraphTermAt_congr_raw hsuccEq hrawC
      have hbot : BProv Ax_s C bot :=
        BProv_Ax_s_bot_of_ordinalCodeGraphTermAt_zero_succ
          hzeroC hsuccC
      exact BProv_botE hbot
    exact BProv_exE_of_sentences
      (B := Ax_s) Ax_s_sentences
      (G := H) (a := succBody) (c := target)
      (BProv_ass (B := Ax_s) (G := H) (by simp [H]))
      (by simpa [C] using hopened)
  exact BProv_orE hcases
    (by simpa [target] using hzeroBranch)
    (by simpa [target, succBody] using hsuccBranch)

/-- Induction invariant at a raw input: every other raw input with the same
ordinal-code endpoint is equal to it.  The outer binder is the competing raw
input and the inner binder is the common endpoint. -/
def ordinalCodeInjectiveTermAt (raw : Term) : Formula :=
  all (all
    (imp
      (ordinalCodeGraphTermAt
        (Term.rename Nat.succ (Term.rename Nat.succ raw))
        (Term.var 0))
      (imp
        (ordinalCodeGraphTermAt (Term.var 1) (Term.var 0))
        (eq
          (Term.rename Nat.succ (Term.rename Nat.succ raw))
          (Term.var 1)))))

theorem subst_ordinalCodeInjectiveTermAt
    (sigma : Nat → Term) (raw : Term) :
    subst sigma (ordinalCodeInjectiveTermAt raw) =
      ordinalCodeInjectiveTermAt (Term.subst sigma raw) := by
  have hraw :
      Term.subst (Term.upSubst (Term.upSubst sigma))
          (Term.rename Nat.succ (Term.rename Nat.succ raw)) =
        Term.rename Nat.succ
          (Term.rename Nat.succ (Term.subst sigma raw)) := by
    rw [Term.subst_rename_succ_up]
    rw [Term.subst_rename_succ_up]
  simp [ordinalCodeInjectiveTermAt,
    subst_ordinalCodeGraphTermAt,
    subst, Term.subst, Term.upSubst,
    Term.rename, hraw]

theorem rename_ordinalCodeInjectiveTermAt
    (r : Nat → Nat) (raw : Term) :
    rename r (ordinalCodeInjectiveTermAt raw) =
      ordinalCodeInjectiveTermAt (Term.rename r raw) := by
  rw [← subst_var_rename]
  simpa [term_subst_var_rename] using
    (subst_ordinalCodeInjectiveTermAt
      (fun n => Term.var (r n)) raw)

/-- Instantiate the universal induction invariant at explicit competing raw
and endpoint terms. -/
theorem BProv_eq_of_ordinalCodeInjectiveTermAt
    {G : List Formula} {left right coded : Term}
    (hinjective : BProv Ax_s G
      (ordinalCodeInjectiveTermAt left))
    (hleft : BProv Ax_s G
      (ordinalCodeGraphTermAt left coded))
    (hright : BProv Ax_s G
      (ordinalCodeGraphTermAt right coded)) :
    BProv Ax_s G (eq left right) := by
  have hrightRaw := BProv_allE
    (B := Ax_s) (G := G) (t := right) hinjective
  have hcodedRaw := BProv_allE
    (B := Ax_s) (G := G) (t := coded) hrightRaw
  have himp : BProv Ax_s G
      (imp
        (ordinalCodeGraphTermAt left coded)
        (imp
          (ordinalCodeGraphTermAt right coded)
          (eq left right))) := by
    simpa [ordinalCodeInjectiveTermAt,
      subst_ordinalCodeGraphTermAt,
      subst, instTerm, Term.subst, Term.upSubst,
      Term.subst_rename_succ_up,
      term_subst_instTerm_rename_succ] using hcodedRaw
  exact BProv_mp Ax_s G _ _
    (BProv_mp Ax_s G _ _ himp hleft) hright

/-- Base case of the raw-side injectivity induction. -/
theorem BProv_Ax_s_ordinalCodeInjectiveTermAt_zero
    {G : List Formula} :
    BProv Ax_s G
      (ordinalCodeInjectiveTermAt Term.zero) := by
  let Q₁ : List Formula := G.map (rename Nat.succ)
  let Q₂ : List Formula := Q₁.map (rename Nat.succ)
  let leftGraph : Formula :=
    ordinalCodeGraphTermAt Term.zero (Term.var 0)
  let rightGraph : Formula :=
    ordinalCodeGraphTermAt (Term.var 1) (Term.var 0)
  let target : Formula := eq Term.zero (Term.var 1)
  have hbody : BProv Ax_s Q₂
      (imp leftGraph (imp rightGraph target)) := by
    let C : List Formula := leftGraph :: Q₂
    let D : List Formula := rightGraph :: C
    have hleft : BProv Ax_s D leftGraph :=
      BProv_ass (B := Ax_s) (G := D) (by simp [D, C])
    have hright : BProv Ax_s D rightGraph :=
      BProv_ass (B := Ax_s) (G := D) (by simp [D])
    have heq : BProv Ax_s D target := by
      simpa [leftGraph, rightGraph, target] using
        (BProv_Ax_s_eq_zero_of_ordinalCodeGraphTermAt_common
          hleft hright)
    have hrightImp : BProv Ax_s C (imp rightGraph target) := by
      simpa [D] using BProv_impI heq
    simpa [C] using BProv_impI hrightImp
  have hinner : BProv Ax_s Q₁
      (all (imp
        (ordinalCodeGraphTermAt Term.zero (Term.var 0))
        (imp
          (ordinalCodeGraphTermAt (Term.var 1) (Term.var 0))
          (eq Term.zero (Term.var 1))))) := by
    simpa [Q₂, leftGraph, rightGraph, target] using
      (BProv_allI_of_sentences
        (B := Ax_s) (G := Q₁)
        Ax_s_sentences hbody)
  have houter := BProv_allI_of_sentences
    (B := Ax_s) (G := G)
    Ax_s_sentences hinner
  simpa [ordinalCodeInjectiveTermAt,
    Q₁, Term.rename] using houter

/-- If the injectivity invariant holds at both predecessors, equality of the
two successor-stage endpoints forces equality of the successor raw inputs. -/
theorem BProv_Ax_s_eq_succ_of_common_ordinalCodeGraphs
    {G : List Formula} {left right coded : Term}
    (hinjective : BProv Ax_s G
      (ordinalCodeInjectiveTermAt left))
    (hleft : BProv Ax_s G
      (ordinalCodeGraphTermAt (Term.succ left) coded))
    (hright : BProv Ax_s G
      (ordinalCodeGraphTermAt (Term.succ right) coded)) :
    BProv Ax_s G (eq (Term.succ left) (Term.succ right)) := by
  let target : Formula := eq (Term.succ left) (Term.succ right)
  have hedgeLeft : BProv Ax_s G
      (ordinalCodePredEdgeTermAt left coded) :=
    BProv_Ax_s_ordinalCodePredEdgeTermAt_of_succ_graph hleft
  have hedgeRight : BProv Ax_s G
      (ordinalCodePredEdgeTermAt right coded) :=
    BProv_Ax_s_ordinalCodePredEdgeTermAt_of_succ_graph hright
  let left₁ : Term := Term.rename Nat.succ left
  let right₁ : Term := Term.rename Nat.succ right
  let coded₁ : Term := Term.rename Nat.succ coded
  let leftBody : Formula :=
    and
      (ordinalCodeGraphTermAt left₁ (Term.var 0))
      (hfAdjoinGraphTermAt coded₁ (Term.var 0) (Term.var 0))
  let C : List Formula := leftBody :: G.map (rename Nat.succ)
  have hopenedLeft : BProv Ax_s C (rename Nat.succ target) := by
    have hleftBody : BProv Ax_s C leftBody :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hleftPred : BProv Ax_s C
        (ordinalCodeGraphTermAt left₁ (Term.var 0)) := by
      simpa [leftBody] using BProv_andE1 hleftBody
    have hleftAdjoin : BProv Ax_s C
        (hfAdjoinGraphTermAt coded₁ (Term.var 0) (Term.var 0)) := by
      simpa [leftBody] using BProv_andE2 hleftBody
    have hedgeRightRen := BProv_rename_of_sentences
      (B := Ax_s) Ax_s_sentences
      hedgeRight Nat.succ
    have hedgeRightC : BProv Ax_s C
        (ordinalCodePredEdgeTermAt right₁ coded₁) := by
      have hctx := BProv_context_cons
        (B := Ax_s) (a := leftBody) hedgeRightRen
      simpa [C, right₁, coded₁,
        ordinalCodePredEdgeTermAt,
        rename_ordinalCodeGraphTermAt,
        rename_hfAdjoinGraphTermAt,
        rename, Term.rename, Term.rename_comp,
        Function.comp_def, SetTheory.up, Nat.add_assoc] using hctx
    let left₂ : Term := Term.rename Nat.succ left₁
    let right₂ : Term := Term.rename Nat.succ right₁
    let coded₂ : Term := Term.rename Nat.succ coded₁
    let rightBody : Formula :=
      and
        (ordinalCodeGraphTermAt right₂ (Term.var 0))
        (hfAdjoinGraphTermAt coded₂ (Term.var 0) (Term.var 0))
    let D : List Formula := rightBody :: C.map (rename Nat.succ)
    have hopenedRight : BProv Ax_s D
        (rename Nat.succ (rename Nat.succ target)) := by
      have hrightBody : BProv Ax_s D rightBody :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D])
      have hrightPred : BProv Ax_s D
          (ordinalCodeGraphTermAt right₂ (Term.var 0)) := by
        simpa [rightBody] using BProv_andE1 hrightBody
      have hrightAdjoin : BProv Ax_s D
          (hfAdjoinGraphTermAt coded₂ (Term.var 0) (Term.var 0)) := by
        simpa [rightBody] using BProv_andE2 hrightBody
      have hleftBodyRen : BProv Ax_s D (rename Nat.succ leftBody) :=
        BProv_ass (B := Ax_s) (G := D) (by simp [D, C])
      have hleftPredD : BProv Ax_s D
          (ordinalCodeGraphTermAt left₂ (Term.var 1)) := by
        have h := BProv_andE1 hleftBodyRen
        simpa [leftBody, left₁, left₂,
          rename_ordinalCodeGraphTermAt,
          rename, Term.rename, Term.rename_comp,
          Function.comp_def] using h
      have hleftAdjoinD : BProv Ax_s D
          (hfAdjoinGraphTermAt coded₂ (Term.var 1) (Term.var 1)) := by
        have h := BProv_andE2 hleftBodyRen
        simpa [leftBody, coded₁, coded₂,
          rename_hfAdjoinGraphTermAt,
          rename, Term.rename, Term.rename_comp,
          Function.comp_def] using h
      have hleftDomain : BProv Ax_s D
          (subst (instTerm (Term.var 1)) codedOrdinalDomain) :=
        BProv_Ax_s_codedOrdinalDomain_of_ordinalCodeGraphTermAt
          hleftPredD
      have hrightDomain : BProv Ax_s D
          (subst (instTerm (Term.var 0)) codedOrdinalDomain) :=
        BProv_Ax_s_codedOrdinalDomain_of_ordinalCodeGraphTermAt
          hrightPred
      have hcodedEq : BProv Ax_s D
          (eq (Term.var 1) (Term.var 0)) :=
        BProv_Ax_s_hfAdjoinGraphTermAt_injective_self
          hleftDomain hrightDomain hleftAdjoinD hrightAdjoin
      have hrightPred' : BProv Ax_s D
          (ordinalCodeGraphTermAt right₂ (Term.var 1)) :=
        BProv_ordinalCodeGraphTermAt_congr_coded
          (BProv_eqSym hcodedEq) hrightPred
      have hinjectiveRen₂ := BProv_iterRenameSucc_of_sentences
        (B := Ax_s) Ax_s_sentences
        2 hinjective
      have hinjectiveD : BProv Ax_s D
          (ordinalCodeInjectiveTermAt left₂) := by
        have hleftCtx := BProv_context_cons
          (B := Ax_s) (a := rename Nat.succ leftBody) hinjectiveRen₂
        have hrightCtx := BProv_context_cons
          (B := Ax_s) (a := rightBody) hleftCtx
        simpa [D, C, left₁, left₂,
          iterRenameContextSucc, iterRenameSucc,
          rename_ordinalCodeInjectiveTermAt,
          Term.rename_comp, Function.comp_def] using hrightCtx
      have hrawEq : BProv Ax_s D (eq left₂ right₂) :=
        BProv_eq_of_ordinalCodeInjectiveTermAt
          hinjectiveD hleftPredD hrightPred'
      have hsuccEq := BProv_eq_congr_succ hrawEq
      simpa [target, left₁, right₁, left₂, right₂,
        rename, Term.rename, Term.rename_comp,
        Function.comp_def] using hsuccEq
    have hresultC : BProv Ax_s C (rename Nat.succ target) :=
      BProv_exE_of_sentences
        (B := Ax_s) Ax_s_sentences
        (G := C) (a := rightBody) (c := rename Nat.succ target)
        (by simpa [ordinalCodePredEdgeTermAt,
            rightBody, right₁, right₂, coded₁, coded₂,
            Term.rename] using hedgeRightC)
        (by simpa [D] using hopenedRight)
    exact hresultC
  exact BProv_exE_of_sentences
    (B := Ax_s) Ax_s_sentences
    (G := G) (a := leftBody) (c := target)
    (by simpa [ordinalCodePredEdgeTermAt,
        leftBody, left₁, coded₁, Term.rename] using hedgeLeft)
    (by simpa [C] using hopenedLeft)

/-- Successor step of the raw-side injectivity induction. -/
theorem BProv_Ax_s_ordinalCodeInjectiveTermAt_succ
    {G : List Formula} {raw : Term}
    (hinjective : BProv Ax_s G
      (ordinalCodeInjectiveTermAt raw)) :
    BProv Ax_s G
      (ordinalCodeInjectiveTermAt (Term.succ raw)) := by
  let Q₁ : List Formula := G.map (rename Nat.succ)
  let Q₂ : List Formula := Q₁.map (rename Nat.succ)
  let raw₂ : Term := Term.rename Nat.succ (Term.rename Nat.succ raw)
  let leftGraph : Formula :=
    ordinalCodeGraphTermAt (Term.succ raw₂) (Term.var 0)
  let rightGraph : Formula :=
    ordinalCodeGraphTermAt (Term.var 1) (Term.var 0)
  let target : Formula := eq (Term.succ raw₂) (Term.var 1)
  have hinjectiveRen₂ := BProv_iterRenameSucc_of_sentences
    (B := Ax_s) Ax_s_sentences
    2 hinjective
  have hinjectiveQ₂ : BProv Ax_s Q₂
      (ordinalCodeInjectiveTermAt raw₂) := by
    simpa [Q₁, Q₂, raw₂, iterRenameContextSucc, iterRenameSucc,
      rename_ordinalCodeInjectiveTermAt,
      Term.rename_comp, Function.comp_def] using hinjectiveRen₂
  have hbody : BProv Ax_s Q₂
      (imp leftGraph (imp rightGraph target)) := by
    let C : List Formula := leftGraph :: Q₂
    let D : List Formula := rightGraph :: C
    have hleft : BProv Ax_s D leftGraph :=
      BProv_ass (B := Ax_s) (G := D) (by simp [D, C])
    have hright : BProv Ax_s D rightGraph :=
      BProv_ass (B := Ax_s) (G := D) (by simp [D])
    have hcases : BProv Ax_s D
        (or
          (eq (Term.var 1) Term.zero)
          (ex (eq
            (Term.rename Nat.succ (Term.var 1))
            (Term.succ (Term.var 0))))) :=
      BProv_Ax_s_zeroOrSuccPred_term (G := D) (Term.var 1)
    have hzeroBranch : BProv Ax_s
        (eq (Term.var 1) Term.zero :: D) target := by
      let Z : List Formula := eq (Term.var 1) Term.zero :: D
      have heq : BProv Ax_s Z (eq (Term.var 1) Term.zero) :=
        BProv_ass (B := Ax_s) (G := Z) (by simp [Z])
      have hleftZ : BProv Ax_s Z leftGraph :=
        BProv_ass (B := Ax_s) (G := Z) (by simp [Z, D, C])
      have hrightZ : BProv Ax_s Z rightGraph :=
        BProv_ass (B := Ax_s) (G := Z) (by simp [Z, D])
      have hzeroGraph : BProv Ax_s Z
          (ordinalCodeGraphTermAt Term.zero (Term.var 0)) :=
        BProv_ordinalCodeGraphTermAt_congr_raw heq hrightZ
      have hbot : BProv Ax_s Z bot :=
        BProv_Ax_s_bot_of_ordinalCodeGraphTermAt_zero_succ
          hzeroGraph hleftZ
      exact BProv_botE hbot
    let succBody : Formula :=
      eq (Term.rename Nat.succ (Term.var 1))
        (Term.succ (Term.var 0))
    have hsuccBranch : BProv Ax_s (ex succBody :: D) target := by
      let H : List Formula := ex succBody :: D
      let E : List Formula := succBody :: H.map (rename Nat.succ)
      have hopened : BProv Ax_s E (rename Nat.succ target) := by
        have hsuccEq : BProv Ax_s E succBody :=
          BProv_ass (B := Ax_s) (G := E) (by simp [E])
        let raw₃ : Term := Term.rename Nat.succ raw₂
        have hleftE : BProv Ax_s E
            (ordinalCodeGraphTermAt
              (Term.succ raw₃) (Term.var 1)) := by
          have hraw : BProv Ax_s E (rename Nat.succ leftGraph) :=
            BProv_ass (B := Ax_s) (G := E) (by simp [E, H, D, C])
          simpa [leftGraph, raw₃,
            rename_ordinalCodeGraphTermAt,
            rename, Term.rename] using hraw
        have hrightE : BProv Ax_s E
            (ordinalCodeGraphTermAt (Term.var 2) (Term.var 1)) := by
          have hraw : BProv Ax_s E (rename Nat.succ rightGraph) :=
            BProv_ass (B := Ax_s) (G := E) (by simp [E, H, D])
          simpa [rightGraph,
            rename_ordinalCodeGraphTermAt,
            rename, Term.rename] using hraw
        have hrightSuccE : BProv Ax_s E
            (ordinalCodeGraphTermAt
              (Term.succ (Term.var 0)) (Term.var 1)) :=
          BProv_ordinalCodeGraphTermAt_congr_raw hsuccEq hrightE
        have hinjectiveRen₃ := BProv_rename_of_sentences
          (B := Ax_s) Ax_s_sentences
          hinjectiveQ₂ Nat.succ
        have hinjectiveE : BProv Ax_s E
            (ordinalCodeInjectiveTermAt raw₃) := by
          have hleftCtx := BProv_context_cons
            (B := Ax_s) (a := rename Nat.succ leftGraph) hinjectiveRen₃
          have hrightCtx := BProv_context_cons
            (B := Ax_s) (a := rename Nat.succ rightGraph) hleftCtx
          have hexCtx := BProv_context_cons
            (B := Ax_s) (a := rename Nat.succ (ex succBody)) hrightCtx
          have hbodyCtx := BProv_context_cons
            (B := Ax_s) (a := succBody) hexCtx
          simpa [E, H, D, C, raw₃,
            rename_ordinalCodeInjectiveTermAt] using hbodyCtx
        have hsuccRawEq : BProv Ax_s E
            (eq
              (Term.succ raw₃)
              (Term.succ (Term.var 0))) :=
          BProv_Ax_s_eq_succ_of_common_ordinalCodeGraphs
            hinjectiveE hleftE hrightSuccE
        have htarget : BProv Ax_s E
            (eq (Term.succ raw₃) (Term.var 2)) :=
          BProv_eqTrans hsuccRawEq (BProv_eqSym hsuccEq)
        simpa [target, raw₃,
          rename, Term.rename] using htarget
      exact BProv_exE_of_sentences
        (B := Ax_s) Ax_s_sentences
        (G := H) (a := succBody) (c := target)
        (BProv_ass (B := Ax_s) (G := H) (by simp [H]))
        (by simpa [E] using hopened)
    have heq : BProv Ax_s D target :=
      BProv_orE hcases
        (by simpa using hzeroBranch)
        (by simpa [succBody] using hsuccBranch)
    have hrightImp : BProv Ax_s C (imp rightGraph target) := by
      simpa [D] using BProv_impI heq
    simpa [C] using BProv_impI hrightImp
  have hinner : BProv Ax_s Q₁
      (all (imp leftGraph (imp rightGraph target))) := by
    simpa [Q₂] using
      (BProv_allI_of_sentences
        (B := Ax_s) (G := Q₁)
        Ax_s_sentences hbody)
  have houter := BProv_allI_of_sentences
    (B := Ax_s) (G := G)
    Ax_s_sentences hinner
  simpa [ordinalCodeInjectiveTermAt,
    Q₁, raw₂, leftGraph, rightGraph, target,
    Term.rename] using houter

/-- PA induction proves the raw-side injectivity invariant at every input. -/
theorem BProv_Ax_s_all_ordinalCodeInjective {G : List Formula} :
    BProv Ax_s G
      (all (ordinalCodeInjectiveTermAt (Term.var 0))) := by
  apply BProv_weaken_nil
  let phi : Formula :=
    ordinalCodeInjectiveTermAt (Term.var 0)
  have hzero : BProv Ax_s [] (subst substZero phi) := by
    have hbase :=
      BProv_Ax_s_ordinalCodeInjectiveTermAt_zero (G := [])
    simpa [phi, subst_ordinalCodeInjectiveTermAt,
      substZero, Term.subst] using hbase
  have hsuccImp : BProv Ax_s []
      (imp phi (subst substSuccVar phi)) := by
    let C : List Formula := [phi]
    have hih : BProv Ax_s C phi :=
      BProv_ass (B := Ax_s) (G := C) (by simp [C])
    have hnext : BProv Ax_s C
        (ordinalCodeInjectiveTermAt
          (Term.succ (Term.var 0))) :=
      BProv_Ax_s_ordinalCodeInjectiveTermAt_succ hih
    have hnextSub : BProv Ax_s C (subst substSuccVar phi) := by
      simpa [phi, subst_ordinalCodeInjectiveTermAt,
        substSuccVar, Term.subst] using hnext
    simpa [C] using BProv_impI hnextSub
  have hsucc : BProv Ax_s []
      (all (imp phi (subst substSuccVar phi))) :=
    BProv_allI_of_sentences
      (B := Ax_s) (G := [])
      Ax_s_sentences hsuccImp
  simpa [phi] using BProv_Ax_s_induction_rule hzero hsucc

/-- Exact closure of the sole remaining ordinal-code graph law. -/
theorem ordinalCodeGraphInjective :
    OrdinalCodeGraphInjective := by
  intro G raw₁ raw₂ coded hgraph₁ hgraph₂
  have hall : BProv Ax_s G
      (all (ordinalCodeInjectiveTermAt (Term.var 0))) :=
    BProv_Ax_s_all_ordinalCodeInjective
  have hpointRaw := BProv_allE
    (B := Ax_s) (G := G) (t := raw₁) hall
  have hpoint : BProv Ax_s G
      (ordinalCodeInjectiveTermAt raw₁) := by
    rw [subst_ordinalCodeInjectiveTermAt] at hpointRaw
    simpa [instTerm, Term.subst] using hpointRaw
  exact BProv_eq_of_ordinalCodeInjectiveTermAt
    hpoint hgraph₁ hgraph₂


/-- Concrete graph range reduces the remaining graph package to raw-side
injectivity alone. -/
theorem OrdinalCodeGraphRemainingProofs_of_injective
    (hinjective : OrdinalCodeGraphInjective) :
    OrdinalCodeGraphRemainingProofs where
  range := BProv_Ax_s_ordinalCodeGraph_range_exact
  injective := hinjective

/-- The remaining graph laws plus four term-operation laws construct the
complete package; graph totality is already unconditional. -/
theorem OrdinalCodeGraphProofs_of_remaining_and_compatibility
    (P : OrdinalCodeGraphRemainingProofs)
    (C : OrdinalCodeTermCompatibilityProofs) :
    OrdinalCodeGraphProofs where
  total := OrdinalCodeGraphProofs_total
  range := P.range
  injective := P.injective
  term_graph := fun G t rawMap codedMap codedOut hcode ↦
    BProv_Ax_s_term_graph_of_compatibility
      C t G rawMap codedMap codedOut hcode

/-- The entire ordinal-code graph package now reduces to raw injectivity and
the addition/multiplication term constructors. -/
theorem OrdinalCodeGraphProofs_of_injective_add_mul
    (hinjective : OrdinalCodeGraphInjective)
    (hadd : OrdinalCodeTermAddCompatibility)
    (hmul : OrdinalCodeTermMulCompatibility) :
    OrdinalCodeGraphProofs :=
  OrdinalCodeGraphProofs_of_remaining_and_compatibility
    (OrdinalCodeGraphRemainingProofs_of_injective hinjective)
    (OrdinalCodeTermCompatibilityProofs_of_add_mul hadd hmul)

/-- Convenience constructor exposing multiplication as the only explicit
argument to the otherwise concrete ordinal-code graph package. -/
theorem OrdinalCodeGraphProofs_of_mul
    (hmul : OrdinalCodeTermMulCompatibility) :
    OrdinalCodeGraphProofs :=
  OrdinalCodeGraphProofs_of_remaining_and_compatibility
    (OrdinalCodeGraphRemainingProofs_of_injective
      ordinalCodeGraphInjective)
    (OrdinalCodeTermCompatibilityProofs_of_mul hmul)

/-- Complete ordinal-code graph package for all PA term constructors. -/
theorem ordinalCodeGraphProofs : OrdinalCodeGraphProofs :=
  OrdinalCodeGraphProofs_of_mul ordinalCodeTermMulCompatibility

/-- Totality of the ordinal-code graph turns equality of raw terms into
relational equality of their codes. -/
theorem BProv_codeEqualityTermAt_of_eq
    (P : OrdinalCodeGraphProofs)
    {G : List Formula} {leftRaw rightRaw : Term}
    (heq : BProv Ax_s G (eq leftRaw rightRaw)) :
    BProv Ax_s G
      (codeEqualityTermAt leftRaw rightRaw) := by
  let graphBody : Formula :=
    ordinalCodeGraphTermAt
      (Term.rename Nat.succ leftRaw) (Term.var 0)
  have htotal : BProv Ax_s G (ex graphBody) := by
    simpa [graphBody] using P.total G leftRaw
  have hbody : BProv Ax_s
      (graphBody :: G.map (rename Nat.succ))
      (rename Nat.succ
        (codeEqualityTermAt leftRaw rightRaw)) := by
    let C : List Formula := graphBody :: G.map (rename Nat.succ)
    have hleft : BProv Ax_s C
        (ordinalCodeGraphTermAt
          (Term.rename Nat.succ leftRaw) (Term.var 0)) := by
      exact BProv_ass (B := Ax_s) (G := C) (by simp [C, graphBody])
    have heqShift : BProv Ax_s C
        (eq (Term.rename Nat.succ leftRaw)
          (Term.rename Nat.succ rightRaw)) := by
      simpa [C, rename, Term.rename] using
        (BProv_rename_succ_context_cons_of_sentences
          (B := Ax_s) Ax_s_sentences
          (a := graphBody) heq)
    have hright : BProv Ax_s C
        (ordinalCodeGraphTermAt
          (Term.rename Nat.succ rightRaw) (Term.var 0)) :=
      BProv_ordinalCodeGraphTermAt_congr_raw heqShift hleft
    have hcodes : BProv Ax_s C
        (codeEqualityTermAt
          (Term.rename Nat.succ leftRaw)
          (Term.rename Nat.succ rightRaw)) :=
      BProv_codeEqualityTermAt_of_components
        hleft hright (BProv_eqRefl (Term.var 0))
    simpa [C, rename_codeEqualityTermAt] using hcodes
  exact BProv_exE_of_sentences (B := Ax_s)
    Ax_s_sentences
    (a := graphBody)
    (c := codeEqualityTermAt leftRaw rightRaw)
    htotal hbody

/-- Injectivity of the ordinal-code graph recovers equality of raw terms from
relational equality of their codes. -/
theorem BProv_eq_of_codeEqualityTermAt
    (P : OrdinalCodeGraphProofs)
    {G : List Formula} {leftRaw rightRaw : Term}
    (hcodes : BProv Ax_s G
      (codeEqualityTermAt leftRaw rightRaw)) :
    BProv Ax_s G (eq leftRaw rightRaw) := by
  let body : Formula :=
    codeEqualityBodyTermAt
      (Term.var 1) (Term.var 0)
      (Term.rename (fun n ↦ n+2) leftRaw)
      (Term.rename (fun n ↦ n+2) rightRaw)
  let inner : Formula := ex body
  have houter : BProv Ax_s G (ex inner) := by
    simpa [codeEqualityTermAt, inner, body] using hcodes
  refine BProv_two_exE_of_sentences
    (B := Ax_s) Ax_s_sentences houter ?_
  let C : List Formula :=
    body :: (ex body :: G.map (rename Nat.succ)).map
      (rename Nat.succ)
  have hpacked : BProv Ax_s C body :=
    BProv_ass (B := Ax_s) (G := C) (by simp [C])
  have hleft : BProv Ax_s C
      (ordinalCodeGraphTermAt
        (Term.rename (fun n ↦ n+2) leftRaw)
        (Term.var 1)) := by
    simpa [body, codeEqualityBodyTermAt] using BProv_andE1 hpacked
  have hrightAndEq : BProv Ax_s C
      (and
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+2) rightRaw)
          (Term.var 0))
        (eq (Term.var 1) (Term.var 0))) := by
    simpa [body, codeEqualityBodyTermAt] using BProv_andE2 hpacked
  have hright : BProv Ax_s C
      (ordinalCodeGraphTermAt
        (Term.rename (fun n ↦ n+2) rightRaw)
        (Term.var 0)) :=
    BProv_andE1 hrightAndEq
  have heqCode : BProv Ax_s C
      (eq (Term.var 1) (Term.var 0)) :=
    BProv_andE2 hrightAndEq
  have hleftAtRightCode : BProv Ax_s C
      (ordinalCodeGraphTermAt
        (Term.rename (fun n ↦ n+2) leftRaw)
        (Term.var 0)) :=
    BProv_ordinalCodeGraphTermAt_congr_coded heqCode hleft
  have hraw : BProv Ax_s C
      (eq
        (Term.rename (fun n ↦ n+2) leftRaw)
        (Term.rename (fun n ↦ n+2) rightRaw)) :=
    P.injective hleftAtRightCode hright
  simpa [C, rename, Term.rename, Term.rename_comp,
    Function.comp_def] using hraw

/-- Raw equality is equivalent in PA to equality through existentially chosen
ordinal codes.  The forward direction uses graph totality; the reverse direction
uses graph injectivity. -/
theorem BProv_eq_iff_codeEqualityTermAt
    (P : OrdinalCodeGraphProofs)
    (G : List Formula) (leftRaw rightRaw : Term) :
    BProv Ax_s G
      (iffForm
        (eq leftRaw rightRaw)
        (codeEqualityTermAt leftRaw rightRaw)) := by
  have hforward : BProv Ax_s G
      (imp
        (eq leftRaw rightRaw)
        (codeEqualityTermAt leftRaw rightRaw)) := by
    apply BProv_impI
    exact BProv_codeEqualityTermAt_of_eq P
      (BProv_ass (B := Ax_s)
        (G := eq leftRaw rightRaw :: G) (by simp))
  have hreverse : BProv Ax_s G
      (imp
        (codeEqualityTermAt leftRaw rightRaw)
        (eq leftRaw rightRaw)) := by
    apply BProv_impI
    exact BProv_eq_of_codeEqualityTermAt P
      (BProv_ass (B := Ax_s)
        (G := codeEqualityTermAt leftRaw rightRaw :: G)
        (by simp))
  exact BProv_iffForm_intro hforward hreverse

/-! ### Composite equality atoms -/

/-- Normal form of a reverse-translated equality atom after opening its two
term-value witnesses. -/
def paCompositeEqBodyAt
    (codedMap : Nat → Nat) (left right : Term) : Formula :=
  and
    (compositeTermGraphAt 1 (fun n ↦ codedMap n + 2) left)
    (and
      (compositeTermGraphAt 0 (fun n ↦ codedMap n + 2) right)
      (eq (Term.var 1) (Term.var 0)))

theorem hfFormulaAt_termGraph_left_eq_composite
    (codedMap : Nat → Nat) (t : Term) :
    hfFormulaAt (hfUpVarMap (hfUpVarMap codedMap))
        (AckermannHF.PAInHF.termGraphAt (fun n ↦ n+2) 1 t) =
      compositeTermGraphAt 1 (fun n ↦ codedMap n + 2) t := by
  let graph : Form :=
    AckermannHF.PAInHF.termGraphAt (fun n ↦ n+1) 0 t
  have hgraph : SetTheory.rename Nat.succ graph =
      AckermannHF.PAInHF.termGraphAt (fun n ↦ n+2) 1 t := by
    simpa [graph] using
      (AckermannHF.PAInHF.termGraphAt_rename t
        (ρ := fun n ↦ n+1) (out := 0) (r := Nat.succ))
  rw [← hgraph]
  rw [hfFormulaAt_source_rename]
  apply hfFormulaAt_ext
  intro n
  cases n <;> rfl

theorem hfFormulaAt_termGraph_right_eq_composite
    (codedMap : Nat → Nat) (t : Term) :
    hfFormulaAt (hfUpVarMap (hfUpVarMap codedMap))
        (AckermannHF.PAInHF.termGraphAt (fun n ↦ n+2) 0 t) =
      compositeTermGraphAt 0 (fun n ↦ codedMap n + 2) t := by
  let graph : Form :=
    AckermannHF.PAInHF.termGraphAt (fun n ↦ n+1) 0 t
  have hgraph : SetTheory.rename (SetTheory.up Nat.succ) graph =
      AckermannHF.PAInHF.termGraphAt (fun n ↦ n+2) 0 t := by
    simpa [graph, SetTheory.up] using
      (AckermannHF.PAInHF.termGraphAt_rename t
        (ρ := fun n ↦ n+1) (out := 0)
        (r := SetTheory.up Nat.succ))
  rw [← hgraph]
  rw [hfFormulaAt_source_rename]
  apply hfFormulaAt_ext
  intro n
  cases n <;> rfl

theorem paCompositeAt_eq_normalForm
    (codedMap : Nat → Nat) (left right : Term) :
    paCompositeAt codedMap (eq left right) =
      ex (ex (paCompositeEqBodyAt codedMap left right)) := by
  simp [paCompositeAt, paCompositeEqBodyAt,
    AckermannHF.PAInHF.formulaAt, hfFormulaAt,
    hfUpVarMap,
    hfFormulaAt_termGraph_left_eq_composite,
    hfFormulaAt_termGraph_right_eq_composite]

theorem BProv_paCompositeAt_eq_iff_codeEqualityTermAt_of_termGraphs
    {G : List Formula} {left right rawLeft rawRight : Term}
    {codedMap : Nat → Nat}
    (hleft : BProv Ax_s
      ((G.map (rename Nat.succ)).map (rename Nat.succ))
      (iffForm
        (compositeTermGraphAt 1 (fun n ↦ codedMap n + 2) left)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+2) rawLeft) (Term.var 1))))
    (hright : BProv Ax_s
      ((G.map (rename Nat.succ)).map (rename Nat.succ))
      (iffForm
        (compositeTermGraphAt 0 (fun n ↦ codedMap n + 2) right)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+2) rawRight) (Term.var 0)))) :
    BProv Ax_s G
      (iffForm
        (paCompositeAt codedMap (eq left right))
        (codeEqualityTermAt rawLeft rawRight)) := by
  let G₂ : List Formula :=
    (G.map (rename Nat.succ)).map (rename Nat.succ)
  have heq : BProv Ax_s G₂
      (iffForm
        (eq (Term.var 1) (Term.var 0))
        (eq (Term.var 1) (Term.var 0))) :=
    BProv_iffForm_refl (eq (Term.var 1) (Term.var 0))
  have hbody : BProv Ax_s G₂
      (iffForm
        (paCompositeEqBodyAt codedMap left right)
        (codeEqualityBodyTermAt
          (Term.var 1) (Term.var 0)
          (Term.rename (fun n ↦ n+2) rawLeft)
          (Term.rename (fun n ↦ n+2) rawRight))) := by
    have hp := BProv_iffForm_and_congr hright heq
    have h := BProv_iffForm_and_congr hleft hp
    simpa [G₂, paCompositeEqBodyAt,
      codeEqualityBodyTermAt] using h
  have hinner : BProv Ax_s (G.map (rename Nat.succ))
      (iffForm
        (ex (paCompositeEqBodyAt codedMap left right))
        (ex (codeEqualityBodyTermAt
          (Term.var 1) (Term.var 0)
          (Term.rename (fun n ↦ n+2) rawLeft)
          (Term.rename (fun n ↦ n+2) rawRight)))) := by
    apply BProv_iffForm_ex_congr_of_sentences
      (B := Ax_s) (G := G.map (rename Nat.succ))
      Ax_s_sentences
    simpa [G₂] using hbody
  have houter := BProv_iffForm_ex_congr_of_sentences
    (B := Ax_s) (G := G)
    Ax_s_sentences hinner
  simpa [paCompositeAt_eq_normalForm,
    codeEqualityTermAt] using houter

/-- The equality-atom case of paired raw/coded structural induction. -/
theorem BProv_Ax_s_paCompositeAt_eq_exact
    (P : OrdinalCodeGraphProofs)
    (G : List Formula) (left right : Term)
    (rawMap codedMap : Nat → Nat)
    (hcode : ∀ n, Free n (eq left right) →
      BProv Ax_s G
        (ordinalCodeGraphAt (rawMap n) (codedMap n))) :
    BProv Ax_s G
      (iffForm
        (rename rawMap (eq left right))
        (paCompositeAt codedMap (eq left right))) := by
  let G₂ : List Formula :=
    (G.map (rename Nat.succ)).map (rename Nat.succ)
  let rawMap₂ : Nat → Nat := fun n ↦ rawMap n + 2
  let codedMap₂ : Nat → Nat := fun n ↦ codedMap n + 2
  have hcode₂ : ∀ n, Free n (eq left right) →
      BProv Ax_s G₂
        (ordinalCodeGraphAt (rawMap₂ n) (codedMap₂ n)) := by
    intro n hn
    have h₀ := hcode n hn
    have h₂ := BProv_iterRenameSucc_of_sentences
      (B := Ax_s) Ax_s_sentences
      2 h₀
    simpa [G₂, rawMap₂, codedMap₂, iterRenameContextSucc, iterRenameSucc,
      ordinalCodeGraphAt,
      rename_ordinalCodeGraphTermAt, Term.rename] using h₂
  have hleftRaw : ∀ n, Term.Free n left →
      BProv Ax_s G₂
        (ordinalCodeGraphAt (rawMap₂ n) (codedMap₂ n)) :=
    fun n hn ↦ hcode₂ n (Or.inl hn)
  have hrightRaw : ∀ n, Term.Free n right →
      BProv Ax_s G₂
        (ordinalCodeGraphAt (rawMap₂ n) (codedMap₂ n)) :=
    fun n hn ↦ hcode₂ n (Or.inr hn)
  have hleft₀ := P.term_graph G₂ left rawMap₂ codedMap₂ 1 hleftRaw
  have hright₀ := P.term_graph G₂ right rawMap₂ codedMap₂ 0 hrightRaw
  have hleft : BProv Ax_s G₂
      (iffForm
        (compositeTermGraphAt 1 (fun n ↦ codedMap n + 2) left)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+2) (Term.rename rawMap left))
          (Term.var 1))) := by
    simpa [rawMap₂, codedMap₂, Term.rename_comp,
      Function.comp_def, Nat.add_assoc] using hleft₀
  have hright : BProv Ax_s G₂
      (iffForm
        (compositeTermGraphAt 0 (fun n ↦ codedMap n + 2) right)
        (ordinalCodeGraphTermAt
          (Term.rename (fun n ↦ n+2) (Term.rename rawMap right))
          (Term.var 0))) := by
    simpa [rawMap₂, codedMap₂, Term.rename_comp,
      Function.comp_def, Nat.add_assoc] using hright₀
  have hcomposite :=
    BProv_paCompositeAt_eq_iff_codeEqualityTermAt_of_termGraphs
      (G := G) (left := left) (right := right)
      (rawLeft := Term.rename rawMap left)
      (rawRight := Term.rename rawMap right)
      (codedMap := codedMap) hleft hright
  have hraw := BProv_eq_iff_codeEqualityTermAt P G
    (Term.rename rawMap left) (Term.rename rawMap right)
  have h := BProv_iffForm_trans hraw
    (BProv_iffForm_symm hcomposite)
  simpa [rename] using h

/-! ### Paired-variable quantifier steps -/

/-- Forward half of the universal structural step: a raw universal statement
implies its coded, domain-relativized composite. -/
theorem BProv_Ax_s_paCompositeAt_all_forward
    (P : OrdinalCodeGraphProofs)
    (phi : Formula)
    (ih : ∀ (G : List Formula) (rawMap codedMap : Nat → Nat),
      (∀ n, Free n phi →
        BProv Ax_s G
          (ordinalCodeGraphAt (rawMap n) (codedMap n))) →
      BProv Ax_s G
        (iffForm (rename rawMap phi) (paCompositeAt codedMap phi)))
    (G : List Formula) (rawMap codedMap : Nat → Nat)
    (hcode : ∀ n, Free n (all phi) →
      BProv Ax_s G
        (ordinalCodeGraphAt (rawMap n) (codedMap n))) :
    BProv Ax_s G
      (imp (rename rawMap (all phi))
        (paCompositeAt codedMap (all phi))) := by
  let rawBody : Formula :=
    rename (AckermannHF.PAInHF.upVarMap rawMap) phi
  let codedBody : Formula :=
    paCompositeAt (hfUpVarMap codedMap) phi
  let rawAll : Formula := all rawBody
  let codedAll : Formula :=
    all (imp codedOrdinalDomain codedBody)
  let C₀ : List Formula := rawAll :: G
  let C₁ : List Formula := C₀.map (rename Nat.succ)
  let C₂ : List Formula := codedOrdinalDomain :: C₁
  have hcodedBody : BProv Ax_s C₂ codedBody := by
    have hdomain : BProv Ax_s C₂ codedOrdinalDomain :=
      BProv_ass (B := Ax_s) (G := C₂) (by simp [C₂])
    have hdomainInst : BProv Ax_s C₂
        (subst (instTerm (Term.var 0)) codedOrdinalDomain) := by
      simpa [subst_instTerm_var_zero_codedOrdinalDomain] using hdomain
    have hrange :=
      BProv_Ax_s_ordinalCodeGraph_range_of_domain P hdomainInst
    let graphBody : Formula :=
      ordinalCodeGraphTermAt (Term.var 0) (Term.var 1)
    have hrange' : BProv Ax_s C₂ (ex graphBody) := by
      simpa [graphBody, Term.rename] using hrange
    let C₃ : List Formula := graphBody :: C₂.map (rename Nat.succ)
    have hopened : BProv Ax_s C₃ (rename Nat.succ codedBody) := by
      have hgraph : BProv Ax_s C₃
          (ordinalCodeGraphAt 0 1) := by
        have hass : BProv Ax_s C₃ graphBody :=
          BProv_ass (B := Ax_s) (G := C₃) (by simp [C₃])
        simpa [graphBody, ordinalCodeGraphAt] using hass
      have hpaired : ∀ n, Free n phi →
          BProv Ax_s C₃
            (ordinalCodeGraphAt
              (rangeRawMap rawMap n)
              (rangeCodedMap codedMap n)) := by
        intro n hn
        cases n with
        | zero =>
            simpa [rangeRawMap, rangeCodedMap] using hgraph
        | succ n =>
            have h₀ := hcode n hn
            have h₂ := BProv_iterRenameSucc_of_sentences
              (B := Ax_s) Ax_s_sentences
              2 h₀
            have hrawCtx := BProv_context_cons (B := Ax_s)
              (a := rename Nat.succ (rename Nat.succ rawAll)) h₂
            have hdomainCtx := BProv_context_cons (B := Ax_s)
              (a := rename Nat.succ codedOrdinalDomain) hrawCtx
            have hctx := BProv_context_cons (B := Ax_s)
              (a := graphBody) hdomainCtx
            simpa [C₃, C₂, C₁, C₀,
              iterRenameContextSucc, iterRenameSucc,
              rangeRawMap, rangeCodedMap,
              ordinalCodeGraphAt, rename_ordinalCodeGraphTermAt,
              Term.rename, List.map_map, Function.comp_def] using hctx
      have hih := ih C₃
        (rangeRawMap rawMap)
        (rangeCodedMap codedMap) hpaired
      have hihForward : BProv Ax_s C₃
          (imp
            (rename (rangeRawMap rawMap) phi)
            (paCompositeAt (rangeCodedMap codedMap) phi)) := by
        simpa [iffForm] using BProv_andE1 hih
      have hall₀ : BProv Ax_s C₀ rawAll :=
        BProv_ass (B := Ax_s) (G := C₀) (by simp [C₀])
      have hall₂ := BProv_iterRenameSucc_of_sentences
        (B := Ax_s) Ax_s_sentences
        2 hall₀
      have hallDomainCtx := BProv_context_cons (B := Ax_s)
        (a := rename Nat.succ codedOrdinalDomain) hall₂
      have hallCtx := BProv_context_cons (B := Ax_s)
        (a := graphBody) hallDomainCtx
      have hallCtx' : BProv Ax_s C₃
          (all (rename (SetTheory.up Nat.succ)
            (rename (SetTheory.up Nat.succ) rawBody))) := by
        simpa [C₃, C₂, C₁, C₀, rawAll,
          iterRenameContextSucc, iterRenameSucc, rename] using hallCtx
      have hrawInst := BProv_allE (B := Ax_s) (G := C₃)
        (t := Term.var 0) hallCtx'
      have hraw : BProv Ax_s C₃
          (rename (rangeRawMap rawMap) phi) := by
        simpa [rawAll, rawBody, rename,
          subst_instTerm_range_rawBody] using hrawInst
      have hcomp : BProv Ax_s C₃
          (paCompositeAt (rangeCodedMap codedMap) phi) :=
        BProv_mp Ax_s C₃ _ _ hihForward hraw
      simpa [codedBody, rename_succ_paCompositeAt_up] using hcomp
    exact BProv_exE_of_sentences (B := Ax_s)
      Ax_s_sentences
      (a := graphBody) (c := codedBody) hrange' (by
        simpa [C₃] using hopened)
  have himp : BProv Ax_s C₁
      (imp codedOrdinalDomain codedBody) := by
    simpa [C₂] using BProv_impI hcodedBody
  have hall : BProv Ax_s C₀ codedAll := by
    simpa [codedAll, C₁] using
      (BProv_allI_of_sentences (B := Ax_s)
        Ax_s_sentences
        (G := C₀) himp)
  have hmain : BProv Ax_s G (imp rawAll codedAll) := by
    simpa [C₀] using BProv_impI hall
  have hup : AckermannHF.PAInHF.upVarMap rawMap =
      SetTheory.up rawMap := by
    funext n
    cases n <;> rfl
  have hmain' : BProv Ax_s G
      (imp (all (rename (SetTheory.up rawMap) phi)) codedAll) := by
    simpa [rawAll, rawBody, hup] using hmain
  simpa [codedAll, codedBody, rename,
    paCompositeAt_all_normalForm] using hmain'

/-- Reverse half of the universal structural step: totality supplies a code
for the freshly bound raw value, and range supplies the coded-domain premise. -/
theorem BProv_Ax_s_paCompositeAt_all_reverse
    (P : OrdinalCodeGraphProofs)
    (phi : Formula)
    (ih : ∀ (G : List Formula) (rawMap codedMap : Nat → Nat),
      (∀ n, Free n phi →
        BProv Ax_s G
          (ordinalCodeGraphAt (rawMap n) (codedMap n))) →
      BProv Ax_s G
        (iffForm (rename rawMap phi) (paCompositeAt codedMap phi)))
    (G : List Formula) (rawMap codedMap : Nat → Nat)
    (hcode : ∀ n, Free n (all phi) →
      BProv Ax_s G
        (ordinalCodeGraphAt (rawMap n) (codedMap n))) :
    BProv Ax_s G
      (imp (paCompositeAt codedMap (all phi))
        (rename rawMap (all phi))) := by
  let rawBody : Formula :=
    rename (AckermannHF.PAInHF.upVarMap rawMap) phi
  let codedBody : Formula :=
    paCompositeAt (hfUpVarMap codedMap) phi
  let rawAll : Formula := all rawBody
  let codedAll : Formula :=
    all (imp codedOrdinalDomain codedBody)
  let C₀ : List Formula := codedAll :: G
  let C₁ : List Formula := C₀.map (rename Nat.succ)
  have hrawBody : BProv Ax_s C₁ rawBody := by
    have htotal := P.total C₁ (Term.var 0)
    let graphBody : Formula :=
      ordinalCodeGraphTermAt (Term.var 1) (Term.var 0)
    have htotal' : BProv Ax_s C₁ (ex graphBody) := by
      simpa [graphBody, Term.rename] using htotal
    let C₂ : List Formula := graphBody :: C₁.map (rename Nat.succ)
    have hopened : BProv Ax_s C₂ (rename Nat.succ rawBody) := by
      have hgraphTerm : BProv Ax_s C₂
          (ordinalCodeGraphTermAt (Term.var 1) (Term.var 0)) := by
        have hass : BProv Ax_s C₂ graphBody :=
          BProv_ass (B := Ax_s) (G := C₂) (by simp [C₂])
        simpa [graphBody] using hass
      have hgraph : BProv Ax_s C₂
          (ordinalCodeGraphAt 1 0) := by
        simpa [ordinalCodeGraphAt] using hgraphTerm
      have hpaired : ∀ n, Free n phi →
          BProv Ax_s C₂
            (ordinalCodeGraphAt
              (totalRawMap rawMap n)
              (totalCodedMap codedMap n)) := by
        intro n hn
        cases n with
        | zero =>
            simpa [totalRawMap, totalCodedMap] using hgraph
        | succ n =>
            have h₀ := hcode n hn
            have h₂ := BProv_iterRenameSucc_of_sentences
              (B := Ax_s) Ax_s_sentences
              2 h₀
            have hcodedCtx := BProv_context_cons (B := Ax_s)
              (a := rename Nat.succ (rename Nat.succ codedAll)) h₂
            have hctx := BProv_context_cons (B := Ax_s)
              (a := graphBody) hcodedCtx
            simpa [C₂, C₁, C₀,
              iterRenameContextSucc, iterRenameSucc,
              totalRawMap, totalCodedMap,
              ordinalCodeGraphAt, rename_ordinalCodeGraphTermAt,
              Term.rename, List.map_map, Function.comp_def] using hctx
      have hih := ih C₂
        (totalRawMap rawMap)
        (totalCodedMap codedMap) hpaired
      have hihReverse : BProv Ax_s C₂
          (imp
            (paCompositeAt (totalCodedMap codedMap) phi)
            (rename (totalRawMap rawMap) phi)) := by
        simpa [iffForm] using BProv_andE2 hih
      have hall₀ : BProv Ax_s C₀ codedAll :=
        BProv_ass (B := Ax_s) (G := C₀) (by simp [C₀])
      have hall₂ := BProv_iterRenameSucc_of_sentences
        (B := Ax_s) Ax_s_sentences
        2 hall₀
      have hallCtx := BProv_context_cons (B := Ax_s)
        (a := graphBody) hall₂
      have hallCtx' : BProv Ax_s C₂
          (all (rename (SetTheory.up Nat.succ)
            (rename (SetTheory.up Nat.succ)
              (imp codedOrdinalDomain codedBody)))) := by
        simpa [C₂, C₁, C₀, codedAll,
          iterRenameContextSucc, iterRenameSucc, rename] using hallCtx
      have hbodyInst := BProv_allE (B := Ax_s) (G := C₂)
        (t := Term.var 0) hallCtx'
      have hcodedImp : BProv Ax_s C₂
          (imp codedOrdinalDomain
            (paCompositeAt (totalCodedMap codedMap) phi)) := by
        simpa [codedBody, subst, rename,
          subst_instTerm_total_codedOrdinalDomain,
          subst_instTerm_total_codedBody] using hbodyInst
      have hdomainInst :=
        BProv_Ax_s_codedOrdinalDomain_of_ordinalCodeGraph P hgraphTerm
      have hdomain : BProv Ax_s C₂ codedOrdinalDomain := by
        simpa [subst_instTerm_var_zero_codedOrdinalDomain]
          using hdomainInst
      have hcomp : BProv Ax_s C₂
          (paCompositeAt (totalCodedMap codedMap) phi) :=
        BProv_mp Ax_s C₂ _ _ hcodedImp hdomain
      have hraw : BProv Ax_s C₂
          (rename (totalRawMap rawMap) phi) :=
        BProv_mp Ax_s C₂ _ _ hihReverse hcomp
      simpa [rawBody, rename_succ_rawBody] using hraw
    exact BProv_exE_of_sentences (B := Ax_s)
      Ax_s_sentences
      (a := graphBody) (c := rawBody) htotal' (by
        simpa [C₂] using hopened)
  have hall : BProv Ax_s C₀ rawAll := by
    simpa [rawAll, C₁] using
      (BProv_allI_of_sentences (B := Ax_s)
        Ax_s_sentences
        (G := C₀) hrawBody)
  have hmain : BProv Ax_s G (imp codedAll rawAll) := by
    simpa [C₀] using BProv_impI hall
  have hup : AckermannHF.PAInHF.upVarMap rawMap =
      SetTheory.up rawMap := by
    funext n
    cases n <;> rfl
  have hmain' : BProv Ax_s G
      (imp codedAll (all (rename (SetTheory.up rawMap) phi))) := by
    simpa [rawAll, rawBody, hup] using hmain
  simpa [codedAll, codedBody, rename,
    paCompositeAt_all_normalForm] using hmain'

/-- Full reusable universal step for paired raw/coded structural induction. -/
theorem BProv_Ax_s_paCompositeAt_all_exact
    (P : OrdinalCodeGraphProofs)
    (phi : Formula)
    (ih : ∀ (G : List Formula) (rawMap codedMap : Nat → Nat),
      (∀ n, Free n phi →
        BProv Ax_s G
          (ordinalCodeGraphAt (rawMap n) (codedMap n))) →
      BProv Ax_s G
        (iffForm (rename rawMap phi) (paCompositeAt codedMap phi)))
    (G : List Formula) (rawMap codedMap : Nat → Nat)
    (hcode : ∀ n, Free n (all phi) →
      BProv Ax_s G
        (ordinalCodeGraphAt (rawMap n) (codedMap n))) :
    BProv Ax_s G
      (iffForm (rename rawMap (all phi))
        (paCompositeAt codedMap (all phi))) := by
  exact BProv_iffForm_intro
    (BProv_Ax_s_paCompositeAt_all_forward
      P phi ih G rawMap codedMap hcode)
    (BProv_Ax_s_paCompositeAt_all_reverse
      P phi ih G rawMap codedMap hcode)

/-- Forward half of the existential structural step: totality supplies the
code paired with the freshly opened raw witness. -/
theorem BProv_Ax_s_paCompositeAt_ex_forward
    (P : OrdinalCodeGraphProofs)
    (phi : Formula)
    (ih : ∀ (G : List Formula) (rawMap codedMap : Nat → Nat),
      (∀ n, Free n phi →
        BProv Ax_s G
          (ordinalCodeGraphAt (rawMap n) (codedMap n))) →
      BProv Ax_s G
        (iffForm (rename rawMap phi) (paCompositeAt codedMap phi)))
    (G : List Formula) (rawMap codedMap : Nat → Nat)
    (hcode : ∀ n, Free n (ex phi) →
      BProv Ax_s G
        (ordinalCodeGraphAt (rawMap n) (codedMap n))) :
    BProv Ax_s G
      (imp (rename rawMap (ex phi))
        (paCompositeAt codedMap (ex phi))) := by
  let rawBody : Formula :=
    rename (AckermannHF.PAInHF.upVarMap rawMap) phi
  let codedBody : Formula :=
    paCompositeAt (hfUpVarMap codedMap) phi
  let codedAnd : Formula := and codedOrdinalDomain codedBody
  let rawEx : Formula := ex rawBody
  let codedEx : Formula := ex codedAnd
  let C₀ : List Formula := rawEx :: G
  have hcodedEx : BProv Ax_s C₀ codedEx := by
    have hrawEx : BProv Ax_s C₀ rawEx :=
      BProv_ass (B := Ax_s) (G := C₀) (by simp [C₀])
    let C₁ : List Formula := rawBody :: C₀.map (rename Nat.succ)
    have hrawOpened : BProv Ax_s C₁ (rename Nat.succ codedEx) := by
      have htotal := P.total C₁ (Term.var 0)
      let graphBody : Formula :=
        ordinalCodeGraphTermAt (Term.var 1) (Term.var 0)
      have htotal' : BProv Ax_s C₁ (ex graphBody) := by
        simpa [graphBody, Term.rename] using htotal
      let C₂ : List Formula := graphBody :: C₁.map (rename Nat.succ)
      have hcodeOpened : BProv Ax_s C₂
          (rename Nat.succ (rename Nat.succ codedEx)) := by
        have hgraphTerm : BProv Ax_s C₂
            (ordinalCodeGraphTermAt (Term.var 1) (Term.var 0)) := by
          have hass : BProv Ax_s C₂ graphBody :=
            BProv_ass (B := Ax_s) (G := C₂) (by simp [C₂])
          simpa [graphBody] using hass
        have hgraph : BProv Ax_s C₂
            (ordinalCodeGraphAt 1 0) := by
          simpa [ordinalCodeGraphAt] using hgraphTerm
        have hpaired : ∀ n, Free n phi →
            BProv Ax_s C₂
              (ordinalCodeGraphAt
                (totalRawMap rawMap n)
                (totalCodedMap codedMap n)) := by
          intro n hn
          cases n with
          | zero =>
              simpa [totalRawMap, totalCodedMap] using hgraph
          | succ n =>
              have h₀ := hcode n hn
              have h₂ := BProv_iterRenameSucc_of_sentences
                (B := Ax_s) Ax_s_sentences
                2 h₀
              have hexCtx := BProv_context_cons (B := Ax_s)
                (a := rename Nat.succ (rename Nat.succ rawEx)) h₂
              have hrawCtx := BProv_context_cons (B := Ax_s)
                (a := rename Nat.succ rawBody) hexCtx
              have hctx := BProv_context_cons (B := Ax_s)
                (a := graphBody) hrawCtx
              simpa [C₂, C₁, C₀,
                iterRenameContextSucc, iterRenameSucc,
                totalRawMap, totalCodedMap,
                ordinalCodeGraphAt, rename_ordinalCodeGraphTermAt,
                Term.rename, List.map_map, Function.comp_def] using hctx
        have hih := ih C₂
          (totalRawMap rawMap)
          (totalCodedMap codedMap) hpaired
        have hihForward : BProv Ax_s C₂
            (imp
              (rename (totalRawMap rawMap) phi)
              (paCompositeAt (totalCodedMap codedMap) phi)) := by
          simpa [iffForm] using BProv_andE1 hih
        have hraw₀ : BProv Ax_s C₁ rawBody :=
          BProv_ass (B := Ax_s) (G := C₁) (by simp [C₁])
        have hraw₁ := BProv_rename_of_sentences
          (B := Ax_s) Ax_s_sentences
          hraw₀ Nat.succ
        have hrawCtx := BProv_context_cons (B := Ax_s)
          (a := graphBody) hraw₁
        have hraw : BProv Ax_s C₂
            (rename (totalRawMap rawMap) phi) := by
          simpa [C₂, rawBody, rename_succ_rawBody] using hrawCtx
        have hcomp : BProv Ax_s C₂
            (paCompositeAt (totalCodedMap codedMap) phi) :=
          BProv_mp Ax_s C₂ _ _ hihForward hraw
        have hdomainInst :=
          BProv_Ax_s_codedOrdinalDomain_of_ordinalCodeGraph P hgraphTerm
        have hdomain : BProv Ax_s C₂ codedOrdinalDomain := by
          simpa [subst_instTerm_var_zero_codedOrdinalDomain]
            using hdomainInst
        have hand : BProv Ax_s C₂
            (and codedOrdinalDomain
              (paCompositeAt (totalCodedMap codedMap) phi)) :=
          BProv_andI hdomain hcomp
        have hinst : BProv Ax_s C₂
            (subst (instTerm (Term.var 0))
              (rename (SetTheory.up Nat.succ)
                (rename (SetTheory.up Nat.succ) codedAnd))) := by
          simpa [codedAnd, codedBody, subst, rename,
            subst_instTerm_total_codedOrdinalDomain,
            subst_instTerm_total_codedBody] using hand
        have hex : BProv Ax_s C₂
            (ex (rename (SetTheory.up Nat.succ)
              (rename (SetTheory.up Nat.succ) codedAnd))) :=
          BProv_exI hinst
        simpa [codedEx, rename] using hex
      exact BProv_exE_of_sentences (B := Ax_s)
        Ax_s_sentences
        (a := graphBody) (c := rename Nat.succ codedEx)
        htotal' (by simpa [C₂] using hcodeOpened)
    exact BProv_exE_of_sentences (B := Ax_s)
      Ax_s_sentences
      (a := rawBody) (c := codedEx)
      hrawEx (by simpa [C₁] using hrawOpened)
  have hmain : BProv Ax_s G (imp rawEx codedEx) := by
    simpa [C₀] using BProv_impI hcodedEx
  have hup : AckermannHF.PAInHF.upVarMap rawMap =
      SetTheory.up rawMap := by
    funext n
    cases n <;> rfl
  have hmain' : BProv Ax_s G
      (imp (ex (rename (SetTheory.up rawMap) phi)) codedEx) := by
    simpa [rawEx, rawBody, hup] using hmain
  simpa [codedEx, codedAnd, codedBody, rename,
    paCompositeAt_ex_normalForm] using hmain'

/-- Reverse half of the existential structural step: range opens a raw witness
for the freshly opened coded ordinal. -/
theorem BProv_Ax_s_paCompositeAt_ex_reverse
    (P : OrdinalCodeGraphProofs)
    (phi : Formula)
    (ih : ∀ (G : List Formula) (rawMap codedMap : Nat → Nat),
      (∀ n, Free n phi →
        BProv Ax_s G
          (ordinalCodeGraphAt (rawMap n) (codedMap n))) →
      BProv Ax_s G
        (iffForm (rename rawMap phi) (paCompositeAt codedMap phi)))
    (G : List Formula) (rawMap codedMap : Nat → Nat)
    (hcode : ∀ n, Free n (ex phi) →
      BProv Ax_s G
        (ordinalCodeGraphAt (rawMap n) (codedMap n))) :
    BProv Ax_s G
      (imp (paCompositeAt codedMap (ex phi))
        (rename rawMap (ex phi))) := by
  let rawBody : Formula :=
    rename (AckermannHF.PAInHF.upVarMap rawMap) phi
  let codedBody : Formula :=
    paCompositeAt (hfUpVarMap codedMap) phi
  let codedAnd : Formula := and codedOrdinalDomain codedBody
  let rawEx : Formula := ex rawBody
  let codedEx : Formula := ex codedAnd
  let C₀ : List Formula := codedEx :: G
  have hrawEx : BProv Ax_s C₀ rawEx := by
    have hcodedEx : BProv Ax_s C₀ codedEx :=
      BProv_ass (B := Ax_s) (G := C₀) (by simp [C₀])
    let C₁ : List Formula := codedAnd :: C₀.map (rename Nat.succ)
    have hcodedOpened : BProv Ax_s C₁ (rename Nat.succ rawEx) := by
      have hand : BProv Ax_s C₁ codedAnd :=
        BProv_ass (B := Ax_s) (G := C₁) (by simp [C₁])
      have hdomain : BProv Ax_s C₁ codedOrdinalDomain := by
        simpa [codedAnd] using BProv_andE1 hand
      have hdomainInst : BProv Ax_s C₁
          (subst (instTerm (Term.var 0)) codedOrdinalDomain) := by
        simpa [subst_instTerm_var_zero_codedOrdinalDomain]
          using hdomain
      have hrange :=
        BProv_Ax_s_ordinalCodeGraph_range_of_domain P hdomainInst
      let graphBody : Formula :=
        ordinalCodeGraphTermAt (Term.var 0) (Term.var 1)
      have hrange' : BProv Ax_s C₁ (ex graphBody) := by
        simpa [graphBody, Term.rename] using hrange
      let C₂ : List Formula := graphBody :: C₁.map (rename Nat.succ)
      have hrawOpened : BProv Ax_s C₂
          (rename Nat.succ (rename Nat.succ rawEx)) := by
        have hgraph : BProv Ax_s C₂
            (ordinalCodeGraphAt 0 1) := by
          have hass : BProv Ax_s C₂ graphBody :=
            BProv_ass (B := Ax_s) (G := C₂) (by simp [C₂])
          simpa [graphBody, ordinalCodeGraphAt] using hass
        have hpaired : ∀ n, Free n phi →
            BProv Ax_s C₂
              (ordinalCodeGraphAt
                (rangeRawMap rawMap n)
                (rangeCodedMap codedMap n)) := by
          intro n hn
          cases n with
          | zero =>
              simpa [rangeRawMap, rangeCodedMap] using hgraph
          | succ n =>
              have h₀ := hcode n hn
              have h₂ := BProv_iterRenameSucc_of_sentences
                (B := Ax_s) Ax_s_sentences
                2 h₀
              have hexCtx := BProv_context_cons (B := Ax_s)
                (a := rename Nat.succ (rename Nat.succ codedEx)) h₂
              have handCtx := BProv_context_cons (B := Ax_s)
                (a := rename Nat.succ codedAnd) hexCtx
              have hctx := BProv_context_cons (B := Ax_s)
                (a := graphBody) handCtx
              simpa [C₂, C₁, C₀,
                iterRenameContextSucc, iterRenameSucc,
                rangeRawMap, rangeCodedMap,
                ordinalCodeGraphAt, rename_ordinalCodeGraphTermAt,
                Term.rename, List.map_map, Function.comp_def] using hctx
        have hih := ih C₂
          (rangeRawMap rawMap)
          (rangeCodedMap codedMap) hpaired
        have hihReverse : BProv Ax_s C₂
            (imp
              (paCompositeAt (rangeCodedMap codedMap) phi)
              (rename (rangeRawMap rawMap) phi)) := by
          simpa [iffForm] using BProv_andE2 hih
        have hcoded : BProv Ax_s C₁ codedBody := by
          simpa [codedAnd] using BProv_andE2 hand
        have hcodedRen := BProv_rename_of_sentences
          (B := Ax_s) Ax_s_sentences
          hcoded Nat.succ
        have hcodedCtx := BProv_context_cons (B := Ax_s)
          (a := graphBody) hcodedRen
        have hcomp : BProv Ax_s C₂
            (paCompositeAt (rangeCodedMap codedMap) phi) := by
          simpa [C₂, codedBody,
            rename_succ_paCompositeAt_up] using hcodedCtx
        have hraw : BProv Ax_s C₂
            (rename (rangeRawMap rawMap) phi) :=
          BProv_mp Ax_s C₂ _ _ hihReverse hcomp
        have hinst : BProv Ax_s C₂
            (subst (instTerm (Term.var 0))
              (rename (SetTheory.up Nat.succ)
                (rename (SetTheory.up Nat.succ) rawBody))) := by
          simpa [rawBody, subst_instTerm_range_rawBody] using hraw
        have hex : BProv Ax_s C₂
            (ex (rename (SetTheory.up Nat.succ)
              (rename (SetTheory.up Nat.succ) rawBody))) :=
          BProv_exI hinst
        simpa [rawEx, rename] using hex
      exact BProv_exE_of_sentences (B := Ax_s)
        Ax_s_sentences
        (a := graphBody) (c := rename Nat.succ rawEx)
        hrange' (by simpa [C₂] using hrawOpened)
    exact BProv_exE_of_sentences (B := Ax_s)
      Ax_s_sentences
      (a := codedAnd) (c := rawEx)
      hcodedEx (by simpa [C₁] using hcodedOpened)
  have hmain : BProv Ax_s G (imp codedEx rawEx) := by
    simpa [C₀] using BProv_impI hrawEx
  have hup : AckermannHF.PAInHF.upVarMap rawMap =
      SetTheory.up rawMap := by
    funext n
    cases n <;> rfl
  have hmain' : BProv Ax_s G
      (imp codedEx (ex (rename (SetTheory.up rawMap) phi))) := by
    simpa [rawEx, rawBody, hup] using hmain
  simpa [codedEx, codedAnd, codedBody, rename,
    paCompositeAt_ex_normalForm] using hmain'

/-- Full reusable existential step for paired raw/coded structural induction. -/
theorem BProv_Ax_s_paCompositeAt_ex_exact
    (P : OrdinalCodeGraphProofs)
    (phi : Formula)
    (ih : ∀ (G : List Formula) (rawMap codedMap : Nat → Nat),
      (∀ n, Free n phi →
        BProv Ax_s G
          (ordinalCodeGraphAt (rawMap n) (codedMap n))) →
      BProv Ax_s G
        (iffForm (rename rawMap phi) (paCompositeAt codedMap phi)))
    (G : List Formula) (rawMap codedMap : Nat → Nat)
    (hcode : ∀ n, Free n (ex phi) →
      BProv Ax_s G
        (ordinalCodeGraphAt (rawMap n) (codedMap n))) :
    BProv Ax_s G
      (iffForm (rename rawMap (ex phi))
        (paCompositeAt codedMap (ex phi))) := by
  exact BProv_iffForm_intro
    (BProv_Ax_s_paCompositeAt_ex_forward
      P phi ih G rawMap codedMap hcode)
    (BProv_Ax_s_paCompositeAt_ex_reverse
      P phi ih G rawMap codedMap hcode)

/-- Full paired-variable structural induction for every PA formula. -/
theorem BProv_Ax_s_paCompositeAt_formula_exact
    (P : OrdinalCodeGraphProofs) :
    ∀ (phi : Formula) (G : List Formula)
        (rawMap codedMap : Nat → Nat),
      (∀ n, Free n phi →
        BProv Ax_s G
          (ordinalCodeGraphAt (rawMap n) (codedMap n))) →
      BProv Ax_s G
        (iffForm (rename rawMap phi) (paCompositeAt codedMap phi)) := by
  intro phi
  induction phi with
  | eq left right =>
      intro G rawMap codedMap hcode
      exact BProv_Ax_s_paCompositeAt_eq_exact
        P G left right rawMap codedMap hcode
  | bot =>
      intro G rawMap codedMap hcode
      simpa [rename, paCompositeAt,
        AckermannHF.PAInHF.formulaAt, hfFormulaAt] using
        (BProv_iffForm_refl (B := Ax_s) (G := G) bot)
  | imp a b iha ihb =>
      intro G rawMap codedMap hcode
      have ha := iha G rawMap codedMap
        (fun n hn ↦ hcode n (Or.inl hn))
      have hb := ihb G rawMap codedMap
        (fun n hn ↦ hcode n (Or.inr hn))
      simpa [rename, paCompositeAt,
        AckermannHF.PAInHF.formulaAt, hfFormulaAt] using
        BProv_iffForm_imp_congr ha hb
  | and a b iha ihb =>
      intro G rawMap codedMap hcode
      have ha := iha G rawMap codedMap
        (fun n hn ↦ hcode n (Or.inl hn))
      have hb := ihb G rawMap codedMap
        (fun n hn ↦ hcode n (Or.inr hn))
      simpa [rename, paCompositeAt,
        AckermannHF.PAInHF.formulaAt, hfFormulaAt] using
        BProv_iffForm_and_congr ha hb
  | or a b iha ihb =>
      intro G rawMap codedMap hcode
      have ha := iha G rawMap codedMap
        (fun n hn ↦ hcode n (Or.inl hn))
      have hb := ihb G rawMap codedMap
        (fun n hn ↦ hcode n (Or.inr hn))
      simpa [rename, paCompositeAt,
        AckermannHF.PAInHF.formulaAt, hfFormulaAt] using
        BProv_iffForm_or_congr ha hb
  | all a ih =>
      intro G rawMap codedMap hcode
      exact BProv_Ax_s_paCompositeAt_all_exact
        P a ih G rawMap codedMap hcode
  | ex a ih =>
      intro G rawMap codedMap hcode
      exact BProv_Ax_s_paCompositeAt_ex_exact
        P a ih G rawMap codedMap hcode

/-- The ordinal-Code graph proof package canonically supplies the full
paired-variable structural induction. -/
theorem PACompositeStructuralProofs_of_graphProofs
    (P : OrdinalCodeGraphProofs) : PACompositeStructuralProofs where
  toOrdinalCodeGraphProofs := P
  formula_exact := fun G phi rawMap codedMap hcode ↦
    BProv_Ax_s_paCompositeAt_formula_exact
      P phi G rawMap codedMap hcode

/-- A graph proof package alone closes the PA composite identity on every
sentence. -/
theorem BProv_Ax_s_pa_roundTrip_of_graphProofs
    (P : OrdinalCodeGraphProofs)
    (phi : Formula) (hphi : Sentence phi) :
    BProv Ax_s []
      (iffForm phi
        (translateHFFormula
          (AckermannHF.PAInHF.translateFormula phi))) :=
  BProv_Ax_s_pa_roundTrip_of_structuralProofs
    (PACompositeStructuralProofs_of_graphProofs P) phi hphi

/-- The fragment of PA formulas whose syntax contains no quantifier. -/
def QuantifierFree : Formula → Prop
  | eq _ _ => True
  | bot => True
  | imp a b => QuantifierFree a ∧ QuantifierFree b
  | and a b => QuantifierFree a ∧ QuantifierFree b
  | or a b => QuantifierFree a ∧ QuantifierFree b
  | all _ => False
  | ex _ => False

/-- Once equality atoms are related through the ordinal-code graph, the
entire quantifier-free fragment follows by structural proof composition. -/
theorem BProv_Ax_s_paCompositeAt_iff_of_quantifierFree
    (equality_exact :
      ∀ (G : List Formula) (left right : Term)
          (rawMap codedMap : Nat → Nat),
        (∀ n, Free n (eq left right) →
          BProv Ax_s G
            (ordinalCodeGraphAt (rawMap n) (codedMap n))) →
        BProv Ax_s G
          (iffForm
            (rename rawMap (eq left right))
            (paCompositeAt codedMap (eq left right)))) :
    ∀ (phi : Formula), QuantifierFree phi →
      ∀ (G : List Formula) (rawMap codedMap : Nat → Nat),
        (∀ n, Free n phi →
          BProv Ax_s G
            (ordinalCodeGraphAt (rawMap n) (codedMap n))) →
        BProv Ax_s G
          (iffForm (rename rawMap phi) (paCompositeAt codedMap phi)) := by
  intro phi hqf
  induction phi with
  | eq left right =>
      intro G rawMap codedMap hcode
      exact equality_exact G left right rawMap codedMap hcode
  | bot =>
      intro G rawMap codedMap hcode
      simpa [rename, paCompositeAt,
        AckermannHF.PAInHF.formulaAt, hfFormulaAt] using
        (BProv_iffForm_refl (B := Ax_s) (G := G) bot)
  | imp a b iha ihb =>
      intro G rawMap codedMap hcode
      have hqa : QuantifierFree a := hqf.1
      have hqb : QuantifierFree b := hqf.2
      have ha := iha hqa G rawMap codedMap
        (fun n hn ↦ hcode n (Or.inl hn))
      have hb := ihb hqb G rawMap codedMap
        (fun n hn ↦ hcode n (Or.inr hn))
      simpa [rename, paCompositeAt,
        AckermannHF.PAInHF.formulaAt, hfFormulaAt] using
        BProv_iffForm_imp_congr ha hb
  | and a b iha ihb =>
      intro G rawMap codedMap hcode
      have hqa : QuantifierFree a := hqf.1
      have hqb : QuantifierFree b := hqf.2
      have ha := iha hqa G rawMap codedMap
        (fun n hn ↦ hcode n (Or.inl hn))
      have hb := ihb hqb G rawMap codedMap
        (fun n hn ↦ hcode n (Or.inr hn))
      simpa [rename, paCompositeAt,
        AckermannHF.PAInHF.formulaAt, hfFormulaAt] using
        BProv_iffForm_and_congr ha hb
  | or a b iha ihb =>
      intro G rawMap codedMap hcode
      have hqa : QuantifierFree a := hqf.1
      have hqb : QuantifierFree b := hqf.2
      have ha := iha hqa G rawMap codedMap
        (fun n hn ↦ hcode n (Or.inl hn))
      have hb := ihb hqb G rawMap codedMap
        (fun n hn ↦ hcode n (Or.inr hn))
      simpa [rename, paCompositeAt,
        AckermannHF.PAInHF.formulaAt, hfFormulaAt] using
        BProv_iffForm_or_congr ha hb
  | all a ih =>
      exact False.elim hqf
  | ex a ih =>
      exact False.elim hqf


end Formula
end PA

namespace AckermannHF

/-- Conditional deductive-bi-interpretability shell with the PA round trip
factored through the internal ordinal-Code graph package. -/
def PAHFFinDeductiveBiInterpretationCertificate_of_codeStructuralProofs
    (P : PA.Formula.PACompositeStructuralProofs)
    (hhf_roundTrip :
      ∀ (phi : Form), Sentence phi →
        BProv HFFinAx_s []
          (fIff phi
            (PAInHF.translateFormula
              (PA.Formula.translateHFFormula phi)))) :
    PAHFFinDeductiveBiInterpretationCertificate :=
  PAHFFinDeductiveBiInterpretationCertificate_of_remaining
    (fun phi hphi ↦
      PA.Formula.BProv_Ax_s_pa_roundTrip_of_structuralProofs
        P phi hphi)
    hhf_roundTrip

end AckermannHF
end SetTheory
