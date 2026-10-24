import DiophantineConsistency.ObjectPairingSyntax

/-! # An actual set-theory formula for the sharp max-square pairing graph

The three auxiliary coordinates range over the entire internal omega.
The totality/functionality statements below are proofs in the existing
sealed ZFC calculus. No arbitrary external graph theorem is transferred.
-/
noncomputable section
namespace DiophantineConsistency.ObjectPairingGraph
set_option maxRecDepth 16000
attribute [local irreducible] ObjectPairingSyntax.expression
open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency ObjectOmegaSemiring
universe u
variable {V : Type u} {mem : V → V → Prop}
variable (H : ZFAxioms mem)
abbrev N := Natural H

private def coordinates (z a b : ℕ) : Fin 6 → ℕ := ![a+3,z+3,b+3,2,1,0]

private def auxiliaryForm (z a b : ℕ) : Form :=
  fEx (fEx (fEx (fAnd (fNatF 2) (fAnd (fNatF 1) (fAnd (fNatF 0)
    (ObjectPolynomial.equationForm ObjectPairingSyntax.expression (coordinates z a b)))))))

private theorem auxiliaryForm_spec (ee : ℕ → V) (z a b : ℕ)
    (hz : mem (ee z) (omegaV H)) (ha : mem (ee a) (omegaV H))
    (hb : mem (ee b) (omegaV H)) :
    Sat mem ee (auxiliaryForm z a b) ↔
      (⟨ee z,hz⟩ : N H)=ObjectNatPairing.pair H ⟨ee a,ha⟩ ⟨ee b,hb⟩ := by
  change (∃ t s m, Sat mem (scons m (scons s (scons t ee))) (fNatF 2) ∧
    Sat mem (scons m (scons s (scons t ee))) (fNatF 1) ∧
    Sat mem (scons m (scons s (scons t ee))) (fNatF 0) ∧
    Sat mem (scons m (scons s (scons t ee)))
      (ObjectPolynomial.equationForm ObjectPairingSyntax.expression (coordinates z a b))) ↔ _
  constructor
  · rintro ⟨t,s,m,ht,hs,hm,he⟩
    let tt : N H := ⟨t,(fNatF_spec H _ 2).mp ht⟩
    let ss : N H := ⟨s,(fNatF_spec H _ 1).mp hs⟩
    let mm : N H := ⟨m,(fNatF_spec H _ 0).mp hm⟩
    apply (ObjectPairingSyntax.exists_equationRel_iff H ⟨ee z,hz⟩ ⟨ee a,ha⟩ ⟨ee b,hb⟩).mp
    refine ⟨tt,ss,mm,?_⟩
    have he' := (ObjectPolynomial.equationForm_spec H ObjectPairingSyntax.expression
      (coordinates z a b) (scons m (scons s (scons t ee)))).mp he
    convert he' using 1
    funext i
    fin_cases i <;> rfl
  · intro h
    obtain ⟨t,s,m,he⟩ := (ObjectPairingSyntax.exists_equationRel_iff H
      ⟨ee z,hz⟩ ⟨ee a,ha⟩ ⟨ee b,hb⟩).mpr h
    refine ⟨t.val,s.val,m.val,(fNatF_spec H _ 2).mpr t.property,
      (fNatF_spec H _ 1).mpr s.property,(fNatF_spec H _ 0).mpr m.property,?_⟩
    apply (ObjectPolynomial.equationForm_spec H ObjectPairingSyntax.expression
      (coordinates z a b) _).mpr
    convert he using 1
    funext i
    fin_cases i <;> rfl

/-- The actual graph formula guards all three visible inputs as naturals. -/
def graphForm (z a b : ℕ) : Form :=
  fAnd (fNatF z) (fAnd (fNatF a) (fAnd (fNatF b) (auxiliaryForm z a b)))

theorem graphForm_naturals (ee : ℕ → V) (z a b : ℕ)
    (h : Sat mem ee (graphForm z a b)) :
    mem (ee z) (omegaV H) ∧ mem (ee a) (omegaV H) ∧ mem (ee b) (omegaV H) :=
  ⟨(fNatF_spec H ee z).mp h.1,(fNatF_spec H ee a).mp h.2.1,
    (fNatF_spec H ee b).mp h.2.2.1⟩

theorem graphForm_spec (ee : ℕ → V) (z a b : ℕ)
    (hz : mem (ee z) (omegaV H)) (ha : mem (ee a) (omegaV H))
    (hb : mem (ee b) (omegaV H)) :
    Sat mem ee (graphForm z a b) ↔
      (⟨ee z,hz⟩ : N H)=ObjectNatPairing.pair H ⟨ee a,ha⟩ ⟨ee b,hb⟩ := by
  constructor
  · intro h
    exact (auxiliaryForm_spec H ee z a b hz ha hb).mp h.2.2.2
  · intro h
    exact ⟨(fNatF_spec H ee z).mpr hz,(fNatF_spec H ee a).mpr ha,
      (fNatF_spec H ee b).mpr hb,(auxiliaryForm_spec H ee z a b hz ha hb).mpr h⟩

/-- Total pairing on all internal naturals. -/
def totalForm : Form := sealF
  (fImp (fAnd (fNatF 1) (fNatF 0)) (fEx (graphForm 0 2 1)))

/-- Functionality includes the graph's own guards, with no extra output premise. -/
def uniqueForm : Form := sealF
  (fImp (fAnd (graphForm 1 3 2) (graphForm 0 3 2)) (fEq 1 0))

theorem sentence_totalForm : Sentence totalForm := Sentence_seal _
theorem sentence_uniqueForm : Sentence uniqueForm := Sentence_seal _

theorem zfc_proves_total : BProv ZFCax_s [] totalForm := by
  refine completeness_inf_context ZFCax_s [] totalForm Sentences_ZFC ?_
  intro Dom relation env hmodel _
  let HH := ObjectMultiplication.axioms_of_zfc_model env hmodel
  apply (seal_valid (mem := relation) _).mpr ?_ env
  intro ee h
  have ha := (fNatF_spec HH ee 1).mp h.1
  have hb := (fNatF_spec HH ee 0).mp h.2
  let z := ObjectNatPairing.pair HH ⟨ee 1,ha⟩ ⟨ee 0,hb⟩
  refine ⟨z.val,(graphForm_spec HH (scons z.val ee) 0 2 1 z.property ha hb).mpr ?_⟩
  rfl

theorem zfc_proves_unique : BProv ZFCax_s [] uniqueForm := by
  refine completeness_inf_context ZFCax_s [] uniqueForm Sentences_ZFC ?_
  intro Dom relation env hmodel _
  let HH := ObjectMultiplication.axioms_of_zfc_model env hmodel
  apply (seal_valid (mem := relation) _).mpr ?_ env
  intro ee h
  obtain ⟨hz,ha,hb⟩ := graphForm_naturals HH ee 1 3 2 h.1
  obtain ⟨hz',_,_⟩ := graphForm_naturals HH ee 0 3 2 h.2
  have h1 := (graphForm_spec HH ee 1 3 2 hz ha hb).mp h.1
  have h2 := (graphForm_spec HH ee 0 3 2 hz' ha hb).mp h.2
  exact congrArg Subtype.val (h1.trans h2.symm)

end DiophantineConsistency.ObjectPairingGraph
