import DiophantineConsistency.PRAExponentialWitnessBound
/-! Bound negative Foundation extDef at any witness limit; the negative
    exponential and bit bounds remain open. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRANegExtWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
theorem neg_ext_bound (a b c w : V) : (∼extDef.val).Evalb ![a,b,c] →
    (bnd (∼extDef.val)).Evalb ![a,b,c,w] := by
  intro h
  simp [extDef, divDef, remDef, subDef, Semiformula.bexsLTSucc, Semiformula.bexsLT,
    FirstOrder.bexs, DeMorgan.imply, bnd, bnd_open, Rew.subst, Rew.q] at h ⊢
  exact h
def negExt : ArithmeticSemisentence 3 := ∼extDef.val

def boundedNegExt : ArithmeticSemisentence 4 := bnd negExt

def negExtBoundBody : ArithmeticSemisentence 4 :=
  “a b c w. !negExt a b c → !boundedNegExt a b c w”

theorem negExtBoundBody_model (e : Fin 4 → V) : negExtBoundBody.Eval e Empty.elim := by
  simp [negExtBoundBody, boundedNegExt, Semiformula.eval_substs]
  exact neg_ext_bound (e 0) (e 1) (e 2) (e 3)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

def negExtBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding negExtBoundBody

theorem candidate_proves_negExt_bound : PRA ⊢ negExtBoundSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [models_iff, negExtBoundSentence, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_lMap, reduct_eq_standard]
  exact negExtBoundBody_model e
end DiophantineConsistency.PRANegExtWitnessBound
